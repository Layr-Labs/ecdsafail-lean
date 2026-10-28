import ECDSAAdd.Arithmetic.Divsteps.ForwardStep
import Mathlib.Data.List.Perm.Basic

namespace ECDSAAdd.Arithmetic.Divsteps

/-- A signed little-endian row with explicit low and sign wires. -/
structure StepRow where
  low : Wire
  middle : List Wire
  sign : Wire
  deriving DecidableEq

def StepRow.wires (r : StepRow) : List Wire := r.low::(r.middle++[r.sign])

/-- Reinterpret the same wires after the physical integer half-row. -/
def StepRow.halfView (r : StepRow) : StepRow :=
  match r.middle with
  | [] => ⟨r.sign,[],r.low⟩
  | a::as => ⟨a,as++[r.sign],r.low⟩

theorem StepRow.halfView_wires (r : StepRow) :
    r.halfView.wires=skywalkHalfView r.low (r.middle++[r.sign]) := by
  cases r with | mk low mid sign => cases mid <;> simp [halfView,wires,skywalkHalfView,List.append_assoc]

theorem StepRow.halfView_perm (r : StepRow) : r.halfView.wires.Perm r.wires := by
  rw [halfView_wires]
  exact List.perm_append_comm.trans (by rfl)

theorem StepRow.halfView_length (r : StepRow) : r.halfView.wires.length=r.wires.length :=
  r.halfView_perm.length_eq

theorem StepRow.halfView_support (r : StepRow) : r.halfView.wires.toFinset=r.wires.toFinset :=
  by ext w; simpa only [List.mem_toFinset] using r.halfView_perm.mem_iff

/-- Retained history for one step. These bits are not reusable clean workspace. -/
structure StepHistory where
  active : Wire
  parity : Wire
  swap : Wire
  deriving DecidableEq

def StepHistory.wires (h : StepHistory) : List Wire := [h.active,h.parity,h.swap]

/-- Widths are supplied by the caller. One shared mask and one shared carry
pool serve integer, coefficient, and counter arithmetic through prefixes.
Detection scratch is indexed by the physical g wire, so changing the row view
also reorders its detection pairs without reallocating any wire. -/
structure StepLayout where
  f : List Wire
  g : StepRow
  fv : StepRow
  gv : List Wire
  z : StepRow
  mask : List Wire
  carry : List Wire
  detect : Wire → Wire
  one : Wire
  cin : Wire
  history : StepHistory
  past : List StepHistory
  future : List StepHistory

def StepLayout.data (L : StepLayout) : List Wire :=
  L.f++L.g.wires++L.fv.wires++L.gv++L.z.wires

def StepLayout.work (L : StepLayout) : List Wire :=
  L.mask++L.carry++L.g.wires.map L.detect++[L.one,L.cin]

def StepLayout.histories (L : StepLayout) : List Wire :=
  L.history.wires++L.past.flatMap StepHistory.wires++L.future.flatMap StepHistory.wires

def StepLayout.used (L : StepLayout) : List Wire := L.data++L.work++L.histories

def StepLayout.gmask (L : StepLayout) := L.mask.take L.g.wires.length
def StepLayout.vmask (L : StepLayout) := L.mask.take L.gv.length
def StepLayout.cz (L : StepLayout) := L.mask.take L.z.wires.length
def StepLayout.gcarry (L : StepLayout) := L.carry.take (L.g.wires.length-1)
def StepLayout.vcarry (L : StepLayout) := L.carry.take (L.gv.length-1)
def StepLayout.cc (L : StepLayout) := L.carry.take (L.z.wires.length-1)
def StepLayout.bits (L : StepLayout) : List ZeroBit :=
  L.g.wires.map (fun w => ⟨w,L.detect w⟩)

/-- The duplicate-free allocation counts each reusable physical wire once.
No numerical pool capacity or termination bound is assumed. -/
structure StepLayout.Valid (L : StepLayout) : Prop where
  unique : L.used.Nodup
  integers : L.f.length=L.g.wires.length
  coefficients : L.fv.wires.length=L.gv.length
  mask_g : L.g.wires.length≤L.mask.length
  mask_v : L.gv.length≤L.mask.length
  mask_z : L.z.wires.length≤L.mask.length
  carry_g : L.g.wires.length-1≤L.carry.length
  carry_v : L.gv.length-1≤L.carry.length
  carry_z : L.z.wires.length-1≤L.carry.length

/-- Clean reusable workspace; history has a separate freshness obligation. -/
def StepLayout.Clean (L : StepLayout) (s : BasisState) : Prop :=
  ∀ w∈L.work,s w=false

def StepLayout.Fresh (L : StepLayout) (s : BasisState) : Prop :=
  ∀ w∈L.history.wires,s w=false

def StepLayout.halfView (L : StepLayout) : StepLayout := { L with g := L.g.halfView }

theorem StepLayout.halfView_used_perm (L : StepLayout) : L.halfView.used.Perm L.used := by
  have h := L.g.halfView_perm
  unfold used data work histories halfView
  dsimp only
  exact ((((((List.Perm.refl _).append h).append_right _).append_right _).append_right _).append
    (((List.Perm.refl _).append (h.map L.detect)).append_right _)).append_right _

theorem StepLayout.halfView_valid (L : StepLayout) (h : L.Valid) : L.halfView.Valid := by
  have hl := L.g.halfView_length
  constructor
  · exact L.halfView_used_perm.nodup_iff.mpr h.unique
  · simpa only [halfView,hl] using h.integers
  · exact h.coefficients
  · simpa only [halfView,hl] using h.mask_g
  · exact h.mask_v
  · exact h.mask_z
  · simpa only [halfView,hl] using h.carry_g
  · exact h.carry_v
  · exact h.carry_z

theorem StepLayout.halfView_support (L : StepLayout) : L.halfView.used.toFinset=L.used.toFinset :=
  by ext w; simpa only [List.mem_toFinset] using L.halfView_used_perm.mem_iff

theorem StepLayout.halfView_clean (L : StepLayout) (s : BasisState) :
    L.halfView.Clean s ↔ L.Clean s := by
  have h := ((List.Perm.refl (L.mask++L.carry)).append
    (L.g.halfView_perm.map L.detect)).append_right [L.one,L.cin]
  unfold Clean work halfView
  dsimp only
  exact forall_congr' (fun w => by rw [h.mem_iff])

/-- Integer/coefficient/counter views are prefixes of the same clean rows. -/
theorem StepLayout.prefix_lengths (L : StepLayout) (h : L.Valid) :
    L.gmask.length=L.g.wires.length ∧ L.vmask.length=L.gv.length ∧
    L.cz.length=L.z.wires.length ∧ L.gcarry.length+1=L.g.wires.length ∧
    L.vcarry.length+1=L.gv.length ∧ L.cc.length+1=L.z.wires.length := by
  have hg : 2≤L.g.wires.length := by simp [StepRow.wires]
  have hz : 2≤L.z.wires.length := by simp [StepRow.wires]
  have hv : 2≤L.gv.length := by rw [←h.coefficients]; simp [StepRow.wires]
  simp only [gmask,vmask,cz,gcarry,vcarry,cc,List.length_take,
    Nat.min_eq_left h.mask_g,Nat.min_eq_left h.mask_v,Nat.min_eq_left h.mask_z,
    Nat.min_eq_left h.carry_g,Nat.min_eq_left h.carry_v,Nat.min_eq_left h.carry_z]
  simp only [true_and]
  exact ⟨by omega,by omega,by omega⟩

theorem StepLayout.bits_inputs (L : StepLayout) : L.bits.map ZeroBit.input=L.g.wires := by
  simp [bits,List.map_map,Function.comp_def]

/-- The actual ForwardStep, with all scratch views and controls supplied. -/
def StepLayout.program (L : StepLayout) : Program :=
  forwardStep L.history.swap L.history.parity L.cin L.history.active
    L.g.low L.g.sign L.fv.low L.fv.sign L.one L.z.sign
    L.f L.g.middle L.gmask L.gcarry L.fv.middle L.vmask L.gv L.vcarry
    L.cz L.z.wires L.cc L.bits

/-- Global uniqueness immediately separates data, reusable work and all history. -/
theorem StepLayout.separation (L : StepLayout) (h : L.Valid) :
    L.data.Nodup ∧ L.work.Nodup ∧ L.histories.Nodup ∧
    List.Disjoint L.data L.work ∧ List.Disjoint L.data L.histories ∧
    List.Disjoint L.work L.histories := by
  have hh := h.unique
  simp only [used,List.nodup_append',List.disjoint_append_left] at hh
  tauto

private theorem StepLayout.select_nodup (L : StepLayout) (h : L.Valid) (xs : List Wire)
    (hc : ∀ w,List.count w xs≤List.count w L.used) : xs.Nodup := by
  apply List.nodup_iff_count.mpr
  intro w
  exact (hc w).trans (List.nodup_iff_count.mp h.unique w)

/-- Each arithmetic call gets a duplicate-free view although all three calls
reuse prefixes of the same physical mask and carry pools. -/
theorem StepLayout.arithmetic_nodup (L : StepLayout) (h : L.Valid) :
    (L.history.swap::L.history.parity::L.cin::(L.f++L.gmask++L.g.wires++L.gcarry)).Nodup ∧
    (L.history.swap::L.history.parity::L.cin::(L.fv.wires++L.vmask++L.gv++L.vcarry)).Nodup ∧
    (L.history.active::L.history.swap::(L.cz++L.z.wires++L.cc)).Nodup := by
  have hm (k w : Nat) := (List.take_sublist k L.mask).count_le w
  have hc (k w : Nat) := (List.take_sublist k L.carry).count_le w
  refine ⟨?_,?_,?_⟩
  all_goals
    apply L.select_nodup h
    intro w
    have hm1 := hm L.g.wires.length w
    have hm2 := hm L.gv.length w
    have hm3 := hm L.z.wires.length w
    have hc1 := hc (L.g.wires.length-1) w
    have hc2 := hc (L.gv.length-1) w
    have hc3 := hc (L.z.wires.length-1) w
    simp only [used,data,work,histories,gmask,vmask,cz,gcarry,vcarry,cc,
      StepHistory.wires,List.count_append,List.count_cons,List.count_nil]
    omega

private theorem paired_count (xs : List Wire) (f : Wire → Wire) (w : Wire) :
    List.count w ((xs.map (fun a => (⟨a,f a⟩ : ZeroBit))).flatMap ZeroBit.wires)=
      List.count w xs+List.count w (xs.map f) := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ZeroBit.wires,List.count_cons,ih]; omega

/-- Full-word detection has no aliases between inputs, work or controls. -/
theorem StepLayout.activity_nodup (L : StepLayout) (h : L.Valid) :
    (L.one::L.history.active::L.bits.flatMap ZeroBit.wires).Nodup := by
  apply L.select_nodup h
  intro w
  simp only [used,data,work,histories,StepHistory.wires,List.count_append,List.count_cons,
    List.count_nil,bits,paired_count]
  omega

/-- Every shared prefix inherits cleanliness from the physical workspace. -/
theorem StepLayout.clean_prefixes (L : StepLayout) (s : BasisState) (h : L.Clean s) :
    regValue L.gmask s=0 ∧ regValue L.vmask s=0 ∧ regValue L.cz s=0 ∧
    regValue L.gcarry s=0 ∧ regValue L.vcarry s=0 ∧ regValue L.cc s=0 := by
  have hm : ∀ k,regValue (L.mask.take k) s=0 := by
    intro k
    rw [regValue_zero]
    intro w hw
    exact h w (by simp only [work,List.mem_append]; exact Or.inl (Or.inl (Or.inl (List.mem_of_mem_take hw))))
  have hc : ∀ k,regValue (L.carry.take k) s=0 := by
    intro k
    rw [regValue_zero]
    intro w hw
    exact h w (by simp only [work,List.mem_append]; exact Or.inl (Or.inl (Or.inr (List.mem_of_mem_take hw))))
  exact ⟨hm _,hm _,hm _,hc _,hc _,hc _⟩

attribute [local irreducible] wires forwardStep

theorem StepLayout.program_current_support (L : StepLayout) (h : L.Valid) :
    wires L.program⊆(L.data++L.work++L.history.wires).toFinset := by
  obtain ⟨hgm,hvm,hcz,hgc,hvc,hcc⟩ := L.prefix_lengths h
  have hs := forwardStep_wires_subset L.history.swap L.history.parity L.cin L.history.active
    L.g.low L.g.sign L.fv.low L.fv.sign L.one L.z.sign
    L.f L.g.middle L.gmask L.gcarry L.fv.middle L.vmask L.gv L.vcarry
    L.cz L.z.wires L.cc L.bits h.integers h.coefficients
    (h.integers.trans hgm.symm) (by simpa [StepRow.wires] using hgm)
    (by simpa [StepRow.wires] using hgc) (h.coefficients.trans hvm.symm) hvm hvc hcz hcc
  apply hs.trans
  intro w hw
  have hm (k : Nat) : w∈L.mask.take k → w∈L.mask := List.mem_of_mem_take
  have hc (k : Nat) : w∈L.carry.take k → w∈L.carry := List.mem_of_mem_take
  have hb : w∈L.bits.flatMap ZeroBit.wires → w∈L.g.wires ∨ w∈L.g.wires.map L.detect := by
    intro hw
    simp only [bits,List.mem_flatMap,List.mem_map,ZeroBit.wires,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with ⟨b,⟨a,ha,rfl⟩,hh⟩
    rcases hh with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr (List.mem_map.mpr ⟨a,ha,rfl⟩)
  simp only [forwardStepSupport,List.mem_toFinset,List.mem_cons,List.mem_append] at hw
  have hg : w∈L.g.wires ↔ w=L.g.low ∨ w∈L.g.middle ∨ w=L.g.sign := by simp [StepRow.wires]
  have hv : w∈L.fv.wires ↔ w=L.fv.low ∨ w∈L.fv.middle ∨ w=L.fv.sign := by simp [StepRow.wires]
  have hz : w∈L.z.wires ↔ w=L.z.low ∨ w∈L.z.middle ∨ w=L.z.sign := by simp [StepRow.wires]
  have hm1 := hm L.g.wires.length
  have hm2 := hm L.gv.length
  have hm3 := hm L.z.wires.length
  have hc1 := hc (L.g.wires.length-1)
  have hc2 := hc (L.gv.length-1)
  have hc3 := hc (L.z.wires.length-1)
  simp only [gmask,vmask,cz,gcarry,vcarry,cc] at hw
  simp only [List.mem_toFinset,data,work,StepHistory.wires,
    List.mem_append,List.mem_cons,List.not_mem_nil,or_false,hg,hv,hz]
  simp only [hg] at hb
  simp only [hz] at hw
  clear hs h hgm hvm hcz hgc hvc hcc hm hc hg hv hz
  simp only [or_assoc] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  all_goals
    first
    | have hh := hb hw
      rcases hh with (hh|hh|hh)|hh <;> simp_all only [or_true,true_or]
    | simp_all only [or_true,true_or]

theorem StepLayout.program_support (L : StepLayout) (h : L.Valid) :
    wires L.program⊆L.used.toFinset := by
  apply (L.program_current_support h).trans
  intro w hw
  simp only [List.mem_toFinset,List.mem_append] at hw
  simp only [List.mem_toFinset,used,histories,List.mem_append]
  tauto

theorem StepLayout.program_qubits (L : StepLayout) (h : L.Valid) :
    qubitCount L.program≤L.used.length := by
  have hh := Finset.card_le_card (L.program_support h)
  rwa [List.toFinset_card_of_nodup h.unique] at hh

/-- Number of allocated physical wires; shared prefixes are counted only once. -/
theorem StepLayout.used_length (L : StepLayout) (h : L.Valid) :
    L.used.length=3*L.g.wires.length+2*L.gv.length+L.z.wires.length+
      L.mask.length+L.carry.length+5+3*(L.past.length+L.future.length) := by
  have hh (hs : List StepHistory) : (hs.flatMap StepHistory.wires).length=3*hs.length := by
    induction hs with
    | nil => simp
    | cons a hs ih => simp [StepHistory.wires,ih]; omega
  simp only [used,data,work,histories,List.length_append,List.length_map,hh,
    StepHistory.wires,List.length_cons,List.length_nil,h.integers,h.coefficients]
  omega

/-- Select fresh reserved history after preserving the old triple as past.
This operation only changes the layout; it does not erase any history bit. -/
def StepLayout.nextHistory (L : StepLayout) : StepLayout :=
  match L.future with
  | [] => L
  | next::rest => { L with history:=next, past:=L.history::L.past, future:=rest }

theorem StepLayout.nextHistory_used_perm (L : StepLayout) : L.nextHistory.used.Perm L.used := by
  unfold nextHistory
  split
  · exact List.Perm.refl _
  · rename_i next rest he
    apply List.perm_iff_count.mpr
    intro w
    simp only [used,data,work,histories,he,List.flatMap_cons,List.count_append]
    omega

theorem StepLayout.nextHistory_valid (L : StepLayout) (h : L.Valid) : L.nextHistory.Valid := by
  have hn := L.nextHistory_used_perm.nodup_iff.mpr h.unique
  unfold nextHistory
  split
  · exact h
  · rename_i next rest he
    exact ⟨by simpa only [nextHistory,he] using hn,h.integers,h.coefficients,
      h.mask_g,h.mask_v,h.mask_z,h.carry_g,h.carry_v,h.carry_z⟩

/-- Combined view/history transition, ready for the next step structurally.
Freshness of the newly selected triple remains a state-level caller obligation. -/
def StepLayout.next (L : StepLayout) : StepLayout := L.halfView.nextHistory

theorem StepLayout.next_valid (L : StepLayout) (h : L.Valid) : L.next.Valid :=
  L.halfView.nextHistory_valid (L.halfView_valid h)

theorem StepLayout.next_support (L : StepLayout) : L.next.used.toFinset=L.used.toFinset := by
  have hh := L.halfView.nextHistory_used_perm.trans L.halfView_used_perm
  ext w
  simpa only [List.mem_toFinset] using hh.mem_iff

/-- A small concrete witness with unequal arithmetic widths and genuinely
shared prefix workspace, plus two separate history triples. -/
def stepLayoutExample : StepLayout where
  f := [0,1]
  g := ⟨2,[],3⟩
  fv := ⟨4,[5],6⟩
  gv := [7,8,9]
  z := ⟨10,[],11⟩
  mask := [12,13,14]
  carry := [15,16]
  detect := fun w => w+15
  one := 19
  cin := 20
  history := ⟨21,22,23⟩
  past := []
  future := [⟨24,25,26⟩]

theorem stepLayoutExample_valid : stepLayoutExample.Valid := by
  constructor <;> decide

theorem stepLayoutExample_reuses_prefixes :
    stepLayoutExample.gmask=[12,13] ∧ stepLayoutExample.vmask=[12,13,14] ∧
    stepLayoutExample.cz=[12,13] ∧ stepLayoutExample.gcarry=[15] ∧
    stepLayoutExample.vcarry=[15,16] ∧ stepLayoutExample.cc=[15] := by decide

/-- Row routing and branch-tag inputs have distinct physical wires. -/
theorem StepLayout.control_routing_nodup (L : StepLayout) (h : L.Valid) :
    [L.history.active,L.z.sign,L.g.low,L.history.parity,L.history.swap].Nodup ∧
    (L.history.swap::((L.f++L.fv.wires)++(L.g.wires++L.gv))).Nodup ∧
    (L.history.active::L.fv.wires).Nodup := by
  refine ⟨?_,?_,?_⟩
  all_goals
    apply L.select_nodup h
    intro w
    simp only [used,data,work,histories,StepHistory.wires,StepRow.wires,
      List.count_append,List.count_cons,List.count_nil]
    omega

/-- Arbitrary widths can be stated independently of the physical allocation. -/
def StepLayout.Sized (L : StepLayout) (n v k : Nat) : Prop :=
  L.g.wires.length=n ∧ L.gv.length=v ∧ L.z.wires.length=k

theorem StepLayout.halfView_sized (L : StepLayout) (n v k : Nat) (h : L.Sized n v k) :
    L.halfView.Sized n v k := by
  simpa only [Sized,halfView,StepRow.halfView_length] using h

theorem StepLayout.program_counts (L : StepLayout) (h : L.Valid) (n v k : Nat)
    (hw : L.Sized n v k) :
    toffoliCount L.program=5*n+5*v+k-4 ∧
    measurementCount L.program=4*n+3*v+k-5 := by
  obtain ⟨hgm,hvm,hcz,hgc,hvc,hcc⟩ := L.prefix_lengths h
  have hh := forwardStep_counts L.history.swap L.history.parity L.cin L.history.active
    L.g.low L.g.sign L.fv.low L.fv.sign L.one L.z.sign
    L.f L.g.middle L.gmask L.gcarry L.fv.middle L.vmask L.gv L.vcarry
    L.cz L.z.wires L.cc L.bits (L.control_routing_nodup h).2.1 h.integers h.coefficients
    L.bits_inputs (h.integers.trans hgm.symm) (by simpa [StepRow.wires] using hgm)
    (by simpa [StepRow.wires] using hgc) (h.coefficients.trans hvm.symm) hvm hvc hcz hcc
  have hn : L.g.middle.length+2=n := by simpa [Sized,StepRow.wires] using hw.1
  have hv : L.fv.middle.length+2=v := by
    simpa [StepRow.wires] using h.coefficients.trans hw.2.1
  simpa only [program,hn,hv,hw.2.2] using hh

/-- The program never touches either past or still-reserved history. -/
theorem StepLayout.reserved_frame (L : StepLayout) (h : L.Valid)
    (s : State) (m : List Bool) (w : Wire)
    (hw : w∈L.past.flatMap StepHistory.wires++L.future.flatMap StepHistory.wires) :
    (run L.program m s).basis w=s.basis w := by
  apply run_preserves_outside
  intro hh
  have hm := L.program_current_support h hh
  have hn : ((L.data++L.work++L.history.wires)++
      (L.past.flatMap StepHistory.wires++L.future.flatMap StepHistory.wires)).Nodup := by
    simpa only [used,histories,List.append_assoc] using h.unique
  exact List.disjoint_left.mp (List.nodup_append'.mp hn).2.2
    (List.mem_toFinset.mp hm) hw

def StepLayout.FutureClean (L : StepLayout) (s : BasisState) : Prop :=
  ∀ w∈L.future.flatMap StepHistory.wires,s w=false

theorem StepLayout.future_clean_preserved (L : StepLayout) (h : L.Valid)
    (s : State) (m : List Bool) (hf : L.FutureClean s.basis) :
    L.FutureClean (run L.program m s).basis := by
  intro w hw
  rw [L.reserved_frame h s m w (List.mem_append_right _ hw)]
  exact hf w hw

/-- A reserved next triple is fresh after execution; the old triple is retained.
The nonempty-future premise prevents silently reusing exhausted history. -/
theorem StepLayout.next_fresh (L : StepLayout) (h : L.Valid)
    (s : State) (m : List Bool) (hf : L.FutureClean s.basis) (hne : L.future≠[]) :
    L.next.Fresh (run L.program m s).basis ∧ L.next.FutureClean (run L.program m s).basis := by
  have hp := L.future_clean_preserved h s m hf
  cases he : L.future with
  | nil => exact (hne he).elim
  | cons next rest =>
    simp only [FutureClean,he,List.flatMap_cons,List.mem_append] at hp
    constructor
    · simp only [StepLayout.next,halfView,nextHistory,he,Fresh]
      intro w hw
      exact hp w (Or.inl hw)
    · simp only [StepLayout.next,halfView,nextHistory,he,FutureClean]
      intro w hw
      exact hp w (Or.inr hw)

/-- Layout-only output view equation needed by a finite walk encoder. -/
theorem StepLayout.next_g (L : StepLayout) :
    L.next.g.wires=skywalkHalfView L.g.low (L.g.middle++[L.g.sign]) := by
  unfold next nextHistory
  split <;> exact L.g.halfView_wires

theorem StepLayout.next_sized (L : StepLayout) (n v k : Nat) (h : L.Sized n v k) :
    L.next.Sized n v k := by
  have hh := L.halfView_sized n v k h
  unfold next nextHistory
  split <;> exact hh

/-- Finite-history layout sequence; execution must stop before reusing an
exhausted current slot. Structural invariants themselves hold for every index. -/
def StepLayout.at (L : StepLayout) : Nat → StepLayout
  | 0 => L
  | i+1 => (L.at i).next

theorem StepLayout.at_valid (L : StepLayout) (h : L.Valid) (i : Nat) : (L.at i).Valid := by
  induction i with
  | zero => exact h
  | succ i ih => exact (L.at i).next_valid ih

theorem StepLayout.at_support (L : StepLayout) (i : Nat) : (L.at i).used.toFinset=L.used.toFinset := by
  induction i with
  | zero => rfl
  | succ i ih => exact (L.at i).next_support.trans ih

theorem StepLayout.at_sized (L : StepLayout) (n v k : Nat) (h : L.Sized n v k) (i : Nat) :
    (L.at i).Sized n v k := by
  induction i with
  | zero => exact h
  | succ i ih => exact (L.at i).next_sized n v k ih

theorem StepLayout.next_future_length (L : StepLayout) : L.next.future.length=L.future.length-1 := by
  unfold next nextHistory halfView
  dsimp only
  split <;> simp_all

theorem StepLayout.at_future_length (L : StepLayout) (i : Nat) :
    (L.at i).future.length=L.future.length-i := by
  induction i with
  | zero => simp [StepLayout.at]
  | succ i ih => rw [StepLayout.at,next_future_length,ih]; omega

/-- Enough reserved history for a transition before the chosen finite horizon. -/
theorem StepLayout.at_can_advance (L : StepLayout) (i : Nat) (hi : i<L.future.length) :
    (L.at i).future≠[] := by
  have hh := L.at_future_length i
  intro he
  rw [he,List.length_nil] at hh
  omega

end ECDSAAdd.Arithmetic.Divsteps
