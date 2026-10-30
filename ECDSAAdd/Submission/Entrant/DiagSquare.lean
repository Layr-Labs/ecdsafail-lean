import ECDSAAdd.Submission.Entrant.EndpointD
import ECDSAAdd.Submission.Entrant.TrimRow
set_option Elab.async false

-- DIAGONAL COMPONENT DiagonalSemantics.lean
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
section DiagonalSharing
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

/-- The unnormalized signed-row square. -/
def rawMake (xs dst pad carry : List Wire) : Program :=
  signedSquareRows xs dst pad carry ++ signedSquareTop xs dst

def rawClear (xs dst pad carry : List Wire) : Program :=
  signedSquareTop xs dst ++ signedSquareRowsClear xs dst pad carry

theorem rawMake_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawMake xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawMake xs dst pad carry) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (rawMake xs dst pad carry) m s).basis q=s.basis q := by
  let a := m.take (measurementCount (signedSquareRows xs dst pad carry))
  let b := m.drop (measurementCount (signedSquareRows xs dst pad carry))
  have r := signedSquareRows_correct xs dst pad carry hn hd (Or.inr hp) hc s a 0 h0
    ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp h0 q (List.mem_of_mem_drop hq)))
    (by simp [regValue_append,hp0,hc0])
  let u := run (signedSquareRows xs dst pad carry) a s
  have nt : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append] at h ⊢; omega
  have t := signedSquareTop_correct xs dst nt hd u b r.2.2.2.2
  have source (q : Wire) (hq : q∈xs) : u.basis q=s.basis q := r.2.2.1 q (by
    intro bad
    have h := List.nodup_iff_count.mp nt q
    have a := List.count_pos_iff.mpr hq; have b := List.count_pos_iff.mpr bad
    simp only [List.count_append] at h; omega)
  have topSame : signedTopTerm xs u.basis=signedTopTerm xs s.basis :=
    signedTopTerm_congr xs _ _ source
  simp only [rawMake,run_append]
  refine ⟨t.1.trans r.1,?_,fun q hq => (t.2.2.1 q hq).trans (r.2.2.1 q hq)⟩
  rw [t.2.1,r.2.1,topSame,Nat.zero_add,←signedRawValue_rows_top]
  exact signedRawValue_correct xs s.basis (List.ne_nil_of_length_pos (by omega))

/-- The shared affine correction, expressed in the carry and the sum bits. -/
def sharedWord (h a b : Nat) : Nat :=
  (2^(h-1)-1-(a+b)%2^(h-1))+
    2^(h-1)*((a%2^(h-1)+b%2^(h-1))/2^(h-1))+
    2^h*(1-((a+b)/2^(h-1))%2)

theorem diagonal_identity (h a b : Nat) (hh : h=32 ∨ h=33)
    (ha : a<2^h) (hb : b<2^h) :
    (signedDiagValue (a+b) (h+1) : Int) - signedDiagValue a h - signedDiagValue b h =
      (2^h : Nat)*(sharedWord h a b + 1 : Int) - (2^(2*h-1) : Nat) := by
  rcases hh with rfl|rfl <;>
    norm_num [signedDiagValue,sharedWord] at * <;> omega


theorem sub_congr (x n y : Nat) (hy : y≤n) :
    (((x+n-y)%n : Nat) : Int) ≡ (x : Int)-y [ZMOD (n : Int)] := by
  have h : y≤x+n := by omega
  simp only [Int.ModEq,Int.natCast_mod,Int.natCast_sub h,Int.natCast_add]
  simp [Int.sub_emod,Int.add_emod]

theorem lift_sub_congr (x p n w : Nat) (hw : w+1≤n) :
    ((x%p+p*((x/p+n-w-1)%n) : Nat) : Int) ≡
      (x : Int)-(p : Int)*(w+1) [ZMOD ((p*n : Nat) : Int)] := by
  have hsub : x/p+n-w-1=x/p+n-(w+1) := by omega
  have r := sub_congr (x/p) n (w+1) hw
  rw [←hsub] at r
  have r' := (r.mul_left' (c:=(p : Int))).add_left (x%p : Nat)
  have split : ((x%p : Nat) : Int)+(p : Int)*(x/p)=x := by exact_mod_cast Nat.mod_add_div x p
  push_cast at r' ⊢
  push_cast at split
  convert r' using 1 <;> try rfl
  all_goals nlinarith only [split]

theorem lift_add_congr (x p n k : Nat) :
    ((x%p+p*((x/p+k)%n) : Nat) : Int) ≡
      (x : Int)+(p : Int)*k [ZMOD ((p*n : Nat) : Int)] := by
  have r : (((x/p+k)%n : Nat) : Int) ≡ ((x/p+k : Nat) : Int) [ZMOD (n : Int)] := by
    simp only [Int.natCast_mod]; exact Int.mod_modEq _ _
  have r' := (r.mul_left' (c:=(p : Int))).add_left (x%p : Nat)
  have split : ((x%p : Nat) : Int)+(p : Int)*(x/p)=x := by exact_mod_cast Nat.mod_add_div x p
  push_cast at r' ⊢
  push_cast at split
  convert r' using 1 <;> try rfl
  all_goals nlinarith only [split]

theorem state_ext {s t : State} (hp : s.phase=t.phase) (hb : s.basis=t.basis) : s=t := by
  cases s; cases t; simp_all

def recordPad : Program → List Bool → List Bool
  | [], _ => []
  | .measureX _ _ _ :: p, [] => false::recordPad p []
  | .measureX _ _ _ :: p, b::bs => b::recordPad p bs
  | _::p, m => recordPad p m

theorem run_recordPad (p q : Program) (m n : List Bool) (s : State) :
    run (p++q) (recordPad p m++n) s=run q n (run p m s) := by
  induction p generalizing m s with
  | nil => rfl
  | cons i p ih =>
    cases i <;> simp only [recordPad,List.cons_append,run]
    all_goals try exact ih m _
    cases m <;> simp [recordPad,ih]

theorem raw_roundtrip (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m n : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    run (rawClear xs dst pad carry) n (run (rawMake xs dst pad carry) m s)=s := by
  let rows := signedSquareRows xs dst pad carry
  let top := signedSquareTop xs dst
  let clr := signedSquareRowsClear xs dst pad carry
  have nt : (xs++dst).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append] at h ⊢; omega
  have topCancel (u : State) (a b : List Bool) : run top b (run top a u)=u := by
    have r := signedSquareTop_roundtrip xs dst nt u (recordPad top a++b)
    rw [run_recordPad] at r
    simpa only [top] using r
  have rowsCancel (a b : List Bool) : run clr b (run rows a s)=s := by
    have r := signedSquareRows_roundtrip xs dst pad carry hn hd (Or.inr hp) hc s
      (recordPad rows a++b) 0 h0
      ((regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp h0 q (List.mem_of_mem_drop hq)))
      (by simp [regValue_append,hp0,hc0])
    rw [run_recordPad] at r
    exact state_ext r.1 r.2
  simp only [rawClear,rawMake,run_append]
  rw [topCancel]
  exact rowsCancel _ _

theorem rawClear_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool)
    (h0 : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawClear xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawClear xs dst pad carry) m s).basis=0 ∧
    ∀q,q∉dst → (run (rawClear xs dst pad carry) m s).basis q=s.basis q := by
  let base : State := ⟨s.phase,fun q => if q∈dst then false else s.basis q⟩
  have away (q : Wire) (hq : q∈xs++pad++carry) : q∉dst := by
    intro bad
    have h := List.nodup_iff_count.mp hn q
    have a := List.count_pos_iff.mpr hq; have b := List.count_pos_iff.mpr bad
    simp only [List.count_append] at h a; omega
  have keep (r : List Wire) (hr : ∀q∈r,q∈xs++pad++carry) :
      regValue r base.basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun q hq => by simp [base,away q (hr q hq)])
  have d0 : regValue dst base.basis=0 := (regValue_zero _ _).mpr (fun q hq => by simp [base,hq])
  have p0 := (keep pad (fun q h => by simp [h])).trans hp0
  have c0 := (keep carry (fun q h => by simp [h])).trans hc0
  have f := rawMake_correct xs dst pad carry hn hx hd hp hc base [] d0 p0 c0
  have same : run (rawMake xs dst pad carry) [] base=s := by
    apply state_ext (t:=s) (show _=s.phase from f.1)
    funext q
    by_cases hq : q∈dst
    · apply (regValue_eq_iff dst _ _).mp _ q hq
      rw [f.2.1,keep xs (fun q h => by simp [h]),h0]
    · exact (f.2.2 q hq).trans (by simp [base,hq])
  have restore := raw_roundtrip xs dst pad carry hn hx hd hp hc base [] m d0 p0 c0
  rw [same] at restore
  rw [restore]
  exact ⟨rfl,d0,fun q hq => by simp [base,hq]⟩

/-- `rawMake` with the dead lowest carry of the first signed row copied (TrimRow). -/
def rawMakeT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimRow.mk xs dst pad carry

/-- `rawClear` with the dead lowest carry of the first signed row copied (TrimRow). -/
def rawClearT (xs dst pad carry : List Wire) : Program := ECDSAAdd.Entrant.TrimRow.cl xs dst pad carry

theorem rawMakeT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool) (h0 : regValue dst s.basis=0)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawMakeT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawMakeT xs dst pad carry) m s).basis=
      (regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length ∧
    ∀q,q∉dst → (run (rawMakeT xs dst pad carry) m s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimRow.mk_exists xs dst pad carry hn hx hd hp hc s m h0 hc0
  rw [rawMakeT,hR]
  exact rawMake_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawClearT_correct (xs dst pad carry : List Wire)
    (hn : (xs++dst++pad++carry).Nodup) (hx : 2≤xs.length)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : xs.length-1≤carry.length)
    (s : State) (m : List Bool)
    (h0 : regValue dst s.basis=(regValue xs s.basis)^2+signedDiagValue (regValue xs s.basis) xs.length)
    (hp0 : regValue pad s.basis=0) (hc0 : regValue carry s.basis=0) :
    (run (rawClearT xs dst pad carry) m s).phase=s.phase ∧
    regValue dst (run (rawClearT xs dst pad carry) m s).basis=0 ∧
    ∀q,q∉dst → (run (rawClearT xs dst pad carry) m s).basis q=s.basis q := by
  obtain ⟨R,hR⟩ := ECDSAAdd.Entrant.TrimRow.cl_exists xs dst pad carry hn hx hd hp hc s m h0 hc0
  rw [rawClearT,hR]
  exact rawClear_correct xs dst pad carry hn hx hd hp hc s R h0 hp0 hc0

theorem rawT_counts (xs dst pad carry : List Wire)
    (hx : 2≤xs.length) (hd : dst.length=2*xs.length) (hp : 1≤pad.length)
    (hc : xs.length-1≤carry.length) :
    (toffoliCount (rawMakeT xs dst pad carry)+1=toffoliCount (rawMake xs dst pad carry) ∧
      measurementCount (rawMakeT xs dst pad carry)+1=measurementCount (rawMake xs dst pad carry)) ∧
    (toffoliCount (rawClearT xs dst pad carry)+1=toffoliCount (rawClear xs dst pad carry) ∧
      measurementCount (rawClearT xs dst pad carry)+1=measurementCount (rawClear xs dst pad carry)) :=
  ECDSAAdd.Entrant.TrimRow.counts xs dst pad carry hx hd hp hc

theorem rawT_slots (xs dst pad carry : List Wire) :
    Challenge.gateSlots (rawMakeT xs dst pad carry)≤Challenge.gateSlots (rawMake xs dst pad carry) ∧
    Challenge.gateSlots (rawClearT xs dst pad carry)≤Challenge.gateSlots (rawClear xs dst pad carry) :=
  ECDSAAdd.Entrant.TrimRow.slots xs dst pad carry

theorem rawT_wires (xs dst pad carry : List Wire) (X : Finset Wire)
    (h1 : wires (signedSquareRows xs dst pad carry)⊆X) (h2 : wires (signedSquareTop xs dst)⊆X)
    (h3 : wires (signedSquareRowsClear xs dst pad carry)⊆X) :
    wires (rawMakeT xs dst pad carry)⊆X ∧ wires (rawClearT xs dst pad carry)⊆X := by
  have w := ECDSAAdd.Entrant.TrimRow.wires_sub xs dst pad carry
  simp only [wires_append] at w
  exact ⟨w.1.trans (Finset.union_subset h1 h2),w.2.trans (Finset.union_subset h2 h3)⟩

theorem rawT_physical (xs dst pad carry : List Wire)
    (h1 : GatePhysical (signedSquareRows xs dst pad carry)) (h2 : GatePhysical (signedSquareTop xs dst))
    (h3 : GatePhysical (signedSquareRowsClear xs dst pad carry)) :
    GatePhysical (rawMakeT xs dst pad carry) ∧ GatePhysical (rawClearT xs dst pad carry) :=
  ECDSAAdd.Entrant.TrimRow.physical xs dst pad carry
    (by rw [gatePhysical_append]; exact ⟨h1,h2⟩) (by rw [gatePhysical_append]; exact ⟨h2,h3⟩)

def parityLoad (as bs ss : List Wire) (h : Nat) (q : Wire) : Program :=
  [.CX (as.getD (h-1) 0) q,.CX (bs.getD (h-1) 0) q,.CX (ss.getD (h-1) 0) q]

def correctionBits (h : Nat) (ss : List Wire) (q : Wire) : List MappedBit :=
  mappedRead (ss.take (h-1)) true++
    [{wire:=some q,flip:=false},{wire:=some (ss.getD (h-1) 0),flip:=true},
      {wire:=none,flip:=false}]

theorem parity_value (h : Nat) (as bs ss : List Wire) (s : BasisState)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hv : regValue ss s=regValue as s+regValue bs s) :
    (s (as.getD (h-1) 0) ^^ s (bs.getD (h-1) 0) ^^ s (ss.getD (h-1) 0)).toNat =
      (regValue as s%2^(h-1)+regValue bs s%2^(h-1))/2^(h-1) := by
  have ah := regValue_bit as (h-1) 0 s (by rcases hh with rfl|rfl <;> omega)
  have bh := regValue_bit bs (h-1) 0 s (by rcases hh with rfl|rfl <;> omega)
  have sh := regValue_bit ss (h-1) 0 s (by rcases hh with rfl|rfl <;> omega)
  have al := regValue_lt as s; have bl := regValue_lt bs s
  rw [hal] at al; rw [hbl] at bl
  cases a : s (as.getD (h-1) 0) <;> cases b : s (bs.getD (h-1) 0) <;>
    cases c : s (ss.getD (h-1) 0) <;> simp only [a,b,c,Bool.toNat_false,Bool.toNat_true] at * <;>
    rcases hh with rfl|rfl <;> norm_num at * <;> omega


def load (a b c q cin : Wire) : Program := [.CX a q,.CX b q,.CX c q,.X cin]
def unload (a b c q cin : Wire) : Program := [.X cin,.CX a q,.CX b q,.CX c q]

theorem load_effect (a b c q cin : Wire) (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hiq : cin≠q) (s : State) (m : List Bool) :
    run (load a b c q cin) m s=⟨s.phase,
      writeBit (writeBit s.basis q (s.basis q ^^ s.basis a ^^ s.basis b ^^ s.basis c)) cin (!s.basis cin)⟩ := by
  simp only [load,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases wq : w=q <;> by_cases wi : w=cin <;>
    simp [writeBit,Function.update,ha,hb,hc,hiq,Ne.symm hiq,wq,wi,Bool.xor_assoc]

theorem unload_effect (a b c q cin : Wire) (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hia : a≠cin) (hib : b≠cin) (hic : c≠cin) (hiq : cin≠q) (s : State) (m : List Bool) :
    run (unload a b c q cin) m s=⟨s.phase,
      writeBit (writeBit s.basis cin (!s.basis cin)) q
        (s.basis q ^^ s.basis a ^^ s.basis b ^^ s.basis c)⟩ := by
  simp only [unload,run]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases wq : w=q <;> by_cases wi : w=cin <;>
    simp [writeBit,Function.update,ha,hb,hc,hia,hib,hic,hiq,Ne.symm hiq,wq,wi,Bool.xor_assoc]

theorem load_sandwich (a b c q cin : Wire) (D : List Wire)
    (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hia : a≠cin) (hib : b≠cin) (hic : c≠cin) (hiq : cin≠q)
    (ao : a∉D) (bo : b∉D) (co : c∉D) (qo : q∉D) (io : cin∉D)
    (s v : State) (m n : List Bool)
    (hp : v.phase=(run (load a b c q cin) m s).phase)
    (hf : ∀w,w∉D → v.basis w=(run (load a b c q cin) m s).basis w) :
    (run (unload a b c q cin) n v).phase=s.phase ∧
    regValue D (run (unload a b c q cin) n v).basis=regValue D v.basis ∧
    ∀w,w∉D → (run (unload a b c q cin) n v).basis w=s.basis w := by
  rw [load_effect a b c q cin ha hb hc hiq] at hp hf
  rw [unload_effect a b c q cin ha hb hc hia hib hic hiq]
  refine ⟨hp,?_,?_⟩
  · apply regValue_congr
    intro w hw
    have wq : w≠q := fun e => qo (e ▸ hw)
    have wi : w≠cin := fun e => io (e ▸ hw)
    simp [writeBit,wq,wi]
  · intro w hw
    have fa := hf a ao; have fb := hf b bo; have fc := hf c co
    have fq := hf q qo; have fi := hf cin io; have fw := hf w hw
    simp only [writeBit,Function.update] at *
    by_cases wq : w=q
    · subst w
      simp [ha,hb,hc,hia,hib,hic,hiq,Ne.symm hiq] at *
      rw [fq,fa,fb,fc]
      simp [Bool.xor_assoc]
    · by_cases wi : w=cin
      · subst w
        simp [wq,fi]
      · simp [wq,wi,fw]


def Update (dst : List Wire) (delta : Int) (s t : State) : Prop :=
  t.phase=s.phase ∧ (∀q,q∉dst → t.basis q=s.basis q) ∧
    (regValue dst t.basis : Int) ≡ (regValue dst s.basis : Int)+delta [ZMOD (2^dst.length : Nat)]

theorem Update.seq {dst : List Wire} {d e : Int} {s u t : State}
    (hu : Update dst d s u) (ht : Update dst e u t) : Update dst (d+e) s t := by
  refine ⟨ht.1.trans hu.1,fun q hq => (ht.2.1 q hq).trans (hu.2.1 q hq),?_⟩
  convert ht.2.2.trans (hu.2.2.add_right e) using 1 <;> ring

theorem rv_split (dst : List Wire) (k : Nat) (hk : k≤dst.length) (s : BasisState) :
    regValue dst s=regValue (dst.take k) s+2^k*regValue (dst.drop k) s := by
  have e := regValue_append (dst.take k) (dst.drop k) s
  simpa only [List.take_append_drop,List.length_take,Nat.min_eq_left hk] using e

theorem drop_count (dst : List Wire) (k : Nat) (q : Wire) : (dst.drop k).count q≤dst.count q := by
  have e : (dst.take k).count q+(dst.drop k).count q=dst.count q := by
    rw [←List.count_append,List.take_append_drop]
  omega

theorem drop_views (dst carry : List Wire) (cin : Wire) (k : Nat)
    (hn : (cin::dst++carry).Nodup) :
    (cin::dst.drop k++carry).Nodup ∧ List.Disjoint (dst.take k) (dst.drop k) := by
  refine ⟨?_,?_⟩
  · apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp hn q; have d := drop_count dst k q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  · have n : (dst.take k++dst.drop k).Nodup := by
      rw [List.take_append_drop]
      exact (List.nodup_append.mp (List.nodup_cons.mp hn).2).1
    exact List.disjoint_left.mpr (fun q hq ht => (List.nodup_append.mp n).2.2 q hq q ht rfl)

theorem sub_drop (bits : List MappedBit) (dst carry : List Wire) (cin : Wire) (k : Nat)
    (hk : k≤dst.length) (hn : (cin::dst++carry).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::dst++carry)
    (hl : bits.length=dst.length-k) (hc : carry.length+1=dst.length-k)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    Update dst (-((2^k : Nat) : Int)*(mappedValue bits s.basis+(s.basis cin).toNat)) s
      (run (mappedSub bits (dst.drop k) carry cin) m s) := by
  have views := drop_views dst carry cin k hn
  have r := BalancedInverse.mappedSub_any_correct bits (dst.drop k) carry cin views.1
    (fun q hq bad => hs q hq (by
      simp only [List.mem_cons,List.mem_append] at bad ⊢
      rcases bad with h|h|h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (List.mem_of_mem_drop h))
      · exact Or.inr h))
    (by simpa using hl) (by simpa using hc) s m hclean
  let t := run (mappedSub bits (dst.drop k) carry cin) m s
  have low : regValue (dst.take k) t.basis=regValue (dst.take k) s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.1 q (List.disjoint_left.mp views.2 hq))
  have c : (s.basis cin).toNat≤1 := by cases s.basis cin <;> decide
  have v := mappedValue_lt bits s.basis
  rw [hl] at v
  have sc := sub_congr (regValue (dst.drop k) s.basis) (2^(dst.length-k))
    (mappedValue bits s.basis+(s.basis cin).toNat) (by omega)
  have e : regValue (dst.drop k) t.basis =
      (regValue (dst.drop k) s.basis+2^(dst.length-k)-
        (mappedValue bits s.basis+(s.basis cin).toNat))%2^(dst.length-k) := by
    simpa only [List.length_drop,Nat.sub_sub] using r.2.2
  rw [←e] at sc
  have sc' := (sc.mul_left' (c:=((2^k : Nat) : Int))).add_left
    (regValue (dst.take k) s.basis : Nat)
  have ep : (2^k : Nat)*(2^(dst.length-k))=2^dst.length := by rw [←pow_add]; congr 1; omega
  have epI : ((2^k : Nat) : Int)*((2^(dst.length-k) : Nat) : Int)=((2^dst.length : Nat) : Int) := by
    exact_mod_cast ep
  rw [epI] at sc'
  refine ⟨r.1,fun q hq => r.2.1 q (fun bad => hq (List.mem_of_mem_drop bad)),?_⟩
  rw [rv_split dst k hk t.basis,low]
  push_cast at sc' ⊢
  have split := congrArg (fun x : Nat => (x : Int)) (rv_split dst k hk s.basis)
  push_cast at split
  convert sc' using 1 <;> try rfl
  nlinarith only [split]


theorem add_drop (bits : List MappedBit) (dst carry : List Wire) (cin : Wire) (k : Nat)
    (hk : k≤dst.length) (hn : (cin::dst++carry).Nodup)
    (hs : ∀q∈mappedWires bits,q∉cin::dst++carry)
    (hl : bits.length=dst.length-k) (hc : carry.length+1=dst.length-k)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) :
    Update dst (((2^k : Nat) : Int)*(mappedValue bits s.basis+(s.basis cin).toNat)) s
      (run (mappedAdd bits (dst.drop k) carry cin) m s) := by
  have views := drop_views dst carry cin k hn
  have r := mappedAdd_correct bits (dst.drop k) carry cin views.1
    (fun q hq bad => hs q hq (by
      simp only [List.mem_cons,List.mem_append] at bad ⊢
      rcases bad with h|h|h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (List.mem_of_mem_drop h))
      · exact Or.inr h))
    (by simpa using hl) (by simpa using hc) s m hclean
  let t := run (mappedAdd bits (dst.drop k) carry cin) m s
  have low : regValue (dst.take k) t.basis=regValue (dst.take k) s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.1 q (List.disjoint_left.mp views.2 hq))
  have sc : (((mappedValue bits s.basis+regValue (dst.drop k) s.basis+(s.basis cin).toNat)%
      2^(dst.length-k) : Nat) : Int) ≡
      ((mappedValue bits s.basis+regValue (dst.drop k) s.basis+(s.basis cin).toNat : Nat) : Int)
      [ZMOD (2^(dst.length-k) : Nat)] := by
    simp only [Int.natCast_mod]; exact Int.mod_modEq _ _
  have e : regValue (dst.drop k) t.basis =
      (mappedValue bits s.basis+regValue (dst.drop k) s.basis+(s.basis cin).toNat)%2^(dst.length-k) := by
    simpa only [List.length_drop] using r.2.2
  rw [←e] at sc
  have sc' := (sc.mul_left' (c:=((2^k : Nat) : Int))).add_left
    (regValue (dst.take k) s.basis : Nat)
  have ep : (2^k : Nat)*(2^(dst.length-k))=2^dst.length := by rw [←pow_add]; congr 1; omega
  have epI : ((2^k : Nat) : Int)*((2^(dst.length-k) : Nat) : Int)=((2^dst.length : Nat) : Int) := by
    exact_mod_cast ep
  rw [epI] at sc'
  refine ⟨r.1,fun q hq => r.2.1 q (fun bad => hq (List.mem_of_mem_drop bad)),?_⟩
  rw [rv_split dst k hk t.basis,low]
  push_cast at sc' ⊢
  have split := congrArg (fun x : Nat => (x : Int)) (rv_split dst k hk s.basis)
  push_cast at split
  convert sc' using 1 <;> try rfl
  nlinarith only [split]

theorem getD_in (l : List Wire) (k : Nat) (hk : k<l.length) : l.getD k 0∈l := by
  rw [List.getD_eq_getElem l 0 hk]
  exact List.getElem_mem hk

theorem correctionBits_length (h : Nat) (ss : List Wire) (q : Wire)
    (hh : 1≤h) (hl : h≤ss.length) : (correctionBits h ss q).length=h+2 := by
  simp only [correctionBits,List.length_append,mappedRead_length,List.length_take,List.length_cons,List.length_nil]
  omega

theorem correctionBits_value (h a b : Nat) (ss : List Wire) (q : Wire) (s : BasisState)
    (hh : 1≤h) (hsl : ss.length=h+1) (hv : regValue ss s=a+b)
    (hq : (s q).toNat=(a%2^(h-1)+b%2^(h-1))/2^(h-1)) :
    mappedValue (correctionBits h ss q) s=sharedWord h a b := by
  have take : regValue (ss.take (h-1)) s=regValue ss s%2^(h-1) := by
    have e := rv_split ss (h-1) (by omega) s
    rw [e,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt]
    simpa only [List.length_take,Nat.min_eq_left (by omega : h-1≤ss.length)] using regValue_lt (ss.take (h-1)) s
  have bit := regValue_bit ss (h-1) 0 s (by omega)
  have neg : (!s (ss.getD (h-1) 0)).toNat=1-(s (ss.getD (h-1) 0)).toNat := by
    cases s (ss.getD (h-1) 0) <;> decide
  simp only [correctionBits,mappedValue_append,mappedRead_complement,mappedRead_length,
    mappedValue,MappedBit.value,Option.map_some,Option.getD_some,Option.map_none,Option.getD_none,
    Bool.false_xor,Bool.true_xor,Bool.xor_false,Bool.toNat_false,Nat.mul_zero,Nat.add_zero]
  rw [take,neg,bit,hv,hq,List.length_take,Nat.min_eq_left (by omega : h-1≤ss.length)]
  have ep : 2^(h-1)*2=2^h := by rw [←pow_succ]; congr 1; omega
  dsimp only [sharedWord]
  rw [←ep]
  ring


def loadedSub (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat) : Program :=
  load a b c q cin ++ (mappedSub bits (dst.drop k) carry cin ++ unload a b c q cin)

theorem loadedSub_correct (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat)
    (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hia : a≠cin) (hib : b≠cin) (hic : c≠cin) (hiq : cin≠q)
    (ao : a∉dst) (bo : b∉dst) (co : c∉dst) (qo : q∉dst) (io : cin∉dst) (qc : q∉carry)
    (hk : k≤dst.length) (hn : (cin::dst++carry).Nodup)
    (hs : ∀w∈mappedWires bits,w∉cin::dst++carry)
    (hl : bits.length=dst.length-k) (hcl : carry.length+1=dst.length-k)
    (s : State) (m : List Bool) (hclean : ∀w∈carry,s.basis w=false) :
    let u := run (load a b c q cin) [] s
    Update dst (-((2^k : Nat) : Int)*(mappedValue bits u.basis+(u.basis cin).toNat)) s
      (run (loadedSub a b c q cin bits dst carry k) m s) := by
  let u := run (load a b c q cin) [] s
  let body := mappedSub bits (dst.drop k) carry cin
  let f := m.take (measurementCount body)
  let g := m.drop (measurementCount body)
  let v := run body f u
  have ui : ∀w∈carry,u.basis w=false := by
    intro w hw
    have wi : w≠cin := fun e => (List.nodup_cons.mp hn).1 (by simp [←e,hw])
    have wq : w≠q := fun e => qc (e ▸ hw)
    dsimp only [u]
    rw [load_effect a b c q cin ha hb hc hiq]
    simpa [writeBit,wi,wq] using hclean w hw
  have r := sub_drop bits dst carry cin k hk hn hs hl hcl u f ui
  have san := load_sandwich a b c q cin dst ha hb hc hia hib hic hiq ao bo co qo io s v [] g r.1 r.2.1
  have ud : regValue dst u.basis=regValue dst s.basis := by
    apply regValue_congr; intro w hw
    have wq : w≠q := fun e => qo (e ▸ hw)
    have wi : w≠cin := fun e => io (e ▸ hw)
    dsimp only [u]
    rw [load_effect a b c q cin ha hb hc hiq]
    simp [writeBit,wq,wi]
  have out : Update dst (-((2^k : Nat) : Int)*(mappedValue bits u.basis+(u.basis cin).toNat)) s
      (run (unload a b c q cin) g v) := by
    refine ⟨san.1,san.2.2,?_⟩
    rw [san.2.1]
    simpa only [ud] using r.2.2
  have lm : measurementCount (load a b c q cin)=0 := rfl
  simpa only [loadedSub,run_append,lm,List.take_zero,List.drop_zero,u,body,f,g,v] using out

def loadedAdd (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat) : Program :=
  load a b c q cin ++ (mappedAdd bits (dst.drop k) carry cin ++ unload a b c q cin)

theorem loadedAdd_correct (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat)
    (ha : a≠q) (hb : b≠q) (hc : c≠q)
    (hia : a≠cin) (hib : b≠cin) (hic : c≠cin) (hiq : cin≠q)
    (ao : a∉dst) (bo : b∉dst) (co : c∉dst) (qo : q∉dst) (io : cin∉dst) (qc : q∉carry)
    (hk : k≤dst.length) (hn : (cin::dst++carry).Nodup)
    (hs : ∀w∈mappedWires bits,w∉cin::dst++carry)
    (hl : bits.length=dst.length-k) (hcl : carry.length+1=dst.length-k)
    (s : State) (m : List Bool) (hclean : ∀w∈carry,s.basis w=false) :
    let u := run (load a b c q cin) [] s
    Update dst (((2^k : Nat) : Int)*(mappedValue bits u.basis+(u.basis cin).toNat)) s
      (run (loadedAdd a b c q cin bits dst carry k) m s) := by
  let u := run (load a b c q cin) [] s
  let body := mappedAdd bits (dst.drop k) carry cin
  let f := m.take (measurementCount body)
  let g := m.drop (measurementCount body)
  let v := run body f u
  have ui : ∀w∈carry,u.basis w=false := by
    intro w hw
    have wi : w≠cin := fun e => (List.nodup_cons.mp hn).1 (by simp [←e,hw])
    have wq : w≠q := fun e => qc (e ▸ hw)
    dsimp only [u]
    rw [load_effect a b c q cin ha hb hc hiq]
    simpa [writeBit,wi,wq] using hclean w hw
  have r := add_drop bits dst carry cin k hk hn hs hl hcl u f ui
  have san := load_sandwich a b c q cin dst ha hb hc hia hib hic hiq ao bo co qo io s v [] g r.1 r.2.1
  have ud : regValue dst u.basis=regValue dst s.basis := by
    apply regValue_congr; intro w hw
    have wq : w≠q := fun e => qo (e ▸ hw)
    have wi : w≠cin := fun e => io (e ▸ hw)
    dsimp only [u]
    rw [load_effect a b c q cin ha hb hc hiq]
    simp [writeBit,wq,wi]
  have out : Update dst (((2^k : Nat) : Int)*(mappedValue bits u.basis+(u.basis cin).toNat)) s
      (run (unload a b c q cin) g v) := by
    refine ⟨san.1,san.2.2,?_⟩
    rw [san.2.1]
    simpa only [ud] using r.2.2
  have lm : measurementCount (load a b c q cin)=0 := rfl
  simpa only [loadedAdd,run_append,lm,List.take_zero,List.drop_zero,u,body,f,g,v] using out


theorem nd_count {l L : List Wire} (hn : L.Nodup) (h : ∀q,l.count q≤L.count q) : l.Nodup :=
  List.nodup_iff_count_le_one.mpr (fun q => (h q).trans (List.nodup_iff_count_le_one.mp hn q))

theorem dis_count {L r t : List Wire} (hn : L.Nodup) (h : ∀q,r.count q+t.count q≤L.count q)
    (q : Wire) (hq : q∈r) : q∉t := by
  intro bad
  have a := List.count_pos_iff.mpr hq; have b := List.count_pos_iff.mpr bad
  have c := List.nodup_iff_count_le_one.mp hn q; have d := h q; omega

theorem correctionBits_wires (h : Nat) (ss : List Wire) (q : Wire) :
    mappedWires (correctionBits h ss q)=ss.take (h-1)++[q,ss.getD (h-1) 0] := by
  simp only [correctionBits,mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
    Option.toList_some,Option.toList_none,List.nil_append,List.append_nil]
  rw [show List.flatMap (fun b : MappedBit => b.wire.toList) (mappedRead (ss.take (h-1)) true)=
    ss.take (h-1) from mappedRead_wires _ true]
  rfl

theorem sharedSub_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)) s
      (run (loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
        (correctionBits h ss q) dst (carry.take (h+1)) h) m s) := by
  have hpos : 1≤h := by rcases hh with rfl|rfl <;> omega
  have out (w : Wire) (hw : w∈as++bs++ss) : w∉cin::q::dst++carry :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have qo : q∉cin::dst++carry := dis_count (r:=[q]) hn
    (fun w => by simp only [List.count_cons,List.count_append,List.count_singleton,List.count_nil]; omega) q (by simp)
  have io : cin∉dst++carry := dis_count (r:=[cin]) hn
    (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
  let a := as.getD (h-1) 0
  let b := bs.getD (h-1) 0
  let c := ss.getD (h-1) 0
  have am : a∈as++bs++ss := by simp only [List.mem_append]; exact Or.inl (Or.inl (getD_in as _ (by omega)))
  have bm : b∈as++bs++ss := by simp only [List.mem_append]; exact Or.inl (Or.inr (getD_in bs _ (by omega)))
  have cm : c∈as++bs++ss := by simp only [List.mem_append]; exact Or.inr (getD_in ss _ (by omega))
  have aq : a≠q := fun e => out a am (by simp [e])
  have bq : b≠q := fun e => out b bm (by simp [e])
  have cq : c≠q := fun e => out c cm (by simp [e])
  have ai : a≠cin := fun e => out a am (by simp [e])
  have bi : b≠cin := fun e => out b bm (by simp [e])
  have ci : c≠cin := fun e => out c cm (by simp [e])
  have iq : cin≠q := fun e => qo (by simp [e])
  have src (w : Wire) (hw : w∈mappedWires (correctionBits h ss q)) : w∉cin::dst++carry := by
    rw [correctionBits_wires] at hw
    rcases List.mem_append.mp hw with hw|hw
    · have o := out w (List.mem_append_right _ (List.mem_of_mem_take hw))
      intro bad; exact o (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact qo
      · have o := out c cm
        intro bad; exact o (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
  have tc (w : Wire) (hw : w∈carry.take (h+1)) : w∈carry := List.mem_of_mem_take hw
  have tn : (cin::dst++carry.take (h+1)).Nodup := nd_count hn (fun w => by
    have t := (List.take_sublist (h+1) carry).count_le w
    simp only [List.count_cons,List.count_append]; omega)
  have hs : ∀w∈mappedWires (correctionBits h ss q),w∉cin::dst++carry.take (h+1) := by
    intro w hw bad; apply src w hw
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    rcases bad with (bad|bad)|bad
    · exact Or.inl (Or.inl bad)
    · exact Or.inl (Or.inr bad)
    · exact Or.inr (tc w bad)
  have r := loadedSub_correct a b c q cin (correctionBits h ss q) dst (carry.take (h+1)) h aq bq cq ai bi ci iq
    (fun hm => out a am (by simp [hm])) (fun hm => out b bm (by simp [hm]))
    (fun hm => out c cm (by simp [hm])) (fun hm => qo (by simp [hm]))
    (fun hm => io (by simp [hm])) (fun hm => qo (by simp [tc q hm])) (by omega) tn hs
    (by rw [correctionBits_length h ss q hpos (by omega),hdl]; omega)
    (by simp only [List.length_take]; omega) s m
    (fun w hw => (regValue_zero _ _).mp hc0 w (tc w hw))
  let u := run (load a b c q cin) [] s
  have us : regValue ss u.basis=regValue ss s.basis := by
    apply regValue_congr; intro w hw
    have o := out w (List.mem_append_right _ hw)
    have wi : w≠cin := fun e => o (by simp [e])
    have wq : w≠q := fun e => o (by simp [e])
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp [writeBit,wi,wq]
  have uq : (u.basis q).toNat=(regValue as s.basis%2^(h-1)+regValue bs s.basis%2^(h-1))/2^(h-1) := by
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp only [writeBit,Function.update,Ne.symm iq,if_false,if_true,hq0,Bool.false_xor]
    exact parity_value h as bs ss s.basis hh hal hbl hsl hv
  have ui : u.basis cin=true := by
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp [writeBit,hi0]
  have uv := correctionBits_value h (regValue as s.basis) (regValue bs s.basis) ss q u.basis hpos hsl
    (us.trans hv) uq
  simpa only [show run (load a b c q cin) [] s=u from rfl,uv,ui,Bool.toNat_true] using r

theorem sharedAdd_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)) s
      (run (loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
        (correctionBits h ss q) dst (carry.take (h+1)) h) m s) := by
  have hpos : 1≤h := by rcases hh with rfl|rfl <;> omega
  have out (w : Wire) (hw : w∈as++bs++ss) : w∉cin::q::dst++carry :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have qo : q∉cin::dst++carry := dis_count (r:=[q]) hn
    (fun w => by simp only [List.count_cons,List.count_append,List.count_singleton,List.count_nil]; omega) q (by simp)
  have io : cin∉dst++carry := dis_count (r:=[cin]) hn
    (fun w => by simp only [List.count_cons,List.count_append,List.count_nil]; omega) cin (by simp)
  let a := as.getD (h-1) 0
  let b := bs.getD (h-1) 0
  let c := ss.getD (h-1) 0
  have am : a∈as++bs++ss := by simp only [List.mem_append]; exact Or.inl (Or.inl (getD_in as _ (by omega)))
  have bm : b∈as++bs++ss := by simp only [List.mem_append]; exact Or.inl (Or.inr (getD_in bs _ (by omega)))
  have cm : c∈as++bs++ss := by simp only [List.mem_append]; exact Or.inr (getD_in ss _ (by omega))
  have aq : a≠q := fun e => out a am (by simp [e])
  have bq : b≠q := fun e => out b bm (by simp [e])
  have cq : c≠q := fun e => out c cm (by simp [e])
  have ai : a≠cin := fun e => out a am (by simp [e])
  have bi : b≠cin := fun e => out b bm (by simp [e])
  have ci : c≠cin := fun e => out c cm (by simp [e])
  have iq : cin≠q := fun e => qo (by simp [e])
  have src (w : Wire) (hw : w∈mappedWires (correctionBits h ss q)) : w∉cin::dst++carry := by
    rw [correctionBits_wires] at hw
    rcases List.mem_append.mp hw with hw|hw
    · have o := out w (List.mem_append_right _ (List.mem_of_mem_take hw))
      intro bad; exact o (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl
      · exact qo
      · have o := out c cm
        intro bad; exact o (by simp only [List.mem_cons,List.mem_append] at bad ⊢; tauto)
  have tc (w : Wire) (hw : w∈carry.take (h+1)) : w∈carry := List.mem_of_mem_take hw
  have tn : (cin::dst++carry.take (h+1)).Nodup := nd_count hn (fun w => by
    have t := (List.take_sublist (h+1) carry).count_le w
    simp only [List.count_cons,List.count_append]; omega)
  have hs : ∀w∈mappedWires (correctionBits h ss q),w∉cin::dst++carry.take (h+1) := by
    intro w hw bad; apply src w hw
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    rcases bad with (bad|bad)|bad
    · exact Or.inl (Or.inl bad)
    · exact Or.inl (Or.inr bad)
    · exact Or.inr (tc w bad)
  have r := loadedAdd_correct a b c q cin (correctionBits h ss q) dst (carry.take (h+1)) h aq bq cq ai bi ci iq
    (fun hm => out a am (by simp [hm])) (fun hm => out b bm (by simp [hm]))
    (fun hm => out c cm (by simp [hm])) (fun hm => qo (by simp [hm]))
    (fun hm => io (by simp [hm])) (fun hm => qo (by simp [tc q hm])) (by omega) tn hs
    (by rw [correctionBits_length h ss q hpos (by omega),hdl]; omega)
    (by simp only [List.length_take]; omega) s m
    (fun w hw => (regValue_zero _ _).mp hc0 w (tc w hw))
  let u := run (load a b c q cin) [] s
  have us : regValue ss u.basis=regValue ss s.basis := by
    apply regValue_congr; intro w hw
    have o := out w (List.mem_append_right _ hw)
    have wi : w≠cin := fun e => o (by simp [e])
    have wq : w≠q := fun e => o (by simp [e])
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp [writeBit,wi,wq]
  have uq : (u.basis q).toNat=(regValue as s.basis%2^(h-1)+regValue bs s.basis%2^(h-1))/2^(h-1) := by
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp only [writeBit,Function.update,Ne.symm iq,if_false,if_true,hq0,Bool.false_xor]
    exact parity_value h as bs ss s.basis hh hal hbl hsl hv
  have ui : u.basis cin=true := by
    dsimp only [u]
    rw [load_effect a b c q cin aq bq cq iq]
    simp [writeBit,hi0]
  have uv := correctionBits_value h (regValue as s.basis) (regValue bs s.basis) ss q u.basis hpos hsl
    (us.trans hv) uq
  simpa only [show run (load a b c q cin) [] s=u from rfl,uv,ui,Bool.toNat_true] using r


def correction (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h ++
    mappedAdd (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin

def correctionBack (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire) : Program :=
  mappedSub (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin ++
  loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h

theorem correction_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (-((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)+
      (2^(2*h-1) : Nat)) s (run (correction h as bs ss dst carry q cin) m s) := by
  let P := loadedSub (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h
  let f := m.take (measurementCount P)
  let g := m.drop (measurementCount P)
  let u := run P f s
  have r := sharedSub_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn s f hv hq0 hi0 hc0
  have cnd : (cin::dst++carry.take 2).Nodup := nd_count hn (fun w => by
    have c := (List.take_sublist 2 carry).count_le w
    simp only [List.count_cons,List.count_append]; omega)
  have out (w : Wire) (hw : w∈cin::carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have uc : ∀w∈carry.take 2,u.basis w=false := by
    intro w hw
    have hm := List.mem_of_mem_take hw
    exact (r.2.1 w (out w (by simp [hm]))).trans ((regValue_zero _ _).mp hc0 w hm)
  have ui : u.basis cin=false := (r.2.1 cin (out cin (by simp))).trans hi0
  have inc := add_drop (mappedConstant none 3 1) dst (carry.take 2) cin (2*h-1) (by omega) cnd
    (by simp [mappedConstant,mappedConstantBit,mappedWires])
    (by rw [mappedConstant_length,hdl]; rcases hh with rfl|rfl <;> omega)
    (by simp only [List.length_take]; rcases hh with rfl|rfl <;> omega) u g uc
  have inc' : Update dst ((2^(2*h-1) : Nat) : Int) u
      (run (mappedAdd (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin) g u) := by
    simpa only [mappedConstant_value none 3 1 u.basis (by decide),mappedEnabled,
      Option.map_none,Option.getD_none,if_true,ui,Bool.toNat_false,Nat.add_zero,Int.natCast_one,Int.natCast_zero,add_zero,mul_one]
      using inc
  have total := r.seq inc'
  simpa only [correction,run_append,P,f,g,u] using total

theorem cross_normalize (h a b : Nat) (hh : h=32 ∨ h=33) (ha : a<2^h) (hb : b<2^h) :
    (((a+b)^2+signedDiagValue (a+b) (h+1) : Nat) : Int)-
      ((a^2+signedDiagValue a h : Nat) : Int)-((b^2+signedDiagValue b h : Nat) : Int)-
      ((2^h : Nat) : Int)*(sharedWord h a b+1)+(2^(2*h-1) : Nat)=(2*a*b : Nat) := by
  have dg := diagonal_identity h a b hh ha hb
  push_cast at dg ⊢
  nlinarith only [dg]


theorem correctionBack_correct (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : h=32 ∨ h=33) (hal : as.length=h) (hbl : bs.length=h) (hsl : ss.length=h+1)
    (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length)
    (hn : (cin::q::as++bs++ss++dst++carry).Nodup)
    (s : State) (m : List Bool) (hv : regValue ss s.basis=regValue as s.basis+regValue bs s.basis)
    (hq0 : s.basis q=false) (hi0 : s.basis cin=false) (hc0 : regValue carry s.basis=0) :
    Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)-
      (2^(2*h-1) : Nat)) s (run (correctionBack h as bs ss dst carry q cin) m s) := by
  let P := mappedSub (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin
  let f := m.take (measurementCount P)
  let g := m.drop (measurementCount P)
  let u := run P f s
  have cnd : (cin::dst++carry.take 2).Nodup := nd_count hn (fun w => by
    have c := (List.take_sublist 2 carry).count_le w
    simp only [List.count_cons,List.count_append]; omega)
  have clean : ∀w∈carry.take 2,s.basis w=false :=
    fun w hw => (regValue_zero _ _).mp hc0 w (List.mem_of_mem_take hw)
  have dec := sub_drop (mappedConstant none 3 1) dst (carry.take 2) cin (2*h-1) (by omega) cnd
    (by simp [mappedConstant,mappedConstantBit,mappedWires])
    (by rw [mappedConstant_length,hdl]; rcases hh with rfl|rfl <;> omega)
    (by simp only [List.length_take]; rcases hh with rfl|rfl <;> omega) s f clean
  have dec' : Update dst (-((2^(2*h-1) : Nat) : Int)) s u := by
    simpa only [mappedConstant_value none 3 1 s.basis (by decide),mappedEnabled,
      Option.map_none,Option.getD_none,if_true,hi0,Bool.toNat_false,Int.natCast_zero,add_zero,
      Int.natCast_one,mul_one] using dec
  have out (w : Wire) (hw : w∈cin::q::as++bs++ss++carry) : w∉dst :=
    dis_count hn (fun w => by simp only [List.count_cons,List.count_append]; omega) w hw
  have keep (l : List Wire) (hl : ∀w∈l,w∈cin::q::as++bs++ss++carry) :
      regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun w hw => dec'.2.1 w (out w (hl w hw)))
  have ka := keep as (fun w hw => by simp [hw])
  have kb := keep bs (fun w hw => by simp [hw])
  have ks := keep ss (fun w hw => by simp [hw])
  have kc := keep carry (fun w hw => by simp [hw])
  have r := sharedAdd_correct h as bs ss dst carry q cin hh hal hbl hsl hdl hcl hn u g
    (by rw [ks,ka,kb]; exact hv)
    ((dec'.2.1 q (out q (by simp))).trans hq0)
    ((dec'.2.1 cin (out cin (by simp))).trans hi0) (kc.trans hc0)
  rw [ka,kb] at r
  have total := dec'.seq r
  have total' : Update dst (((2^h : Nat) : Int)*(sharedWord h (regValue as s.basis) (regValue bs s.basis)+1)-
      (2^(2*h-1) : Nat)) s
      (run (loadedAdd (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
        (correctionBits h ss q) dst (carry.take (h+1)) h) g u) := by
    convert total using 1 <;> ring
  simpa only [correctionBack,run_append,P,f,g,u] using total'

theorem loaded_counts (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat)
    (hl : bits.length=(dst.drop k).length) (hc : carry.length+1=(dst.drop k).length) :
    toffoliCount (loadedSub a b c q cin bits dst carry k)=(dst.drop k).length-1 ∧
    measurementCount (loadedSub a b c q cin bits dst carry k)=(dst.drop k).length-1 ∧
    toffoliCount (loadedAdd a b c q cin bits dst carry k)=(dst.drop k).length-1 ∧
    measurementCount (loadedAdd a b c q cin bits dst carry k)=(dst.drop k).length-1 := by
  have sub := mappedSub_counts bits (dst.drop k) carry cin hl hc
  have add := mappedAdd_counts bits (dst.drop k) carry cin hl hc
  simp only [loadedSub,loadedAdd,toffoliCount_append,measurementCount_append,
    show toffoliCount (load a b c q cin)=0 from rfl,
    show toffoliCount (unload a b c q cin)=0 from rfl,
    show measurementCount (load a b c q cin)=0 from rfl,
    show measurementCount (unload a b c q cin)=0 from rfl,
    sub.1,sub.2,add.1,add.2,Nat.zero_add,Nat.add_zero,and_self]

theorem correction_counts (h : Nat) (as bs ss dst carry : List Wire) (q cin : Wire)
    (hh : 2≤h) (hsl : ss.length=h+1) (hdl : dst.length=2*h+2) (hcl : h+1≤carry.length) :
    toffoliCount (correction h as bs ss dst carry q cin)=h+3 ∧
    measurementCount (correction h as bs ss dst carry q cin)=h+3 ∧
    toffoliCount (correctionBack h as bs ss dst carry q cin)=h+3 ∧
    measurementCount (correctionBack h as bs ss dst carry q cin)=h+3 := by
  have b := loaded_counts (as.getD (h-1) 0) (bs.getD (h-1) 0) (ss.getD (h-1) 0) q cin
    (correctionBits h ss q) dst (carry.take (h+1)) h
    (by rw [correctionBits_length h ss q (by omega) (by omega),List.length_drop,hdl]; omega)
    (by simp only [List.length_take,List.length_drop]; omega)
  have a := mappedAdd_counts (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin
    (by rw [mappedConstant_length,List.length_drop,hdl]; omega)
    (by simp only [List.length_take,List.length_drop]; omega)
  have c := mappedSub_counts (mappedConstant none 3 1) (dst.drop (2*h-1)) (carry.take 2) cin
    (by rw [mappedConstant_length,List.length_drop,hdl]; omega)
    (by simp only [List.length_take,List.length_drop]; omega)
  simp only [correction,correctionBack,toffoliCount_append,measurementCount_append,
    b.1,b.2.1,b.2.2.1,b.2.2.2,a.1,a.2,c.1,c.2,List.length_drop,hdl]
  omega


theorem plain_sub_update (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hl : xs.length=dst.length) (hc : carry.length+1=dst.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) (hi : s.basis cin=false) :
    Update dst (-(regValue xs s.basis : Int)) s (run (subInPlace xs dst carry cin) m s) := by
  have r := BalancedInverse.subInPlace_any_correct xs dst carry cin hn hl hc s m hclean
  have vl := regValue_lt xs s.basis
  rw [hl] at vl
  refine ⟨r.1,r.2.1,?_⟩
  rw [r.2.2,hi,Bool.toNat_false,Nat.sub_zero]
  simpa only [sub_eq_add_neg] using sub_congr (regValue dst s.basis) (2^dst.length)
    (regValue xs s.basis) (by omega)

theorem plain_add_update (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hl : xs.length=dst.length) (hc : carry.length+1=dst.length)
    (s : State) (m : List Bool) (hclean : ∀q∈carry,s.basis q=false) (hi : s.basis cin=false) :
    Update dst (regValue xs s.basis : Int) s (run (addInPlace xs dst carry cin) m s) := by
  have r := addInPlace_correct xs dst carry cin hn hl hc s m hclean
  refine ⟨r.1,r.2.1,?_⟩
  rw [r.2.2,hi,Bool.toNat_false,Nat.add_zero]
  simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
  rw [Int.add_comm]
  exact Int.emod_emod _ _

theorem diag_sub_update (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length) (hd : dst.length=2*xs.length)
    (hc : dst.length-1≤carry.length) (s : State) (m : List Bool)
    (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    Update dst (-(signedDiagValue (regValue xs s.basis) xs.length : Int)) s
      (run (mappedDiagSub xs dst carry cin) m s) := by
  have r := mappedDiagSub_correct cin xs dst carry hn hx hd hc s m hclean hi
  have vl : signedDiagValue (regValue xs s.basis) xs.length<2^dst.length := by
    rw [←mappedDiagonal_exact xs s.basis hx]
    simpa only [mappedDiagonal_length xs hx,hd] using mappedValue_lt (mappedDiagonal xs) s.basis
  refine ⟨r.1,r.2.2,?_⟩
  rw [r.2.1]
  simpa only [sub_eq_add_neg] using sub_congr (regValue dst s.basis) (2^dst.length)
    (signedDiagValue (regValue xs s.basis) xs.length) (by omega)

theorem diag_add_update (xs dst carry : List Wire) (cin : Wire)
    (hn : (cin::xs++dst++carry).Nodup) (hx : 0<xs.length) (hd : dst.length=2*xs.length)
    (hc : dst.length-1≤carry.length) (s : State) (m : List Bool)
    (hclean : regValue carry s.basis=0) (hi : s.basis cin=false) :
    Update dst (signedDiagValue (regValue xs s.basis) xs.length : Int) s
      (run (mappedDiagAdd xs dst carry cin) m s) := by
  have r := mappedDiagAdd_correct cin xs dst carry hn hx hd hc s m hclean hi
  refine ⟨r.1,r.2.2,?_⟩
  rw [r.2.1]
  simp only [Int.ModEq,Int.natCast_mod,Int.natCast_add]
  exact Int.emod_emod _ _

end ECDSAAdd.Entrant.DiagSq
end DiagonalSharing
section DiagonalRegisterIntegration
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

def reg (R : KRegs) (i : Fin 4) : List Wire := ![R.dlo,R.dhi,R.S,R.T] i
def vec (a b s t : Int) : Fin 4 → Int := ![a,b,s,t]

theorem vec0 (a b s t x : Int) : Function.update (vec a b s t) 0 x=vec x b s t := by
  funext i; fin_cases i <;> simp [vec,Function.update]
theorem vec1 (a b s t x : Int) : Function.update (vec a b s t) 1 x=vec a x s t := by
  funext i; fin_cases i <;> simp [vec,Function.update]
theorem vec2 (a b s t x : Int) : Function.update (vec a b s t) 2 x=vec a b x t := by
  funext i; fin_cases i <;> simp [vec,Function.update]
theorem vec3 (a b s t x : Int) : Function.update (vec a b s t) 3 x=vec a b s x := by
  funext i; fin_cases i <;> simp [vec,Function.update]

theorem reg_disjoint (R : KRegs) (hn : R.all.Nodup) (i j : Fin 4) (hij : i≠j)
    (q : Wire) (hq : q∈reg R i) : q∉reg R j := by
  fin_cases i <;> fin_cases j <;> simp [reg] at *
  all_goals exact kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq

theorem reg_member (R : KRegs) (i : Fin 4) (q : Wire) (hq : q∈reg R i) :
    q∈R.dst ∨ q∈R.S ∨ q∈R.T := by
  fin_cases i
  · exact Or.inl (List.mem_of_mem_take hq)
  · exact Or.inl (List.mem_of_mem_drop hq)
  · exact Or.inr (Or.inl hq)
  · exact Or.inr (Or.inr hq)

structure Shape (R : KRegs) (base s : State) (v : Fin 4 → Int) : Prop where
  phase : s.phase=base.phase
  value : ∀i,(regValue (reg R i) s.basis : Int) ≡ v i [ZMOD (2^(reg R i).length : Nat)]
  rest : ∀q,q∉R.dst → q∉R.S → q∉R.T → s.basis q=base.basis q

theorem Shape.step {R : KRegs} (hn : R.all.Nodup) {base s t : State} {v : Fin 4 → Int}
    (h : Shape R base s v) (i : Fin 4) (x : Int)
    (hp : t.phase=s.phase) (hf : ∀q,q∉reg R i → t.basis q=s.basis q)
    (hv : (regValue (reg R i) t.basis : Int) ≡ x [ZMOD (2^(reg R i).length : Nat)]) :
    Shape R base t (Function.update v i x) := by
  refine ⟨hp.trans h.phase,?_,?_⟩
  · intro j
    by_cases ji : j=i
    · subst j; simpa using hv
    · rw [Function.update_of_ne ji,kkeep hf (reg_disjoint R hn j i ji)]
      exact h.value j
  · intro q hd hs ht
    have qi : q∉reg R i := by
      intro bad
      rcases reg_member R i q bad with bad|bad|bad
      · exact hd bad
      · exact hs bad
      · exact ht bad
    exact (hf q qi).trans (h.rest q hd hs ht)

theorem Shape.advance {R : KRegs} (hn : R.all.Nodup) {base s t : State} {v : Fin 4 → Int}
    (h : Shape R base s v) (i : Fin 4) (d : Int) (u : Update (reg R i) d s t) :
    Shape R base t (Function.update v i (v i+d)) := by
  apply h.step hn i (v i+d) u.1 u.2.1
  exact u.2.2.trans ((h.value i).add_right d)

theorem Shape.exact {R : KRegs} {base s : State} {v : Fin 4 → Int} (h : Shape R base s v)
    (i : Fin 4) (x : Nat) (hv : v i=x) (hx : x<2^(reg R i).length) :
    regValue (reg R i) s.basis=x := by
  have r := h.value i
  rw [hv] at r
  have r' := Int.natCast_modEq_iff.mp r
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt (regValue_lt (reg R i) s.basis),Nat.mod_eq_of_lt hx] using r'

theorem Shape.keep {R : KRegs} (hn : R.all.Nodup) {base s : State} {v : Fin 4 → Int}
    (h : Shape R base s v) (l : List Wire)
    (hl : ∀q∈l,q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) :
    regValue l s.basis=regValue l base.basis := by
  apply regValue_congr
  intro q hq
  have o := R.outside hn q (hl q hq)
  exact h.rest q o.1 o.2.1 o.2.2

theorem Shape.cin {R : KRegs} (hn : R.all.Nodup) {base s : State} {v : Fin 4 → Int}
    (h : Shape R base s v) : s.basis R.cin=base.basis R.cin :=
  h.rest R.cin (R.outside hn R.cin (by simp)).1 (R.outside hn R.cin (by simp)).2.1
    (R.outside hn R.cin (by simp)).2.2

def Transition (R : KRegs) (base : State) (v w : Fin 4 → Int) (P : Program) : Prop :=
  ∀s m,Shape R base s v → Shape R base (run P m s) w

theorem Transition.seq {R : KRegs} {base : State} {v w z : Fin 4 → Int} {P Q : Program}
    (hp : Transition R base v w P) (hq : Transition R base w z Q) : Transition R base v z (P++Q) := by
  intro s m hs
  rw [run_append]
  exact hq _ _ (hp _ _ hs)


def rawValue (n x : Nat) : Nat := x^2+signedDiagValue x n

def seeds (R : KRegs) : Program :=
  rawMakeT R.lo R.dlo R.pad R.carry ++ rawMakeT R.hi R.dhi R.pad R.carry ++ R.smk ++
    rawMakeT R.S R.T R.pad R.carry

theorem seeds_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (seeds R) m s)
      (vec (rawValue R.h (regValue R.lo s.basis)) (rawValue R.h (regValue R.hi s.basis))
        (regValue R.lo s.basis+regValue R.hi s.basis)
        (rawValue (R.h+1) (regValue R.lo s.basis+regValue R.hi s.basis))) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hpl := w.pad
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have init : Shape R s s (vec 0 0 0 0) := by
    refine ⟨rfl,?_,fun _ _ _ _ => rfl⟩
    intro i; fin_cases i
    · change (regValue R.dlo s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dlo) hd0 (fun q h => List.mem_of_mem_take h)]; rfl
    · change (regValue R.dhi s.basis : Int) ≡ 0 [ZMOD _]
      rw [KRegs.xz (r:=R.dhi) hd0 (fun q h => List.mem_of_mem_drop h)]; rfl
    · change (regValue R.S s.basis : Int) ≡ 0 [ZMOD _]
      rw [hS0]; rfl
    · change (regValue R.T s.basis : Int) ≡ 0 [ZMOD _]
      rw [hT0]; rfl
  have loStep : Transition R s (vec 0 0 0 0) (vec (rawValue R.h a) 0 0 0)
      (rawMakeT R.lo R.dlo R.pad R.carry) := by
    intro t rec ht
    have lt := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have r := rawMakeT_correct R.lo R.dlo R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 0 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 0) (run (rawMakeT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h a : Nat) [ZMOD (2^(reg R 0).length : Nat)] := by
      change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,lt,L0]; rfl
    simpa only [vec0] using ht.step hn 0 (rawValue R.h a) r.1 r.2.2 v
  have hiStep : Transition R s (vec (rawValue R.h a) 0 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) 0 0) (rawMakeT R.hi R.dhi R.pad R.carry) := by
    intro t rec ht
    have ht0 := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := rawMakeT_correct R.hi R.dhi R.pad R.carry
      (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
      (by omega) (by omega) hpl (by omega) t rec
      (ht.exact 1 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 1) (run (rawMakeT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡
        (rawValue R.h b : Nat) [ZMOD (2^(reg R 1).length : Nat)] := by
      change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,ht0,hhi]; rfl
    simpa only [vec1] using ht.step hn 1 (rawValue R.h b) r.1 r.2.2 v
  have sumStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) 0 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0) R.smk := by
    intro t rec ht
    have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
    have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
    have r := R.smk_correct w hn t rec (ht.exact 2 0 rfl (by norm_num))
      ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
    have v : (regValue (reg R 2) (run R.smk rec t).basis : Int) ≡ (a+b : Nat) [ZMOD (2^(reg R 2).length : Nat)] := by
      change (regValue R.S _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,al,bl]
    simpa only [vec2] using ht.step hn 2 (a+b : Nat) r.1 r.2.2 v
  have sqStep : Transition R s (vec (rawValue R.h a) (rawValue R.h b) (a+b) 0)
      (vec (rawValue R.h a) (rawValue R.h b) (a+b) (rawValue (R.h+1) (a+b)))
      (rawMakeT R.S R.T R.pad R.carry) := by
    intro t rec ht
    have av := regValue_lt R.lo s.basis
    have bv := regValue_lt R.hi s.basis
    rw [L0] at av; rw [hhi] at bv
    have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
    have sv := ht.exact 2 (a+b) rfl slt
    change regValue R.S t.basis=a+b at sv
    have r := rawMakeT_correct R.S R.T R.pad R.carry
      (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
      (by omega) hTl hpl (by omega) t rec
      (ht.exact 3 0 rfl (by norm_num))
      ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
      ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
    have v : (regValue (reg R 3) (run (rawMakeT R.S R.T R.pad R.carry) rec t).basis : Int) ≡
        (rawValue (R.h+1) (a+b) : Nat) [ZMOD (2^(reg R 3).length : Nat)] := by
      change (regValue R.T _ : Int) ≡ _ [ZMOD _]
      rw [r.2.1,sv,hSS]; rfl
    simpa only [vec3] using ht.step hn 3 (rawValue (R.h+1) (a+b)) r.1 r.2.2 v
  exact (((loStep.seq hiStep).seq sumStep).seq sqStep) s m init


theorem rawValue_bound (l : List Wire) (s : BasisState) (hl : 1≤l.length) :
    rawValue l.length (regValue l s)<2^(2*l.length) := by
  rw [rawValue,←signedRawValue_correct l s (List.ne_nil_of_length_pos (by omega))]
  exact signedRawValue_bound l s hl

theorem sublo_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) :
    Transition R base (vec A B S T) (vec A B S (T-A)) R.m6 := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := plain_sub_update (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t rec
    (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h)) ((ht.cin hn).trans hi0)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem addlo_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : A<2^R.dlo.length) :
    Transition R base (vec A B S T) (vec A B S (T+A)) R.c6 := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 0 A rfl hX
  change regValue R.dlo t.basis=A at xv
  have zv := (ht.keep hn R.zA (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zA) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := plain_add_update (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t rec
    (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h)) ((ht.cin hn).trans hi0)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((A : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem subhi_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) :
    Transition R base (vec A B S T) (vec A B S (T-B)) R.m7 := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := plain_sub_update (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t rec
    (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h)) ((ht.cin hn).trans hi0)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 (-(B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem addhi_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S : Nat) (T : Int) (hX : B<2^R.dhi.length) :
    Transition R base (vec A B S T) (vec A B S (T+B)) R.c7 := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hSl := w.S; have hTl := w.T; have hcl := w.carry; have h4 := w.h4; have hh := w.hh; have h5 := w.h5
  have xv := ht.exact 1 B rfl hX
  change regValue R.dhi t.basis=B at xv
  have zv := (ht.keep hn R.zB (fun q h => Or.inr (Or.inl (List.mem_of_mem_take h)))).trans
    (KRegs.xz (r:=R.zB) hz0 (fun q h => List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := plain_add_update (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) t rec
    (fun q h => (regValue_zero _ _).mp cv q (List.mem_of_mem_take h)) ((ht.cin hn).trans hi0)
  rw [regValue_append,xv,zv,Nat.mul_zero,Nat.add_zero] at r
  have act := ht.advance hn 3 ((B : Int)) r
  simpa only [show (vec A B S T) 3=T from rfl,vec3,sub_eq_add_neg] using act

theorem diagsublo_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) : Transition R base (vec A B S T) (vec (A-(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (mappedDiagSub R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have hlen : R.lo.length=R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := diag_sub_update R.lo R.dlo R.carry R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) t rec cv ((ht.cin hn).trans hi0)
  rw [xv,hlen] at r
  have act := ht.advance hn 0 (-(signedDiagValue (regValue R.lo base.basis) R.h : Int)) r
  simpa only [show (vec A B S T) 0=A from rfl,vec0,sub_eq_add_neg] using act

theorem diagaddlo_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) : Transition R base (vec A B S T) (vec (A+(signedDiagValue (regValue R.lo base.basis) R.h : Nat)) B S T)
      (mappedDiagAdd R.lo R.dlo R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have hlen : R.lo.length=R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := diag_add_update R.lo R.dlo R.carry R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) t rec cv ((ht.cin hn).trans hi0)
  rw [xv,hlen] at r
  have act := ht.advance hn 0 ((signedDiagValue (regValue R.lo base.basis) R.h : Int)) r
  simpa only [show (vec A B S T) 0=A from rfl,vec0,sub_eq_add_neg] using act

theorem diagsubhi_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) : Transition R base (vec A B S T) (vec A (B-(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (mappedDiagSub R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have hlen : R.hi.length=R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := diag_sub_update R.hi R.dhi R.carry R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) t rec cv ((ht.cin hn).trans hi0)
  rw [xv,hlen] at r
  have act := ht.advance hn 1 (-(signedDiagValue (regValue R.hi base.basis) R.h : Int)) r
  simpa only [show (vec A B S T) 1=B from rfl,vec1,sub_eq_add_neg] using act

theorem diagaddhi_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false)
    (A B S T : Int) : Transition R base (vec A B S T) (vec A (B+(signedDiagValue (regValue R.hi base.basis) R.h : Nat)) S T)
      (mappedDiagAdd R.hi R.dhi R.carry R.cin) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry
  have hlen : R.hi.length=R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have r := diag_add_update R.hi R.dhi R.carry R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) (by omega) t rec cv ((ht.cin hn).trans hi0)
  rw [xv,hlen] at r
  have act := ht.advance hn 1 ((signedDiagValue (regValue R.hi base.basis) R.h : Int)) r
  simpa only [show (vec A B S T) 1=B from rfl,vec1,sub_eq_add_neg] using act

def parity (R : KRegs) : Wire := R.z.getD 0 0

def corr (R : KRegs) : Program := correction R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
def corrBack (R : KRegs) : Program := correctionBack R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin

theorem corr_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T-((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)+(2^(2*R.h-1) : Nat))) (corr R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have r := correction_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring

theorem corrBack_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (base : State) (hz0 : regValue R.z base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) (T+((2^R.h : Nat) : Int)*(sharedWord R.h (regValue R.lo base.basis) (regValue R.hi base.basis)+1)-(2^(2*R.h-1) : Nat))) (corrBack R) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hzl := w.z
  have hhi : R.hi.length=R.h := by omega
  have hs : R.S.length=R.h+1 := by omega
  have qm : parity R∈R.z := getD_in R.z 0 (by omega)
  have qsub : List.Sublist [parity R] R.z := List.singleton_sublist.mpr qm
  have cn : (R.cin::parity R::R.lo++R.hi++R.S++R.T++R.carry).Nodup := knd hn (fun q => by
    have c := R.counts q; have z := qsub.count_le q
    simp only [KRegs.all,List.count_cons,List.count_append,List.count_nil] at c z ⊢; omega)
  have av := regValue_lt R.lo base.basis
  have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hhi] at bv
  have slt : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [hs,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) slt
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have cv := (ht.keep hn R.carry (by intro q h; simp [h])).trans hc0
  have zv := (ht.keep hn R.z (by intro q h; simp [h])).trans hz0
  have r := correctionBack_correct R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    hh L0 hhi hs (by omega) (by omega) cn t rec (by rw [sv,al,bl])
    ((regValue_zero _ _).mp zv _ qm) ((ht.cin hn).trans hi0) cv
  rw [al,bl] at r
  have act := ht.advance hn 3 _ r
  convert act using 1 <;> simp only [vec3]
  congr 1
  change _=T+_
  ring


def headBlock (R : KRegs) : Program := seeds R ++ (R.m6++R.m7++corr R++
  mappedDiagSub R.lo R.dlo R.carry R.cin++mappedDiagSub R.hi R.dhi R.carry R.cin)

def make (R : KRegs) : Program := headBlock R++R.m8

def clear (R : KRegs) : Program := R.c8++(mappedDiagAdd R.lo R.dlo R.carry R.cin++
  mappedDiagAdd R.hi R.dhi R.carry R.cin++corrBack R++R.c7++R.c6++
  rawClearT R.S R.T R.pad R.carry++R.scl++rawClearT R.hi R.dhi R.pad R.carry++
  rawClearT R.lo R.dlo R.pad R.carry)

theorem prefix_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run (headBlock R) m s)
      (vec ((regValue R.lo s.basis)^2) ((regValue R.hi s.basis)^2)
        (regValue R.lo s.basis+regValue R.hi s.basis) (2*regValue R.lo s.basis*regValue R.hi s.basis)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4
  have hhi : R.hi.length=R.h := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have st1 := sublo_transition R w hn s hz0 hc0 hi0 A B S Z hA
  have st2 := subhi_transition R w hn s hz0 hc0 hi0 A B S ((Z : Int)-A) hB
  have st3 := corr_transition R w he hh hn s hz0 hc0 hi0 A B ((Z : Int)-A-B)
  have norm := cross_normalize R.h a b hh alo bhi
  change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
    (2*a*b : Nat) at norm
  rw [norm] at st3
  have st4 := diagsublo_transition R w he hn s hc0 hi0 A B S (2*a*b : Nat)
  have st4' : Transition R s (vec A B S (2*a*b : Nat)) (vec (a^2 : Nat) B S (2*a*b : Nat))
      (mappedDiagSub R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add,add_sub_cancel_right] using st4
  have st5 := diagsubhi_transition R w he hn s hc0 hi0 (a^2 : Nat) B S (2*a*b : Nat)
  have st5' : Transition R s (vec (a^2 : Nat) B S (2*a*b : Nat))
      (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (mappedDiagSub R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add,add_sub_cancel_right] using st5
  have tail := (((st1.seq st2).seq st3).seq st4').seq st5'
  have initial := seeds_shape R w he hn s (m.take (measurementCount (seeds R))) hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have result := tail _ (m.drop (measurementCount (seeds R))) initial
  simpa only [headBlock,run_append,A,B,S,Z,a,b,Int.natCast_mul,Int.natCast_add,Int.natCast_pow] using result


theorem make_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=0)
    (hS0 : regValue R.S s.basis=0) (hT0 : regValue R.T s.basis=0)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (make R) m s).phase=s.phase ∧
    regValue R.dst (run (make R) m s).basis=(regValue R.bank s.basis)^2 ∧
    regValue R.S (run (make R) m s).basis=regValue R.lo s.basis+regValue R.hi s.basis ∧
    regValue R.T (run (make R) m s).basis=2*regValue R.lo s.basis*regValue R.hi s.basis ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (make R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let f := m.take (measurementCount (headBlock R))
  let g := m.drop (measurementCount (headBlock R))
  let u := run (headBlock R) f s
  have h := prefix_shape R w he hh hn s f hd0 hS0 hT0 hz0 hp0 hc0 hi0
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have slt : a+b<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [a,b]; omega
  have ex : (a+b)^2=a^2+2*a*b+b^2 := by ring
  have sq := square_bound (a+b) R.S.length slt
  have tvlt : 2*a*b<2^R.T.length := by rw [hTl]; omega
  have av : regValue R.dlo u.basis=a^2 := h.exact 0 (a^2) (by simp [vec,a,b])
    (by change a^2<2^R.dlo.length; rw [L2]; exact square_bound _ _ al)
  have bv : regValue R.dhi u.basis=b^2 := h.exact 1 (b^2) (by simp [vec,a,b])
    (by change b^2<2^R.dhi.length; rw [L3,show R.bank.length-R.h=R.h by omega]; exact square_bound _ _ bl)
  have sv : regValue R.S u.basis=a+b := h.exact 2 (a+b) (by simp [vec,a,b]) slt
  have tv : regValue R.T u.basis=2*a*b := h.exact 3 (2*a*b) (by simp [vec,a,b]) tvlt
  have dv : regValue R.dst u.basis=a^2+2^(2*R.h)*b^2 := by rw [R.dst_value w,av,bv]
  have cv := (h.keep hn R.carry (by intro q hq; simp [hq])).trans hc0
  have zv := (h.keep hn R.zM (fun q hq => Or.inr (Or.inl (List.mem_of_mem_take hq)))).trans
    (KRegs.xz (r:=R.zM) hz0 (fun q hq => List.mem_of_mem_take hq))
  have ni : (R.cin::(R.T++R.zM)++R.dmid++R.carry.take (R.dmid.length-1)).Nodup :=
    knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega)
  have r := addInPlace_correct (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin ni
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) u g
    (fun q hq => (regValue_zero _ _).mp cv q (List.mem_of_mem_take hq))
  have rv : regValue R.dmid (run R.m8 g u).basis=
      (2*a*b+(a^2+2^(2*R.h)*b^2)/2^R.h)%2^(2*R.bank.length-R.h) := by
    rw [show R.m8=addInPlace (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin from rfl,
      r.2.2,regValue_append,tv,zv,h.cin hn,hi0,
      show regValue R.dmid u.basis=regValue R.dst u.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by have := w.dst; omega) u.basis,dv,L4]
    simp
  have frame : ∀q,q∉R.dmid → (run R.m8 g u).basis q=u.basis q := r.2.1
  have keepLow : regValue (R.dst.take R.h) (run R.m8 g u).basis=regValue (R.dst.take R.h) u.basis :=
    kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have dfin : regValue R.dst (run R.m8 g u).basis=(regValue R.bank s.basis)^2 := by
    rw [R.bank_value w s.basis,R.dst_value_mid w,rv,keepLow,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by have := w.dst; omega),dv]
    exact KRegs.kfinal a b R.h R.bank.length al (by simpa only [show R.bank.length-R.h=R.h by omega] using bl) (by omega)
  have result : (run R.m8 g u).phase=s.phase ∧ regValue R.dst (run R.m8 g u).basis=(regValue R.bank s.basis)^2 ∧
      regValue R.S (run R.m8 g u).basis=a+b ∧ regValue R.T (run R.m8 g u).basis=2*a*b ∧
      ∀q,q∉R.dst → q∉R.S → q∉R.T → (run R.m8 g u).basis q=s.basis q := by
    refine ⟨r.1.trans h.phase,dfin,?_,?_,?_⟩
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans sv
    · exact (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans tv
    · intro q hd hs ht
      exact (frame q (fun bad => hd (List.mem_of_mem_drop bad))).trans (h.rest q hd hs ht)
  simpa only [make,run_append,u,f,g,a,b] using result

theorem rawclearlo_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (B S T : Int) :
    Transition R base (vec (rawValue R.h (regValue R.lo base.basis)) B S T) (vec 0 B S T) (rawClearT R.lo R.dlo R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.lo.length=R.h := by omega
  have hdlen : R.dlo.length=2*R.h := by omega
  have xv := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have rb := rawValue_bound R.lo base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 0 (rawValue R.h (regValue R.lo base.basis)) rfl
    (by change _<2^R.dlo.length; rw [hdlen]; exact rb)
  change regValue R.dlo t.basis=_ at dv
  have r := rawClearT_correct R.lo R.dlo R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 0) (run (rawClearT R.lo R.dlo R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 0).length : Nat)] := by
    change (regValue R.dlo _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec0] using ht.step hn 0 0 r.1 r.2.2 val

theorem rawclearhi_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h)
    (hn : R.all.Nodup) (base : State) (hp0 : regValue R.pad base.basis=0)
    (hc0 : regValue R.carry base.basis=0) (A S T : Int) :
    Transition R base (vec A (rawValue R.h (regValue R.hi base.basis)) S T) (vec A 0 S T) (rawClearT R.hi R.dhi R.pad R.carry) := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hcl := w.carry; have hpl := w.pad
  have hlen : R.hi.length=R.h := by omega
  have hdlen : R.dhi.length=2*R.h := by omega
  have xv := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have rb := rawValue_bound R.hi base.basis (by omega)
  rw [hlen] at rb
  have dv := ht.exact 1 (rawValue R.h (regValue R.hi base.basis)) rfl
    (by change _<2^R.dhi.length; rw [hdlen]; exact rb)
  change regValue R.dhi t.basis=_ at dv
  have r := rawClearT_correct R.hi R.dhi R.pad R.carry
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by omega) (by omega) hpl (by omega) t rec (by rw [xv,hlen]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 1) (run (rawClearT R.hi R.dhi R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 1).length : Nat)] := by
    change (regValue R.dhi _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec1] using ht.step hn 1 0 r.1 r.2.2 val

theorem rawclearSum_transition (R : KRegs) (w : R.W) (hn : R.all.Nodup) (base : State)
    (hp0 : regValue R.pad base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (A B : Int) (S : Nat) (hS : S<2^R.S.length) :
    Transition R base (vec A B S (rawValue R.S.length S)) (vec A B S 0)
      (rawClearT R.S R.T R.pad R.carry) := by
  intro t rec ht
  have h4 := w.h4; have hh := w.hh; have hsl := w.S; have htl := w.T; have hcl := w.carry; have hpl := w.pad
  have sv := ht.exact 2 S rfl hS
  change regValue R.S t.basis=S at sv
  have rb := rawValue_bound R.S t.basis (by omega)
  rw [sv] at rb
  have dv := ht.exact 3 (rawValue R.S.length S) rfl (by change _<2^R.T.length; rw [htl]; exact rb)
  change regValue R.T t.basis=_ at dv
  have r := rawClearT_correct R.S R.T R.pad R.carry
    (knd hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega))
    (by omega) htl hpl (by omega) t rec (by rw [sv]; exact dv)
    ((ht.keep hn R.pad (by intro q h; simp [h])).trans hp0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0)
  have val : (regValue (reg R 3) (run (rawClearT R.S R.T R.pad R.carry) rec t).basis : Int) ≡ 0
      [ZMOD (2^(reg R 3).length : Nat)] := by
    change (regValue R.T _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec3] using ht.step hn 3 0 r.1 r.2.2 val

theorem clearSum_transition (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (base : State) (hz0 : regValue R.z base.basis=0) (hc0 : regValue R.carry base.basis=0)
    (hi0 : base.basis R.cin=false) (A B T : Int) :
    Transition R base (vec A B (regValue R.lo base.basis+regValue R.hi base.basis) T)
      (vec A B 0 T) R.scl := by
  intro t rec ht
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have hs := w.S
  have hl : R.hi.length=R.h := by omega
  have av := regValue_lt R.lo base.basis; have bv := regValue_lt R.hi base.basis
  rw [L0] at av; rw [hl] at bv
  have hS : regValue R.lo base.basis+regValue R.hi base.basis<2^R.S.length := by
    rw [show R.S.length=R.h+1 by omega,pow_succ]; omega
  have sv := ht.exact 2 (regValue R.lo base.basis+regValue R.hi base.basis) (by simp [vec]) hS
  change regValue R.S t.basis=_ at sv
  have al := ht.keep hn R.lo (fun q h => Or.inl (List.mem_of_mem_take h))
  have bl := ht.keep hn R.hi (fun q h => Or.inl (List.mem_of_mem_drop h))
  have r := R.scl_correct w hn t rec (by rw [sv,al,bl])
    ((ht.keep hn R.z (by intro q h; simp [h])).trans hz0)
    ((ht.keep hn R.carry (by intro q h; simp [h])).trans hc0) ((ht.cin hn).trans hi0)
  have val : (regValue (reg R 2) (run R.scl rec t).basis : Int) ≡ 0 [ZMOD (2^(reg R 2).length : Nat)] := by
    change (regValue R.S _ : Int) ≡ 0 [ZMOD _]
    rw [r.2.1]; rfl
  simpa only [vec2] using ht.step hn 2 0 r.1 r.2.2 val


theorem clear_start_shape (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hn : R.all.Nodup)
    (s : State) (m : List Bool) (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    Shape R s (run R.c8 m s) (vec ((regValue R.lo s.basis)^2 : Nat) ((regValue R.hi s.basis)^2 : Nat)
      (regValue R.lo s.basis+regValue R.hi s.basis : Nat) (2*regValue R.lo s.basis*regValue R.hi s.basis : Nat)) := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry; have hdl := w.dst
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  have al : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bl : b<2^(R.bank.length-R.h) := by simpa only [L1] using regValue_lt R.hi s.basis
  have av : a^2<2^(2*R.h) := square_bound _ _ al
  have hd : regValue R.dst s.basis=(a+2^R.h*b)^2 := by
    simpa only [R.bank_value w s.basis] using hd0
  have XLt : (a+2^R.h*b)^2<2^(2*R.bank.length) := by
    rw [←R.bank_value w s.basis]
    exact square_bound _ _ (regValue_lt R.bank s.basis)
  have hX : (a+2^R.h*b)^2=(a^2+2^(2*R.h)*b^2)+2^R.h*(2*a*b) := by ring
  have hdiv : (a+2^R.h*b)^2/2^R.h=(a^2+2^(2*R.h)*b^2)/2^R.h+2*a*b := by
    rw [hX,Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  have hmod : (a+2^R.h*b)^2%2^R.h=(a^2+2^(2*R.h)*b^2)%2^R.h := by
    rw [hX,Nat.add_mul_mod_self_left]
  have hq : (a+2^R.h*b)^2/2^R.h<2^(2*R.bank.length-R.h) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _),←pow_add,
      show 2*R.bank.length-R.h+R.h=2*R.bank.length by omega]
    exact XLt
  have r := BalancedInverse.subInPlace_any_correct (R.T++R.zM) R.dmid
    (R.carry.take (R.dmid.length-1)) R.cin
    (knd hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega))
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega) s m
    (fun q hq => (regValue_zero _ _).mp hc0 q (List.mem_of_mem_take hq))
  have frame : ∀q,q∉R.dmid → (run R.c8 m s).basis q=s.basis q := r.2.1
  have low : regValue (R.dst.take R.h) (run R.c8 m s).basis=regValue (R.dst.take R.h) s.basis := kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)
  have zm : regValue R.zM s.basis=0 := KRegs.xz hz0 (fun q h => List.mem_of_mem_take h)
  have dv : regValue R.dst (run R.c8 m s).basis=a^2+2^(2*R.h)*b^2 := by
    rw [R.dst_value_mid w,show regValue R.dmid (run R.c8 m s).basis=
        regValue R.dmid (run (subInPlace (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin) m s).basis from rfl,
      r.2.2,low,regValue_append,hT0,zm,hi0,
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst R.h (by omega),
      show regValue R.dmid s.basis=regValue R.dst s.basis/2^R.h from
        CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst R.h (by omega) s.basis,hd,L4]
    simp only [Nat.mul_zero,Nat.add_zero,Bool.toNat_false,Nat.sub_zero]
    rw [ksubmod _ _ _ (by rw [hdiv]; exact Nat.le_add_left _ _) hq,hdiv,hmod,Nat.add_sub_cancel,Nat.mod_add_div]
  have dlo : regValue R.dlo (run R.c8 m s).basis=a^2 := by
    rw [show regValue R.dlo (run R.c8 m s).basis=regValue R.dst (run R.c8 m s).basis%2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_take_mod R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt av]
  have dhi : regValue R.dhi (run R.c8 m s).basis=b^2 := by
    rw [show regValue R.dhi (run R.c8 m s).basis=regValue R.dst (run R.c8 m s).basis/2^(2*R.h) from
      CuccaroStreamedSquareWideLayout.regValue_drop_div R.dst (2*R.h) (by omega) _,dv,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt av,Nat.zero_add]
  have sv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hS0
  have tv := (kkeep frame (fun q hq => kdis hn (fun q => by have c := R.counts q; simp only [KRegs.all,List.count_cons,List.count_append] at c ⊢; omega) q hq)).trans hT0
  refine ⟨r.1,?_,fun q hd _ _ => frame q (fun bad => hd (List.mem_of_mem_drop bad))⟩
  intro i; fin_cases i
  · change (regValue R.dlo _ : Int) ≡ _ [ZMOD _]
    rw [dlo]; exact Int.ModEq.rfl
  · change (regValue R.dhi _ : Int) ≡ _ [ZMOD _]
    rw [dhi]; exact Int.ModEq.rfl
  · change (regValue R.S _ : Int) ≡ _ [ZMOD _]
    rw [sv]; exact Int.ModEq.rfl
  · change (regValue R.T _ : Int) ≡ _ [ZMOD _]
    rw [tv]; exact Int.ModEq.rfl


theorem clear_correct (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33)
    (hn : R.all.Nodup) (s : State) (m : List Bool)
    (hd0 : regValue R.dst s.basis=(regValue R.bank s.basis)^2)
    (hS0 : regValue R.S s.basis=regValue R.lo s.basis+regValue R.hi s.basis)
    (hT0 : regValue R.T s.basis=2*regValue R.lo s.basis*regValue R.hi s.basis)
    (hz0 : regValue R.z s.basis=0) (hp0 : regValue R.pad s.basis=0)
    (hc0 : regValue R.carry s.basis=0) (hi0 : s.basis R.cin=false) :
    (run (clear R) m s).phase=s.phase ∧
    regValue R.dst (run (clear R) m s).basis=0 ∧
    regValue R.S (run (clear R) m s).basis=0 ∧
    regValue R.T (run (clear R) m s).basis=0 ∧
    ∀q,q∉R.dst → q∉R.S → q∉R.T → (run (clear R) m s).basis q=s.basis q := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hsl := w.S
  have hhi : R.hi.length=R.h := by omega
  have hSS : R.S.length=R.h+1 := by omega
  let a := regValue R.lo s.basis
  let b := regValue R.hi s.basis
  let A := rawValue R.h a
  let B := rawValue R.h b
  let S := a+b
  let Z := rawValue (R.h+1) S
  let d : Int := ((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)-(2^(2*R.h-1) : Nat)
  have alo : a<2^R.h := by simpa only [L0] using regValue_lt R.lo s.basis
  have bhi : b<2^R.h := by simpa only [hhi] using regValue_lt R.hi s.basis
  have hA : A<2^R.dlo.length := by
    have v := rawValue_bound R.lo s.basis (by omega)
    simpa only [L0,L2] using v
  have hB : B<2^R.dhi.length := by
    have v := rawValue_bound R.hi s.basis (by omega)
    simpa only [hhi,L3,show 2*(R.bank.length-R.h)=2*R.h by omega] using v
  have slt : S<2^R.S.length := by rw [hSS,pow_succ]; dsimp only [S]; omega
  have st1 := diagaddlo_transition R w he hn s hc0 hi0 (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat)
  have st1' : Transition R s (vec (a^2 : Nat) (b^2 : Nat) S (2*a*b : Nat))
      (vec A (b^2 : Nat) S (2*a*b : Nat)) (mappedDiagAdd R.lo R.dlo R.carry R.cin) := by
    simpa only [A,a,rawValue,Int.natCast_add] using st1
  have st2 := diagaddhi_transition R w he hn s hc0 hi0 A (b^2 : Nat) S (2*a*b : Nat)
  have st2' : Transition R s (vec A (b^2 : Nat) S (2*a*b : Nat))
      (vec A B S (2*a*b : Nat)) (mappedDiagAdd R.hi R.dhi R.carry R.cin) := by
    simpa only [B,b,rawValue,Int.natCast_add] using st2
  have st3 := corrBack_transition R w he hh hn s hz0 hc0 hi0 A B (2*a*b : Nat)
  have st4 := addhi_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d) hB
  have st5 := addlo_transition R w hn s hz0 hc0 hi0 A B S ((2*a*b : Nat)+d+B) hA
  have norm := cross_normalize R.h a b hh alo bhi
  have norm' : ((2*a*b : Nat) : Int)+d+B+A=Z := by
    change ((Z : Nat) : Int)-A-B-((2^R.h : Nat) : Int)*(sharedWord R.h a b+1)+(2^(2*R.h-1) : Nat)=
      (2*a*b : Nat) at norm
    dsimp only [d]
    linarith only [norm]
  rw [norm'] at st5
  have st6 := rawclearSum_transition R w hn s hp0 hc0 A B S slt
  rw [hSS] at st6
  have st7 := clearSum_transition R w he hn s hz0 hc0 hi0 A B 0
  have st8 := rawclearhi_transition R w he hn s hp0 hc0 A 0 0
  have st9 := rawclearlo_transition R w he hn s hp0 hc0 0 0 0
  have st3' : Transition R s (vec A B S (2*a*b : Nat))
      (vec A B S ((2*a*b : Nat)+d)) (corrBack R) := by
    convert st3 using 1 <;> try rfl
    simp only [d]
    congr 1
    ring
  have tail := ((((((((st1'.seq st2').seq st3').seq st4).seq st5).seq st6).seq st7).seq st8).seq st9)
  have initial := clear_start_shape R w he hn s (m.take (measurementCount R.c8)) hd0 hS0 hT0 hz0 hc0 hi0
  have result := tail _ (m.drop (measurementCount R.c8)) initial
  have final : Shape R s (run (clear R) m s) (vec 0 0 0 0) := by
    simpa only [clear,run_append] using result
  refine ⟨final.phase,?_,final.exact 2 0 rfl (by norm_num),final.exact 3 0 rfl (by norm_num),final.rest⟩
  have zlo : regValue R.dlo (run (clear R) m s).basis=0 := final.exact 0 0 rfl (by norm_num)
  have zhi : regValue R.dhi (run (clear R) m s).basis=0 := final.exact 1 0 rfl (by norm_num)
  rw [R.dst_value w,zlo,zhi]
  simp

end ECDSAAdd.Entrant.DiagSq
end DiagonalRegisterIntegration
section DiagonalSquareInterface
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic
def makeC (R : KRegs) : Program := make R++R.scl
def clearC (R : KRegs) : Program := R.smk++clear R
end ECDSAAdd.Entrant.DiagSq
namespace ECDSAAdd.Entrant.KRegs
open Arithmetic
variable (R : KRegs)
theorem diag_sq_full_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.make R) R.invF := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  have r := DiagSq.make_correct R w he hh hn s m hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [invF,r.2.2.1,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  exact ⟨rfl,rfl⟩

theorem diag_sq_full_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.clear R) R.invF := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  have r := DiagSq.clear_correct R w he hh hn s m hd0 (by rw [hI.1,R.lo_mod w,R.hi_div w]) (by rw [hI.2,R.lo_mod w,R.hi_div w])
    (xz hz0 hz) hp0 hc0 hi0
  refine ⟨r.1,r.2.1,?_,fun q h x => r.2.2.2.2 q h (fun y => x (List.mem_append_left _ y)) (fun y => x (List.mem_append_right _ y))⟩
  rw [regValue_append,r.2.2.1,r.2.2.2.1]; simp

theorem diag_sq_cl_make (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqMake R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.makeC R) R.invC := by
  intro s m hd0 hX hp0 hc0 hz0 hi0
  let a := m.take (measurementCount (DiagSq.make R))
  let b := m.drop (measurementCount (DiagSq.make R))
  have r := DiagSq.make_correct R w he hh hn s a hd0 (xz hX (fun q h => List.mem_append_left _ h))
    (xz hX (fun q h => List.mem_append_right _ h)) (xz hz0 hz) hp0 hc0 hi0
  generalize hu : run (DiagSq.make R) a s=u at r
  have fu : ∀q,q∉R.S → q∉R.T → q∉R.dst → u.basis q=s.basis q := fun q a b c => r.2.2.2.2 q c a b
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S ∧ q∉R.T ∧ q∉R.dst) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => fu q (hl q hq).1 (hl q hq).2.1 (hl q hq).2.2)
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin) : q∉R.S ∧ q∉R.T ∧ q∉R.dst :=
    let x := R.outside hn q h; ⟨x.2.1,x.2.2,x.1⟩
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := R.scl_correct w hn u b (by rw [r.2.2.1,lo,hi])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((fu _ (o _ (by simp)).1 (o _ (by simp)).2.1 (o _ (by simp)).2.2).trans hi0)
  have eq : run (DiagSq.makeC R) m s=run R.scl b u := by
    rw [DiagSq.makeC,run_append,←hu]
  rw [eq]
  have sT := R.outside hn
  have dS : ∀q∈R.dst,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  have TS : ∀q∈R.T,q∉R.S := kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega)
  refine ⟨c.1.trans r.1,?_,?_,?_⟩
  · rw [kkeep c.2.2 dS,r.2.1]
  · refine ⟨c.2.1,?_⟩
    rw [kkeep c.2.2 TS,r.2.2.2.1,R.lo_mod w,R.hi_div w]
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2 q xS).trans (fu q xS xT h)

theorem diag_sq_cl_clear (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h=32 ∨ R.h=33) (hn : R.all.Nodup) (z : List Wire) (hz : ∀q∈R.z,q∈z) :
    SqClear R.bank R.dst (R.S++R.T) R.pad R.carry z R.cin (DiagSq.clearC R) R.invC := by
  intro s m hd0 hI hp0 hc0 hz0 hi0
  let a := m.take (measurementCount R.smk)
  let b := m.drop (measurementCount R.smk)
  have r := R.smk_correct w hn s a hI.1 (xz hz0 hz) hc0 hi0
  generalize hu : run R.smk a s=u at r
  have o (q : Wire) (h : q∈R.bank ∨ q∈R.z ∨ q∈R.pad ∨ q∈R.carry ∨ q=R.cin ∨ q∈R.dst ∨ q∈R.T) : q∉R.S := by
    rcases h with h|h|h|h|h|h|h
    · exact (R.outside hn q (Or.inl h)).2.1
    · exact (R.outside hn q (Or.inr (Or.inl h))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inl h)))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inl h))))).2.1
    · exact (R.outside hn q (Or.inr (Or.inr (Or.inr (Or.inr h))))).2.1
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
    · exact kdis hn (fun q => by simp only [all,List.count_cons,List.count_append]; omega) q h
  have keep (l : List Wire) (hl : ∀q∈l,q∉R.S) : regValue l u.basis=regValue l s.basis :=
    regValue_congr _ _ _ (fun q hq => r.2.2 q (hl q hq))
  have bk := keep R.bank (fun q h => o q (Or.inl h))
  have lo : regValue R.lo u.basis=regValue R.lo s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_take h)))
  have hi : regValue R.hi u.basis=regValue R.hi s.basis := keep _ (fun q h => o q (Or.inl (List.mem_of_mem_drop h)))
  have c := DiagSq.clear_correct R w he hh hn u b (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))),bk]; exact hd0)
    (by rw [r.2.1,lo,hi])
    (by rw [keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))),hI.2,lo,hi,R.lo_mod w,R.hi_div w])
    ((keep _ (fun q h => o q (Or.inr (Or.inl h)))).trans (xz hz0 hz))
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inl h))))).trans hp0)
    ((keep _ (fun q h => o q (Or.inr (Or.inr (Or.inr (Or.inl h)))))).trans hc0)
    ((r.2.2 _ (o _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).trans hi0)
  have eq : run (DiagSq.clearC R) m s=run (DiagSq.clear R) b u := by
    rw [DiagSq.clearC,run_append,←hu]
  rw [eq]
  refine ⟨c.1.trans r.1,c.2.1,?_,?_⟩
  · rw [regValue_append,c.2.2.1,c.2.2.2.1]; simp
  · intro q h x
    have xS : q∉R.S := fun y => x (List.mem_append_left _ y)
    have xT : q∉R.T := fun y => x (List.mem_append_right _ y)
    exact (c.2.2.2.2 q h xS xT).trans (r.2.2 q xS)

end ECDSAAdd.Entrant.KRegs
end DiagonalSquareInterface


-- DIAGONAL COMPONENT RawBaseline.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
namespace ECDSAAdd.Entrant
open Arithmetic
def raw_ksq (k : Nat) : Nat := signedSquareRowsCount k+2*k-1

def raw_kcost (n h : Nat) : Nat :=
  raw_ksq h+raw_ksq (n-h)+(n-h)+raw_ksq (n-h+1)+2*(2*(n-h+1)-1)+(2*n-h-1)

namespace KRegs
variable (R : KRegs)
def raw_m1 : Program := mappedSignedSquare R.lo R.dlo R.pad R.carry R.cin
def raw_m2 : Program := mappedSignedSquare R.hi R.dhi R.pad R.carry R.cin
def raw_m5 : Program := mappedSignedSquare R.S R.T R.pad R.carry R.cin
def raw_c5 : Program := mappedSignedSquareClear R.S R.T R.pad R.carry R.cin
def raw_c2 : Program := mappedSignedSquareClear R.hi R.dhi R.pad R.carry R.cin
def raw_c1 : Program := mappedSignedSquareClear R.lo R.dlo R.pad R.carry R.cin
def raw_make : Program := R.raw_m1++R.raw_m2++R.m3++R.m4++R.raw_m5++R.m6++R.m7++R.m8
def raw_clear : Program := R.c8++R.c7++R.c6++R.raw_c5++R.c4++R.m3++R.raw_c2++R.raw_c1
theorem raw_make_counts (w : R.W) :
    toffoliCount R.raw_make=raw_kcost R.bank.length R.h ∧ measurementCount R.raw_make=raw_kcost R.bank.length R.h := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have q1 := mappedSignedSquare_counts R.lo R.dlo R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q2 := mappedSignedSquare_counts R.hi R.dhi R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q5 := mappedSignedSquare_counts R.S R.T R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q3 := copyRegister_counts none R.lo (R.S.take R.h) (by omega)
  have q4 := addInPlace_counts (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q6 := subInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q7 := subInPlace_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q8 := addInPlace_counts (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  simp only [raw_make,raw_m1,raw_m2,m3,m4,raw_m5,m6,m7,m8,toffoliCount_append,measurementCount_append,
    q1.1.1,q1.1.2,q2.1.1,q2.1.2,q5.1.1,q5.1.2,q3.1,q3.2,q4.1,q4.2,q6.1,q6.2,q7.1,q7.2,q8.1,q8.2]
  simp only [L0,L1,L2,L3,L4,hTl,hSl,raw_kcost,raw_ksq,Option.isSome_none,Bool.false_eq_true,if_false]
  constructor <;> omega

theorem raw_clear_counts (w : R.W) :
    toffoliCount R.raw_clear=raw_kcost R.bank.length R.h ∧ measurementCount R.raw_clear=raw_kcost R.bank.length R.h := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have q1 := mappedSignedSquare_counts R.lo R.dlo R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q2 := mappedSignedSquare_counts R.hi R.dhi R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q5 := mappedSignedSquare_counts R.S R.T R.pad R.carry R.cin (by omega) (by omega) hpl (by omega)
  have q3 := copyRegister_counts none R.lo (R.S.take R.h) (by omega)
  have q4 := subInPlace_counts (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q6 := addInPlace_counts (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q7 := addInPlace_counts (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have q8 := subInPlace_counts (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  simp only [raw_clear,raw_c1,raw_c2,m3,c4,raw_c5,c6,c7,c8,toffoliCount_append,measurementCount_append,
    q1.2.1,q1.2.2,q2.2.1,q2.2.2,q5.2.1,q5.2.2,q3.1,q3.2,q4.1,q4.2,q6.1,q6.2,q7.1,q7.2,q8.1,q8.2]
  simp only [L0,L1,L2,L3,L4,hTl,hSl,raw_kcost,raw_ksq,Option.isSome_none,Bool.false_eq_true,if_false]
  constructor <;> omega

theorem raw_steps_support (w : R.W) :
    ECDSAAdd.wires R.raw_make⊆R.all.toFinset ∧ ECDSAAdd.wires R.raw_clear⊆R.all.toFinset := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z; have hpl := w.pad; have hcl := w.carry
  have g1 := mappedSignedSquare_wires_subset R.lo R.dlo R.pad R.carry R.cin (by omega) hpl (by omega)
  have g2 := mappedSignedSquare_wires_subset R.hi R.dhi R.pad R.carry R.cin (by omega) hpl (by omega)
  have g5 := mappedSignedSquare_wires_subset R.S R.T R.pad R.carry R.cin (by omega) hpl (by omega)
  have g3 := copyRegister_wires_subset none R.lo (R.S.take R.h)
  have g4 := addInPlace_wires (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g6 := addInPlace_wires (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g7 := addInPlace_wires (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g8 := addInPlace_wires (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g4s := subInPlace_wires (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g6s := subInPlace_wires (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g7s := subInPlace_wires (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have g8s := subInPlace_wires (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
    (by simp only [List.length_append]; omega) (by simp only [List.length_take]; omega)
  have sb : R.bank ⊆ R.all := fun q h => R.mem_all q (Or.inl h)
  have sd : R.dst ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inl h))
  have sS : R.S ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inr (Or.inl h)))
  have sT : R.T ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inl h))))
  have sz : R.z ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  have sp : R.pad ⊆ R.all := fun q h => R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  have sc : R.carry ⊆ R.all := fun q h =>
    R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have si : [R.cin] ⊆ R.all := by
    intro q h; simp only [List.mem_singleton] at h
    exact R.mem_all q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  have tk {l : List Wire} {k : Nat} (h : l ⊆ R.all) : l.take k ⊆ R.all := fun q hq => h (List.mem_of_mem_take hq)
  have dr {l : List Wire} {k : Nat} (h : l ⊆ R.all) : l.drop k ⊆ R.all := fun q hq => h (List.mem_of_mem_drop hq)
  have fs {l : List Wire} (h : l ⊆ R.all) : l.toFinset ⊆ R.all.toFinset :=
    fun q hq => List.mem_toFinset.mpr (h (List.mem_toFinset.mp hq))
  have ap {l1 l2 : List Wire} (h1 : l1 ⊆ R.all) (h2 : l2 ⊆ R.all) : l1++l2 ⊆ R.all :=
    List.append_subset.mpr ⟨h1,h2⟩
  have co {l : List Wire} (h : l ⊆ R.all) : R.cin::l ⊆ R.all := by
    intro q hq; rcases List.mem_cons.mp hq with e|e
    · exact si (by simp [e])
    · exact h e
  have e1 : (R.lo++R.dlo++R.pad++R.carry++[R.cin]).toFinset⊆R.all.toFinset := fs (ap (ap (ap (ap (tk sb) (tk sd)) sp) sc) si)
  have e2 : (R.hi++R.dhi++R.pad++R.carry++[R.cin]).toFinset⊆R.all.toFinset := fs (ap (ap (ap (ap (dr sb) (dr sd)) sp) sc) si)
  have e5 : (R.S++R.T++R.pad++R.carry++[R.cin]).toFinset⊆R.all.toFinset := fs (ap (ap (ap (ap sS sT) sp) sc) si)
  have e3 : ((none : Option Wire).toList++R.lo++R.S.take R.h).toFinset⊆R.all.toFinset := fs (ap (ap (show (none : Option Wire).toList ⊆ R.all by simp) (tk sb)) (tk sS))
  have e4 : (R.cin::(R.hi++R.zS++R.S++R.carry.take (R.S.length-1))).toFinset⊆R.all.toFinset := fs (co (ap (ap (ap (dr sb) (tk sz)) sS) (tk sc)))
  have e6 : (R.cin::(R.dlo++R.zA++R.T++R.carry.take (R.T.length-1))).toFinset⊆R.all.toFinset := fs (co (ap (ap (ap (tk sd) (tk sz)) sT) (tk sc)))
  have e7 : (R.cin::(R.dhi++R.zB++R.T++R.carry.take (R.T.length-1))).toFinset⊆R.all.toFinset := fs (co (ap (ap (ap (dr sd) (tk sz)) sT) (tk sc)))
  have e8 : (R.cin::(R.T++R.zM++R.dmid++R.carry.take (R.dmid.length-1))).toFinset⊆R.all.toFinset := fs (co (ap (ap (ap sT (tk sz)) (dr sd)) (tk sc)))
  constructor
  · simp only [raw_make,raw_m1,raw_m2,m3,m4,raw_m5,m6,m7,m8,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨g1.1.trans e1,g2.1.trans e2⟩,g3.trans e3⟩,g4 ▸ e4⟩,g5.1.trans e5⟩,g6s ▸ e6⟩,
      g7s ▸ e7⟩,g8 ▸ e8⟩
  · simp only [raw_clear,raw_c1,raw_c2,m3,c4,raw_c5,c6,c7,c8,wires_append,Finset.union_subset_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨g8s ▸ e8,g7 ▸ e7⟩,g6 ▸ e6⟩,g5.2.trans e5⟩,g4s ▸ e4⟩,g3.trans e3⟩,
      g2.2.trans e2⟩,g1.2.trans e1⟩

theorem raw_steps_physical (hn : R.all.Nodup) :
    GatePhysical R.raw_make ∧ GatePhysical R.raw_clear := by
  have p1 := mappedSignedSquare_physical R.lo R.dlo R.pad R.carry R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have p2 := mappedSignedSquare_physical R.hi R.dhi R.pad R.carry R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have p5 := mappedSignedSquare_physical R.S R.T R.pad R.carry R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have p3 := copyRegister_physical none R.lo (R.S.take R.h) (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega)) (by intro c hc; simp at hc)
  have a4 := addInPlace_physical (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have a6 := addInPlace_physical (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have a7 := addInPlace_physical (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have a8 := addInPlace_physical (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have s4 := subInPlace_physical (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have s6 := subInPlace_physical (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have s7 := subInPlace_physical (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  have s8 := subInPlace_physical (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin (knd hn (fun q => by have c := R.counts q; simp only [all,List.count_cons,List.count_append]; omega))
  constructor
  · simp only [raw_make,raw_m1,raw_m2,m3,m4,raw_m5,m6,m7,m8,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨p1.1,p2.1⟩,p3⟩,a4⟩,p5.1⟩,s6⟩,s7⟩,a8⟩
  · simp only [raw_clear,raw_c1,raw_c2,m3,c4,raw_c5,c6,c7,c8,gatePhysical_append]
    exact ⟨⟨⟨⟨⟨⟨⟨s8,a7⟩,a6⟩,p5.2⟩,s4⟩,p3⟩,p2.2⟩,p1.2⟩

theorem raw_tiny_slots (w : R.W) (h33 : R.h≤33) (hhi : R.bank.length-R.h≤34) (hb : R.bank.length≤66) :
    Challenge.gateSlots R.raw_make≤150000 ∧ Challenge.gateSlots R.raw_clear≤150000 := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have h5 := w.h5; have hdl := w.dst; have hSl := w.S
  have hTl := w.T; have hzl := w.z
  have g1 := Baselines.mappedSigned_gateSlots_le R.lo R.dlo R.pad R.carry R.cin
  have g2 := Baselines.mappedSigned_gateSlots_le R.hi R.dhi R.pad R.carry R.cin
  have g5 := Baselines.mappedSigned_gateSlots_le R.S R.T R.pad R.carry R.cin
  have a4 := Baselines.addInPlace_gateSlots_le (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
  have a6 := Baselines.addInPlace_gateSlots_le (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
  have a7 := Baselines.addInPlace_gateSlots_le (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
  have a8 := Baselines.addInPlace_gateSlots_le (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
  have s4 := Baselines.subInPlace_gateSlots_le (R.hi++R.zS) R.S (R.carry.take (R.S.length-1)) R.cin
  have s6 := Baselines.subInPlace_gateSlots_le (R.dlo++R.zA) R.T (R.carry.take (R.T.length-1)) R.cin
  have s7 := Baselines.subInPlace_gateSlots_le (R.dhi++R.zB) R.T (R.carry.take (R.T.length-1)) R.cin
  have s8 := Baselines.subInPlace_gateSlots_le (R.T++R.zM) R.dmid (R.carry.take (R.dmid.length-1)) R.cin
  have c3 := Baselines.copyRegister_gateSlots none R.lo (R.S.take R.h)
  have x1 : R.lo.length*(12*(R.lo.length+1)+6*R.dlo.length) ≤ 33*(12*34+6*66) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x2 : R.hi.length*(12*(R.hi.length+1)+6*R.dhi.length) ≤ 34*(12*35+6*68) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : R.S.length*(12*(R.S.length+1)+6*R.T.length) ≤ 35*(12*36+6*70) :=
    Nat.mul_le_mul (by omega) (by omega)
  have y4 : (R.hi++R.zS).length ≤ 35 := by simp only [List.length_append]; omega
  have y6 : (R.dlo++R.zA).length ≤ 70 := by simp only [List.length_append]; omega
  have y7 : (R.dhi++R.zB).length ≤ 70 := by simp only [List.length_append]; omega
  have y8 : (R.T++R.zM).length ≤ 102 := by simp only [List.length_append]; omega
  have y9 : R.dmid.length ≤ 102 := by omega
  have yc : min R.lo.length (R.S.take R.h).length ≤ 33 := by omega
  constructor
  · simp only [raw_make,raw_m1,raw_m2,m3,m4,raw_m5,m6,m7,m8,Challenge.gateSlots_append]; omega
  · simp only [raw_clear,raw_c1,raw_c2,m3,c4,raw_c5,c6,c7,c8,Challenge.gateSlots_append]; omega

end KRegs
end ECDSAAdd.Entrant


-- DIAGONAL COMPONENT DiagonalResources.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
section DiagonalResources
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.DiagSq
open Arithmetic

theorem counts_rel (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (make R)+(R.h-2)+3=toffoliCount R.raw_make ∧
    measurementCount (make R)+(R.h-2)+3=measurementCount R.raw_make ∧
    toffoliCount (clear R)+(R.h-2)+3=toffoliCount R.raw_clear ∧
    measurementCount (clear R)+(R.h-2)+3=measurementCount R.raw_clear := by
  have h4 := w.h4; have hSl := w.S; have hTl := w.T; have hcl := w.carry
  have hdl := w.dst; have hpl := w.pad
  have t1 := rawT_counts R.lo R.dlo R.pad R.carry (by simp only [KRegs.lo,List.length_take]; omega)
    (by simp only [KRegs.lo,KRegs.dlo,List.length_take]; omega) hpl
    (by simp only [KRegs.lo,List.length_take]; omega)
  have t2 := rawT_counts R.hi R.dhi R.pad R.carry (by simp only [KRegs.hi,List.length_drop]; omega)
    (by simp only [KRegs.hi,KRegs.dhi,List.length_drop]; omega) hpl
    (by simp only [KRegs.hi,List.length_drop]; omega)
  have t5 := rawT_counts R.S R.T R.pad R.carry (by omega) (by omega) hpl (by omega)
  have cc := correction_counts R.h R.lo R.hi R.S R.T R.carry (parity R) R.cin
    (by omega) (by omega) (by omega) (by omega)
  have dc := mappedDiag_counts R.S R.T R.carry R.cin (by omega) hTl (by omega)
  simp only [make,headBlock,seeds,clear,corr,corrBack,rawMake,rawClear,
    KRegs.raw_make,KRegs.raw_clear,KRegs.smk,KRegs.scl,KRegs.raw_m1,KRegs.raw_m2,KRegs.raw_m5,
    KRegs.raw_c1,KRegs.raw_c2,KRegs.raw_c5,mappedSignedSquare,mappedSignedSquareClear,
    toffoliCount_append,measurementCount_append,cc.1,cc.2.1,cc.2.2.1,cc.2.2.2,
    dc.1.1,dc.1.2,dc.2.1,dc.2.2] at t1 t2 t5 ⊢
  omega

theorem slots_rel (R : KRegs) :
    Challenge.gateSlots (make R)≤Challenge.gateSlots R.raw_make+Challenge.gateSlots (corr R) ∧
    Challenge.gateSlots (clear R)≤Challenge.gateSlots R.raw_clear+Challenge.gateSlots (corrBack R) := by
  have t1 := rawT_slots R.lo R.dlo R.pad R.carry
  have t2 := rawT_slots R.hi R.dhi R.pad R.carry
  have t5 := rawT_slots R.S R.T R.pad R.carry
  simp only [make,headBlock,seeds,clear,corr,corrBack,rawMake,rawClear,
    KRegs.raw_make,KRegs.raw_clear,KRegs.smk,KRegs.scl,KRegs.raw_m1,KRegs.raw_m2,KRegs.raw_m5,
    KRegs.raw_c1,KRegs.raw_c2,KRegs.raw_c5,mappedSignedSquare,mappedSignedSquareClear,Challenge.gateSlots_append] at t1 t2 t5 ⊢
  omega

theorem corr_slots (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (corr R)≤800 ∧ Challenge.gateSlots (corrBack R)≤800 := by
  have h4 := w.h4; have hSl := w.S; have hTl := w.T
  have len := correctionBits_length R.h R.S (parity R) (by omega) (by omega)
  have sub := Baselines.mappedSub_gateSlots_le (correctionBits R.h R.S (parity R))
    (R.T.drop R.h) (R.carry.take (R.h+1)) R.cin
  have add := Baselines.mappedAdd_gateSlots_le (correctionBits R.h R.S (parity R))
    (R.T.drop R.h) (R.carry.take (R.h+1)) R.cin
  have inc := Baselines.mappedAdd_gateSlots_le (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  have dec := Baselines.mappedSub_gateSlots_le (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin
  simp only [len,mappedConstant_length,List.length_drop] at sub add inc dec
  simp only [corr,corrBack,correction,correctionBack,loadedSub,loadedAdd,Challenge.gateSlots_append,
    load,unload,Baselines.gateSlots_cons,Challenge.instructionSlots,Baselines.gateSlots_nil]
  omega


theorem load_support (a b c q cin : Wire) :
    wires (load a b c q cin)⊆[a,b,c,q,cin].toFinset ∧
    wires (unload a b c q cin)⊆[a,b,c,q,cin].toFinset := by
  constructor <;> intro x hx <;>
    simp [load,unload,wires,Instr.wires] at hx ⊢ <;> tauto

theorem mapped_support_to (W : List Wire) (bits : List MappedBit) (dst carry : List Wire) (cin : Wire)
    (hi : cin∈W) (hb : ∀x∈mappedWires bits,x∈W) (hd : ∀x∈dst,x∈W) (hc : ∀x∈carry,x∈W) :
    wires (mappedAdd bits dst carry cin)⊆W.toFinset ∧ wires (mappedSub bits dst carry cin)⊆W.toFinset := by
  have lift {P : Program} (hw : wires P⊆(mappedWires bits++dst++carry++[cin]).toFinset) :
      wires P⊆W.toFinset := by
    intro x hx
    have h := hw hx
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    have b := hb x; have d := hd x; have c := hc x
    rcases h with ((h|h)|h)|h
    · exact b h
    · exact d h
    · exact c h
    · simpa only [h] using hi
  exact ⟨lift (mappedAdd_wires_subset bits dst carry cin),lift (mappedSub_wires_subset bits dst carry cin)⟩

theorem corr_views (R : KRegs) (w : R.W) :
    R.lo.getD (R.h-1) 0∈R.bank ∧ R.hi.getD (R.h-1) 0∈R.bank ∧
    R.S.getD (R.h-1) 0∈R.S ∧ parity R∈R.z ∧
    ∀x∈mappedWires (correctionBits R.h R.S (parity R)),x∈R.S ∨ x∈R.z := by
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := R.lens w
  have h4 := w.h4; have hh := w.hh; have hsl := w.S; have hzl := w.z
  have a := List.mem_of_mem_take (getD_in R.lo (R.h-1) (by omega))
  have b := List.mem_of_mem_drop (getD_in R.hi (R.h-1) (by omega))
  have c := getD_in R.S (R.h-1) (by omega)
  have q : parity R∈R.z := getD_in R.z 0 (by omega)
  refine ⟨a,b,c,q,?_⟩
  intro x hx
  rw [correctionBits_wires] at hx
  rcases List.mem_append.mp hx with hx|hx
  · exact Or.inl (List.mem_of_mem_take hx)
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact Or.inr q
    · exact Or.inl c

theorem corr_support (R : KRegs) (w : R.W) :
    wires (corr R)⊆R.all.toFinset ∧ wires (corrBack R)⊆R.all.toFinset := by
  have v := corr_views R w
  have ci : R.cin∈R.all := by simp [KRegs.all]
  have cp : [R.lo.getD (R.h-1) 0,R.hi.getD (R.h-1) 0,R.S.getD (R.h-1) 0,parity R,R.cin].toFinset⊆R.all.toFinset := by
    intro x hx
    simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢
    rcases hx with rfl|rfl|rfl|rfl|rfl
    · simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
    · simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
    · simp only [KRegs.all,List.mem_cons,List.mem_append]; tauto
    · simp [KRegs.all,v.2.2.2.1]
    · exact ci
  have lp := load_support (R.lo.getD (R.h-1) 0) (R.hi.getD (R.h-1) 0) (R.S.getD (R.h-1) 0) (parity R) R.cin
  have l := lp.1.trans cp
  have u := lp.2.trans cp
  have bm := mapped_support_to R.all (correctionBits R.h R.S (parity R)) (R.T.drop R.h) (R.carry.take (R.h+1)) R.cin ci
    (by intro x hx; rcases v.2.2.2.2 x hx with h|h <;> simp [KRegs.all,h])
    (by intro x hx; simp [KRegs.all,List.mem_of_mem_drop hx])
    (by intro x hx; simp [KRegs.all,List.mem_of_mem_take hx])
  have im := mapped_support_to R.all (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin ci
    (by simp [mappedConstant,mappedConstantBit,mappedWires])
    (by intro x hx; simp [KRegs.all,List.mem_of_mem_drop hx])
    (by intro x hx; simp [KRegs.all,List.mem_of_mem_take hx])
  simp only [corr,corrBack,correction,correctionBack,loadedSub,loadedAdd,wires_append,Finset.union_subset_iff]
  tauto

theorem loaded_physical (a b c q cin : Wire) (bits : List MappedBit) (dst carry : List Wire) (k : Nat)
    (ha : a≠q) (hb : b≠q) (hc : c≠q) (hn : (cin::dst++carry).Nodup)
    (hs : ∀x∈mappedWires bits,x∉cin::dst++carry) :
    GatePhysical (loadedSub a b c q cin bits dst carry k) ∧ GatePhysical (loadedAdd a b c q cin bits dst carry k) := by
  have nd := (drop_views dst carry cin k hn).1
  have src : ∀b∈bits,∀x∈b.wire,x∉cin::dst.drop k++carry := by
    intro b hb x hx bad
    have m : x∈mappedWires bits := List.mem_flatMap.mpr ⟨b,hb,by simpa using hx⟩
    apply hs x m
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    rcases bad with (h|h)|h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (List.mem_of_mem_drop h))
    · exact Or.inr h
  have add := mappedAdd_physical bits (dst.drop k) carry cin nd src
  have sub : GatePhysical (mappedSub bits (dst.drop k) carry cin) := by
    simp only [mappedSub,gatePhysical_append]
    exact ⟨⟨notRegister_physical _,add⟩,notRegister_physical _⟩
  have l : GatePhysical (load a b c q cin) := by
    simp [load,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ha,hb,hc]
  have u : GatePhysical (unload a b c q cin) := by
    simp [unload,GatePhysical,RecordedQuantum.PhysicalInstr,ProperGate,ha,hb,hc]
  simp only [loadedSub,loadedAdd,gatePhysical_append]
  tauto

theorem corr_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) :
    GatePhysical (corr R) ∧ GatePhysical (corrBack R) := by
  have v := corr_views R w
  have out (x : Wire) (hx : x∈R.bank++R.S) : x∉R.z :=
    kdis hn (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega) x hx
  have aq : R.lo.getD (R.h-1) 0≠parity R := fun e => out _ (List.mem_append.mpr (Or.inl v.1)) (e ▸ v.2.2.2.1)
  have bq : R.hi.getD (R.h-1) 0≠parity R := fun e => out _ (List.mem_append.mpr (Or.inl v.2.1)) (e ▸ v.2.2.2.1)
  have cq : R.S.getD (R.h-1) 0≠parity R := fun e => out _ (List.mem_append.mpr (Or.inr v.2.2.1)) (e ▸ v.2.2.2.1)
  have nd (n : Nat) : (R.cin::R.T++R.carry.take n).Nodup := knd hn (fun q => by
    have c := (List.take_sublist n R.carry).count_le q
    simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  have src (x : Wire) (hx : x∈mappedWires (correctionBits R.h R.S (parity R))) :
      x∉R.cin::R.T++R.carry.take (R.h+1) := by
    have m : x∈R.S++R.z := List.mem_append.mpr (v.2.2.2.2 x hx)
    exact kdis hn (fun q => by have c := (List.take_sublist (R.h+1) R.carry).count_le q; simp only [KRegs.all,List.count_cons,List.count_append]; omega) x m
  have lp := loaded_physical (R.lo.getD (R.h-1) 0) (R.hi.getD (R.h-1) 0) (R.S.getD (R.h-1) 0)
    (parity R) R.cin (correctionBits R.h R.S (parity R)) R.T (R.carry.take (R.h+1)) R.h aq bq cq (nd _) src
  have it := (drop_views R.T (R.carry.take 2) R.cin (2*R.h-1) (nd 2)).1
  have ip := mappedAdd_physical (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin it
    (by simp [mappedConstant,mappedConstantBit])
  have sp : GatePhysical (mappedSub (mappedConstant none 3 1) (R.T.drop (2*R.h-1)) (R.carry.take 2) R.cin) := by
    simp only [mappedSub,gatePhysical_append]
    exact ⟨⟨notRegister_physical _,ip⟩,notRegister_physical _⟩
  simp only [corr,corrBack,correction,correctionBack,gatePhysical_append]
  tauto

theorem steps_support (R : KRegs) (w : R.W) : wires (make R)⊆R.all.toFinset ∧ wires (clear R)⊆R.all.toFinset := by
  have old := R.raw_steps_support w
  have cc := corr_support R w
  simp only [make,headBlock,seeds,clear,rawMake,rawClear,
    KRegs.raw_make,KRegs.raw_clear,KRegs.smk,KRegs.scl,KRegs.raw_m1,KRegs.raw_m2,KRegs.raw_m5,
    KRegs.raw_c1,KRegs.raw_c2,KRegs.raw_c5,mappedSignedSquare,mappedSignedSquareClear,wires_append,Finset.union_subset_iff] at old ⊢
  have t1 := rawT_wires R.lo R.dlo R.pad R.carry R.all.toFinset (by tauto) (by tauto) (by tauto)
  have t2 := rawT_wires R.hi R.dhi R.pad R.carry R.all.toFinset (by tauto) (by tauto) (by tauto)
  have t5 := rawT_wires R.S R.T R.pad R.carry R.all.toFinset (by tauto) (by tauto) (by tauto)
  tauto

theorem steps_physical (R : KRegs) (w : R.W) (hn : R.all.Nodup) : GatePhysical (make R) ∧ GatePhysical (clear R) := by
  have old := R.raw_steps_physical hn
  have cc := corr_physical R w hn
  simp only [make,headBlock,seeds,clear,rawMake,rawClear,
    KRegs.raw_make,KRegs.raw_clear,KRegs.smk,KRegs.scl,KRegs.raw_m1,KRegs.raw_m2,KRegs.raw_m5,
    KRegs.raw_c1,KRegs.raw_c2,KRegs.raw_c5,mappedSignedSquare,mappedSignedSquareClear,gatePhysical_append] at old ⊢
  have t1 := rawT_physical R.lo R.dlo R.pad R.carry (by tauto) (by tauto) (by tauto)
  have t2 := rawT_physical R.hi R.dhi R.pad R.carry (by tauto) (by tauto) (by tauto)
  have t5 := rawT_physical R.S R.T R.pad R.carry (by tauto) (by tauto) (by tauto)
  tauto


def cost (R : KRegs) : Nat := raw_kcost R.bank.length R.h-(R.h-2)-3

theorem make_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (make R)=cost R ∧ measurementCount (make R)=cost R := by
  have c := counts_rel R w he
  have o := R.raw_make_counts w
  dsimp only [cost]
  omega

theorem clear_counts (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) :
    toffoliCount (clear R)=cost R ∧ measurementCount (clear R)=cost R := by
  have c := counts_rel R w he
  have o := R.raw_clear_counts w
  dsimp only [cost]
  omega

theorem tiny_slots (R : KRegs) (w : R.W) (he : R.bank.length=2*R.h) (hh : R.h≤33) :
    Challenge.gateSlots (make R)≤150800 ∧ Challenge.gateSlots (clear R)≤150800 := by
  have old := R.raw_tiny_slots w hh (by omega) (by omega)
  have c := corr_slots R w he hh
  have r := slots_rel R
  omega

end ECDSAAdd.Entrant.DiagSq
end DiagonalResources


-- DIAGONAL COMPONENT LowK.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
section
namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

/-- Fold-pad tail: untouched by the leaf producer and cleanup, used only for clean-at-rest scratch. -/
def ktmp (L : CuccaroStreamedSquareWideLayout) : List Wire := L.foldPad.drop 131

def oregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=64,bank:=L.inputBank.take src.length,dst:=dst,
   S:=((ktmp L).take 66).take (src.length-63),
   T:=(ext.take 132).take (2*(src.length-63)),
   z:=(L.leafCarry.drop 193).take 62,
   pad:=L.leafPad,carry:=L.leafCarry.take 193,cin:=L.core.cin}

def iregs (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).lo,dst:=(oregs L ext src dst).dlo,
   S:=((ktmp L).drop 66).take 33,T:=(ext.drop 132).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=32,bank:=(oregs L ext src dst).hi,dst:=(oregs L ext src dst).dhi,
   S:=((ext.drop 198).take 34).take 33,T:=(ext.drop 232).take 66,
   z:=(oregs L ext src dst).z.take 30,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

def jregsS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KRegs :=
  {h:=33,bank:=(oregs L ext src dst).S,dst:=(oregs L ext src dst).T,
   S:=(ext.drop 198).take 34,T:=(ext.drop 232).take 68,
   z:=(oregs L ext src dst).z.take 31,pad:=(oregs L ext src dst).pad,carry:=(oregs L ext src dst).carry,cin:=(oregs L ext src dst).cin}

/-- 128-bit leaves: nested split of the low and high halves, cleaned low inner sum. -/
def kgH (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=(jregsH L ext src dst).S++(jregsH L ext src dst).T,X5:=[],
   Q1:=DiagSq.makeC (iregs L ext src dst),Q1c:=DiagSq.clearC (iregs L ext src dst),
   Q2:=DiagSq.make (jregsH L ext src dst),Q2c:=DiagSq.clear (jregsH L ext src dst),
   Q5:=(oregs L ext src dst).m5,Q5c:=(oregs L ext src dst).c5,
   I1:=(iregs L ext src dst).invC,I2:=(jregsH L ext src dst).invF,I5:=fun _ _ => True}

/-- 129-bit leaf: nested split of the low half and of the sum square, cleaned low inner sum. -/
def kgS (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  {R:=oregs L ext src dst,X1:=(iregs L ext src dst).S++(iregs L ext src dst).T,
   X2:=[],X5:=(jregsS L ext src dst).S++(jregsS L ext src dst).T,
   Q1:=DiagSq.makeC (iregs L ext src dst),Q1c:=DiagSq.clearC (iregs L ext src dst),
   Q2:=(oregs L ext src dst).m2,Q2c:=(oregs L ext src dst).c2,
   Q5:=DiagSq.make (jregsS L ext src dst),Q5c:=DiagSq.clear (jregsS L ext src dst),
   I1:=(iregs L ext src dst).invC,I2:=fun _ _ => True,I5:=(jregsS L ext src dst).invF}

def kg (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) : KG :=
  if src.length=128 then kgH L ext src dst else kgS L ext src dst

theorem ktmp_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) : (ktmp L).length=123 := by
  simp [ktmp,L.foldPad_length hw]

theorem oregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (oregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem iregs_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : 128≤src.length) (h129 : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (iregs L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [iregs,oregs,KRegs.lo,KRegs.dlo,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl] <;> omega

theorem jregsH_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h128 : src.length=128) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsH L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsH,oregs,KRegs.hi,KRegs.dhi,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h128] <;> omega

theorem jregsS_W (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
    (h129 : src.length=129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) : (jregsS L ext src dst).W := by
  have sz := L.measured_bank_widths hw
  have tl := ktmp_length L hw
  constructor <;> simp only [jregsS,oregs,List.length_take,List.length_drop,sz.1,sz.2.1,sz.2.2.1,hd,tl,h129] <;> omega

theorem tmp_count (L : CuccaroStreamedSquareWideLayout) (n : Nat) (q : Wire) :
    (L.inputBank.take n++L.leafPad++L.leafCarry++ktmp L).count q≤
      L.core.work.count q+L.foldPad.count q := by
  have inputBound := (List.take_sublist n L.inputBank).count_le q
  have workSplit := congrArg (List.count q) (List.take_append_drop 129 L.core.work)
  have padSplit := congrArg (List.count q) (List.take_append_drop 1 L.foldPad)
  have tailSplit := congrArg (List.count q) (List.take_append_drop 130 (L.foldPad.drop 1))
  have hdd : (L.foldPad.drop 1).drop 130=L.foldPad.drop 131 := by simp [List.drop_drop]
  rw [hdd] at tailSplit
  simp only [inputBank,leafPad,leafCarry,ktmp,List.count_append] at inputBound workSplit padSplit tailSplit ⊢
  omega

def kbig2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) : List Wire :=
  (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L)++ext

theorem lst_le2 (L : CuccaroStreamedSquareWideLayout) (control : Wire) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (q : Wire) :
    (control::L.core.cin::src++L.inputBank.take src.length++dst++L.leafPad++L.leafCarry++L.core.out++ktmp L).count q ≤
      (control::L.wires).count q := by
  have a := hs q
  have b := hd q
  have banks := tmp_count L src.length q
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,List.count_cons,
    List.count_append,List.count_nil] at a banks ⊢
  omega

theorem kbig2_nodup (L : CuccaroStreamedSquareWideLayout) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q) (ext : List Wire) (hx : ext.Nodup)
    (hdx : ∀q∈ext,q∉control::L.wires) : (kbig2 L ext control src dst).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have b := List.nodup_iff_count_le_one.mp hx q
  have c := lst_le2 L control src dst hs hd q
  have d := List.nodup_iff_count_le_one.mp hn q
  simp only [kbig2,List.count_append] at c ⊢
  by_cases hq : q∈ext
  · have z : (control::L.wires).count q=0 := List.count_eq_zero.mpr (hdx q hq)
    omega
  · have z : ext.count q=0 := List.count_eq_zero.mpr hq
    omega

theorem ktmp_wires (L : CuccaroStreamedSquareWideLayout) (q : Wire) (h : q∈ktmp L) : q∈L.wires := by
  have h' : q∈L.foldPad := List.mem_of_mem_drop h
  simp only [foldPad,List.mem_append] at h'
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_append,List.mem_cons]
  tauto

theorem ext_split4 (ext : List Wire) (a b c : Nat) (q : Wire) :
    ((ext.take 132).take a).count q+((ext.drop 132).take 66).count q+
      (((ext.drop 198).take 34).take b).count q+((ext.drop 232).take c).count q≤ext.count q := by
  have x1 := kcnt_take (ext.take 132) a q
  have x2 := kcnt_take ((ext.drop 198).take 34) b q
  have x3 := kcnt_take (ext.drop 232) c q
  have e1 := kcnt_split ext 132 q
  have e2 := kcnt_split (ext.drop 132) 66 q
  have e3 := kcnt_split (ext.drop 198) 34 q
  have e4 := kcnt_take (ext.drop 132) 66 q
  simp only [List.drop_drop] at e2 e3
  norm_num at e2 e3
  omega

theorem tmp_split2 (L : CuccaroStreamedSquareWideLayout) (a : Nat) (q : Wire) :
    (((ktmp L).take 66).take a).count q+(((ktmp L).drop 66).take 33).count q≤(ktmp L).count q := by
  have x1 := kcnt_take ((ktmp L).take 66) a q
  have x2 := kcnt_take ((ktmp L).drop 66) 33 q
  have e := kcnt_split (ktmp L) 66 q
  omega

theorem carry_split (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    (L.leafCarry.take 193).count q+((L.leafCarry.drop 193).take 62).count q≤L.leafCarry.count q := by
  have x := kcnt_take (L.leafCarry.drop 193) 62 q
  have e := kcnt_split L.leafCarry 193 q
  omega

end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout




theorem sub_of_count {l l' : List Wire} (h : ∀q,l.count q≤l'.count q) : l.toFinset⊆l'.toFinset := by
  intro q hq
  have a := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
  exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by have := h q; omega))

section Inst
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hn hs hd hx hdx in
theorem kgH_nodup : (kgH L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 33 66 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    simp only [KG.all,KG.X,kgH,KRegs.all,oregs,iregs,jregsH,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c ⊢
    omega)

include hn hs hd hx hdx in
theorem kgS_nodup : (kgS L ext src dst).all.Nodup :=
  knd (kbig2_nodup L control hn src dst hs hd ext hx hdx) (fun q => by
    have a := ext_split4 ext (2*(src.length-63)) 34 68 q
    have b := tmp_split2 L (src.length-63) q
    have c := carry_split L q
    have e : List.count q (((ext.drop 198).take 34).take 34)=List.count q ((ext.drop 198).take 34) := by
      rw [List.take_take,Nat.min_self]
    simp only [KG.all,KG.X,kgS,KRegs.all,oregs,iregs,jregsS,kbig2,List.count_cons,List.count_append,List.count_nil] at a b c e ⊢
    omega)

theorem kgH_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgH_jall (q : Wire) :
    (jregsH L ext src dst).all.count q≤(kgH L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgH,KRegs.all,jregsH,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_iall (q : Wire) :
    (iregs L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 30 q
  simp only [KG.all,KG.X,kgS,KRegs.all,iregs,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega
theorem kgS_jall (q : Wire) :
    (jregsS L ext src dst).all.count q≤(kgS L ext src dst).all.count q := by
  have c := (oregs L ext src dst).counts q
  have e := kcnt_take (oregs L ext src dst).z 31 q
  simp only [KG.all,KG.X,kgS,KRegs.all,jregsS,List.count_cons,List.count_append,List.count_nil] at c e ⊢
  omega

include hw h128 hsmax hlen he in
theorem kgH_spec (h : src.length=128) (hall : (kgH L ext src dst).all.Nodup) : (kgH L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgH_iall L ext src dst)
  have nj : (jregsH L ext src dst).all.Nodup := knd hall (kgH_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have n5 : ((oregs L ext src dst).cin::(oregs L ext src dst).S++(oregs L ext src dst).T++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,(iregs L ext src dst).diag_sq_cl_make wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).diag_sq_cl_clear wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    (jregsH L ext src dst).diag_sq_full_make wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsH L ext src dst).diag_sq_full_clear wj (by have sz := L.measured_bank_widths hw; simp only [jregsH,oregs,KRegs.hi,List.length_take,List.length_drop,sz.1,h]; omega) (Or.inl rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsH L ext src dst).invF_local,
    sq_plain_make (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_plain_clear (oregs L ext src dst).cin (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n5 (by omega) (by omega) hpl (by omega),
    sq_plain_local⟩

include hw h128 hsmax hlen he in
theorem kgS_spec (h : src.length=129) (hall : (kgS L ext src dst).all.Nodup) : (kgS L ext src dst).Spec := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
  have ni : (iregs L ext src dst).all.Nodup := knd hall (kgS_iall L ext src dst)
  have nj : (jregsS L ext src dst).all.Nodup := knd hall (kgS_jall L ext src dst)
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hh := w.hh; have h4 := w.h4
  have hdl := w.dst
  have n2 : ((oregs L ext src dst).cin::(oregs L ext src dst).hi++(oregs L ext src dst).dhi++
      (oregs L ext src dst).pad++(oregs L ext src dst).carry).Nodup :=
    knd hR (fun q => by have c := (oregs L ext src dst).counts q; simp only [KRegs.all,List.count_cons,List.count_append]; omega)
  exact ⟨w,(iregs L ext src dst).diag_sq_cl_make wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).diag_sq_cl_clear wi (by have sz := L.measured_bank_widths hw; simp only [iregs,oregs,KRegs.lo,List.length_take,sz.1]; omega) (Or.inl rfl) ni _ (fun q h => List.mem_of_mem_take h),
    (iregs L ext src dst).invC_local,
    sq_plain_make (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain_clear (oregs L ext src dst).cin (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).z n2 (by omega) (by omega) hpl (by omega),
    sq_plain_local,
    (jregsS L ext src dst).diag_sq_full_make wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsS L ext src dst).diag_sq_full_clear wj (by simp only [jregsS,oregs,List.length_take,ktmp_length L hw,h]; norm_num) (Or.inr rfl) nj _ (fun q h => List.mem_of_mem_take h),
    (jregsS L ext src dst).invF_local⟩

end Inst
end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

section Inst3
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext src dst : List Wire)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (he : 300≤ext.length)

include hw in
theorem oregs_lens (h : 128≤src.length) (h2 : src.length≤129) :
    (oregs L ext src dst).h=64 ∧ (oregs L ext src dst).bank.length=src.length := by
  have sz := L.measured_bank_widths hw
  refine ⟨rfl,?_⟩
  simp only [oregs,List.length_take,sz.1]; omega

include hw h128 hsmax hlen he in
theorem kgH_counts (h : src.length=128) :
    toffoliCount (kgH L ext src dst).make=6687 ∧ measurementCount (kgH L ext src dst).make=6687 ∧
    toffoliCount (kgH L ext src dst).clear=6687 ∧ measurementCount (kgH L ext src dst).clear=6687 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsH_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := KG.make_counts (kgH L ext src dst) w
  have cl := KG.clear_counts (kgH L ext src dst) w
  have i1 := DiagSq.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := DiagSq.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have j1 := DiagSq.make_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have j2 := DiagSq.clear_counts (jregsH L ext src dst) wj (by simp only [jregsH]; omega)
  have q := TrimSquare.tsq2_counts (oregs L ext src dst).S (oregs L ext src dst).T (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsH L ext src dst).h=32 := rfl
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30-3)+32 ∧ measurementCount (kgH L ext src dst).Q1=(raw_kcost 64 32-30-3)+32 ∧
      toffoliCount (kgH L ext src dst).Q1c=32+(raw_kcost 64 32-30-3) ∧ measurementCount (kgH L ext src dst).Q1c=32+(raw_kcost 64 32-30-3) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((DiagSq.make (iregs L ext src dst))++(iregs L ext src dst).scl)=_; rw [toffoliCount_append,i1.1,ip.2.2.1]
    · show measurementCount ((DiagSq.make (iregs L ext src dst))++(iregs L ext src dst).scl)=_; rw [measurementCount_append,i1.2,ip.2.2.2.1]
    · show toffoliCount ((iregs L ext src dst).smk++(DiagSq.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]
    · show measurementCount ((iregs L ext src dst).smk++(DiagSq.clear (iregs L ext src dst)))=_; rw [measurementCount_append,i2.2,ip.2.1]
  have t2 : toffoliCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30-3) ∧ measurementCount (kgH L ext src dst).Q2=(raw_kcost 64 32-30-3) ∧
      toffoliCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30-3) ∧ measurementCount (kgH L ext src dst).Q2c=(raw_kcost 64 32-30-3) :=
    ⟨j1.1,j1.2,j2.1,j2.2⟩
  have t5 : toffoliCount (kgH L ext src dst).Q5=ksq 65 ∧ measurementCount (kgH L ext src dst).Q5=ksq 65 ∧
      toffoliCount (kgH L ext src dst).Q5c=ksq 65 ∧ measurementCount (kgH L ext src dst).Q5c=ksq 65 := by
    have e : (oregs L ext src dst).S.length=65 := by omega
    have f : (oregs L ext src dst).T.length=130 := by omega
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (oregs L ext src dst).m5=_; unfold KRegs.m5; rw [q.1.1,e,f]; rfl
    · show measurementCount (oregs L ext src dst).m5=_; unfold KRegs.m5; rw [q.1.2,e,f]; rfl
    · show toffoliCount (oregs L ext src dst).c5=_; unfold KRegs.c5; rw [q.2.1,e,f]; rfl
    · show measurementCount (oregs L ext src dst).c5=_; unfold KRegs.c5; rw [q.2.2,e,f]; rfl
  have rb : (kgH L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgH L ext src dst).R.h=64 := rfl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  exact ⟨mk.1,mk.2,cl.1,cl.2⟩

include hw h128 hsmax hlen he in
theorem kgS_counts (h : src.length=129) :
    toffoliCount (kgS L ext src dst).make=6805 ∧ measurementCount (kgS L ext src dst).make=6805 ∧
    toffoliCount (kgS L ext src dst).clear=6805 ∧ measurementCount (kgS L ext src dst).clear=6805 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have wj := jregsS_W L hw ext src dst h hlen he
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T; have hpl := w.pad; have hcl := w.carry; have hdl := w.dst
  have ol := oregs_lens L hw ext src dst h128 hsmax
  have mk := KG.make_counts (kgS L ext src dst) w
  have cl := KG.clear_counts (kgS L ext src dst) w
  have i1 := DiagSq.make_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have i2 := DiagSq.clear_counts (iregs L ext src dst) wi (by simp only [iregs]; omega)
  have ip := (iregs L ext src dst).piece_counts wi
  have j1 := DiagSq.make_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have j2 := DiagSq.clear_counts (jregsS L ext src dst) wj (by simp only [jregsS]; omega)
  have q := TrimSquare.tsq2_counts (oregs L ext src dst).hi (oregs L ext src dst).dhi (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin (by omega) (by omega) hpl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have jh : (jregsS L ext src dst).h=33 := rfl
  simp only [DiagSq.cost] at i1 i2 j1 j2
  rw [il,ih] at i1 i2 ip
  rw [jl,jh] at j1 j2
  have t1 : toffoliCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30-3)+32 ∧ measurementCount (kgS L ext src dst).Q1=(raw_kcost 64 32-30-3)+32 ∧
      toffoliCount (kgS L ext src dst).Q1c=32+(raw_kcost 64 32-30-3) ∧ measurementCount (kgS L ext src dst).Q1c=32+(raw_kcost 64 32-30-3) := by
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount ((DiagSq.make (iregs L ext src dst))++(iregs L ext src dst).scl)=_; rw [toffoliCount_append,i1.1,ip.2.2.1]
    · show measurementCount ((DiagSq.make (iregs L ext src dst))++(iregs L ext src dst).scl)=_; rw [measurementCount_append,i1.2,ip.2.2.2.1]
    · show toffoliCount ((iregs L ext src dst).smk++(DiagSq.clear (iregs L ext src dst)))=_; rw [toffoliCount_append,i2.1,ip.1]
    · show measurementCount ((iregs L ext src dst).smk++(DiagSq.clear (iregs L ext src dst)))=_; rw [measurementCount_append,i2.2,ip.2.1]
  have t2 : toffoliCount (kgS L ext src dst).Q2=ksq 65 ∧ measurementCount (kgS L ext src dst).Q2=ksq 65 ∧
      toffoliCount (kgS L ext src dst).Q2c=ksq 65 ∧ measurementCount (kgS L ext src dst).Q2c=ksq 65 := by
    have e : (oregs L ext src dst).hi.length=65 := by omega
    have f : (oregs L ext src dst).dhi.length=130 := by omega
    refine ⟨?_,?_,?_,?_⟩
    · show toffoliCount (oregs L ext src dst).m2=_; unfold KRegs.m2; rw [q.1.1,e,f]; rfl
    · show measurementCount (oregs L ext src dst).m2=_; unfold KRegs.m2; rw [q.1.2,e,f]; rfl
    · show toffoliCount (oregs L ext src dst).c2=_; unfold KRegs.c2; rw [q.2.1,e,f]; rfl
    · show measurementCount (oregs L ext src dst).c2=_; unfold KRegs.c2; rw [q.2.2,e,f]; rfl
  have t5 : toffoliCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31-3) ∧ measurementCount (kgS L ext src dst).Q5=(raw_kcost 66 33-31-3) ∧
      toffoliCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31-3) ∧ measurementCount (kgS L ext src dst).Q5c=(raw_kcost 66 33-31-3) :=
    ⟨j1.1,j1.2,j2.1,j2.2⟩
  have rb : (kgS L ext src dst).R.bank.length=src.length := ol.2
  have rh : (kgS L ext src dst).R.h=64 := rfl
  rw [t1.1,t2.1,t5.1,t1.2.1,t2.2.1,t5.2.1,rb,rh,h] at mk
  rw [t1.2.2.1,t2.2.2.1,t5.2.2.1,t1.2.2.2,t2.2.2.2,t5.2.2.2,rb,rh,h] at cl
  norm_num [DiagSq.cost,raw_kcost,raw_ksq,kcost,ksq,kextra,signedSquareRowsCount] at mk cl
  exact ⟨mk.1,mk.2,cl.1,cl.2⟩

end Inst3
end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

section Inst4
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

theorem kg_R : (kg L ext src dst).R=oregs L ext src dst := by
  unfold kg; split <;> rfl

theorem kg_I1 : (kg L ext src dst).I1=(iregs L ext src dst).invC := by
  unfold kg; split <;> rfl

theorem kg_X (q : Wire) (h : q∈(kg L ext src dst).X) : q∈ext ∨ q∈((ktmp L).drop 66).take 33 := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · rcases List.mem_append.mp h with h|h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take (h : q∈((ext.drop 198).take 34).take 33))))
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 66)))
    · exact absurd h (List.not_mem_nil)
  · rw [kg,if_neg c] at h
    simp only [KG.X] at h
    rcases List.mem_append.mp h with h|h
    · rcases List.mem_append.mp h with h|h
      · rcases List.mem_append.mp h with h|h
        · exact Or.inr h
        · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 132).take 66)))
      · exact absurd h (List.not_mem_nil)
    · rcases List.mem_append.mp h with h|h
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 198).take 34)))
      · exact Or.inl (List.mem_of_mem_drop (List.mem_of_mem_take (h : q∈(ext.drop 232).take 68)))

include hn hs hd hx hdx in
theorem kg_nodup : (kg L ext src dst).all.Nodup := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]; exact kgH_nodup L control hn ext src dst hs hd hx hdx
  · rw [kg,if_neg c]; exact kgS_nodup L control hn ext src dst hs hd hx hdx

include hw h128 hsmax hlen he in
theorem kg_spec (hall : (kg L ext src dst).all.Nodup) : (kg L ext src dst).Spec := by
  by_cases c : src.length=128
  · rw [kg,if_pos c] at hall ⊢; exact kgH_spec L hw ext src dst h128 hsmax hlen he c hall
  · rw [kg,if_neg c] at hall ⊢; exact kgS_spec L hw ext src dst h128 hsmax hlen he (by omega) hall

def lowkcost2 (n : Nat) : Nat := if n=128 then 6687 else 6805

include hw h128 hsmax hlen he in
theorem kg_counts :
    toffoliCount (kg L ext src dst).make=lowkcost2 src.length ∧
    measurementCount (kg L ext src dst).make=lowkcost2 src.length ∧
    toffoliCount (kg L ext src dst).clear=lowkcost2 src.length ∧
    measurementCount (kg L ext src dst).clear=lowkcost2 src.length := by
  by_cases c : src.length=128
  · rw [kg,lowkcost2,if_pos c,if_pos c]; exact kgH_counts L hw ext src dst h128 hsmax hlen he c
  · rw [kg,lowkcost2,if_neg c,if_neg c]; exact kgS_counts L hw ext src dst h128 hsmax hlen he (by omega)

include hw h128 hsmax hlen he in
theorem kg_support :
    ECDSAAdd.wires (kg L ext src dst).make⊆(kg L ext src dst).all.toFinset ∧
    ECDSAAdd.wires (kg L ext src dst).clear⊆(kg L ext src dst).all.toFinset := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have rp := (oregs L ext src dst).piece_support w
  have ip := (iregs L ext src dst).piece_support wi
  have is := DiagSq.steps_support (iregs L ext src dst) wi
  have tr {P : Program} {A B : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : A⊆B) : ECDSAAdd.wires P⊆B := h1.trans h2
  have ap {P Q : Program} {A : Finset Wire} (h1 : ECDSAAdd.wires P⊆A) (h2 : ECDSAAdd.wires Q⊆A) :
      ECDSAAdd.wires (P++Q)⊆A := by rw [wires_append]; exact Finset.union_subset h1 h2
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have js := DiagSq.steps_support (jregsH L ext src dst) wj
    have iK := sub_of_count (kgH_iall L ext src dst)
    have jK := sub_of_count (kgH_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgH L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact KG.steps_support _ w (ap (tr is.1 iK) (tr ip.2.1 iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr js.1 jK) (tr js.2 jK) (tr rp.2.2.2.2.2.2.1 rK) (tr rp.2.2.2.2.2.2.2 rK)
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have js := DiagSq.steps_support (jregsS L ext src dst) wj
    have iK := sub_of_count (kgS_iall L ext src dst)
    have jK := sub_of_count (kgS_jall L ext src dst)
    have rK : (oregs L ext src dst).all.toFinset⊆(kgS L ext src dst).all.toFinset := fun q hq => KG.r_sub _ q hq
    exact KG.steps_support _ w (ap (tr is.1 iK) (tr ip.2.1 iK)) (ap (tr ip.1 iK) (tr is.2 iK))
      (tr rp.2.2.2.2.1 rK) (tr rp.2.2.2.2.2.1 rK) (tr js.1 jK) (tr js.2 jK)

include hw h128 hsmax hlen he in
theorem kg_physical (hall : (kg L ext src dst).all.Nodup) :
    GatePhysical (kg L ext src dst).make ∧ GatePhysical (kg L ext src dst).clear := by
  have ap {P Q : Program} (h1 : GatePhysical P) (h2 : GatePhysical Q) : GatePhysical (P++Q) :=
    (gatePhysical_append P Q).mpr ⟨h1,h2⟩
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  by_cases h : src.length=128
  · rw [kg,if_pos h] at hall ⊢
    have wj := jregsH_W L hw ext src dst h hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgH_iall L ext src dst)
    have nj := knd hall (kgH_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := DiagSq.steps_physical (iregs L ext src dst) wi ni
    have js := DiagSq.steps_physical (jregsH L ext src dst) wj nj
    exact KG.steps_physical _ hall (ap is.1 ip.2.1) (ap ip.1 is.2) js.1 js.2 rp.2.2.2.2.2.2.1 rp.2.2.2.2.2.2.2
  · rw [kg,if_neg h] at hall ⊢
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have hR : (oregs L ext src dst).all.Nodup := (List.nodup_append.mp hall).1
    have ni := knd hall (kgS_iall L ext src dst)
    have nj := knd hall (kgS_jall L ext src dst)
    have rp := (oregs L ext src dst).piece_physical hR
    have ip := (iregs L ext src dst).piece_physical ni
    have is := DiagSq.steps_physical (iregs L ext src dst) wi ni
    have js := DiagSq.steps_physical (jregsS L ext src dst) wj nj
    exact KG.steps_physical _ hall (ap is.1 ip.2.1) (ap ip.1 is.2) rp.2.2.2.2.1 rp.2.2.2.2.2.1 js.1 js.2

include hw h128 hsmax hlen he in
theorem kg_slots :
    Challenge.gateSlots (kg L ext src dst).make+Challenge.gateSlots (kg L ext src dst).clear≤1200000 := by
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have wi := iregs_W L hw ext src dst h128 hsmax hlen he
  have ol := oregs_lens L hw ext src dst h128 hsmax
  obtain ⟨L0,L1,L2,L3,L4,L5,L6,L7,L8,L9,L10⟩ := (oregs L ext src dst).lens w
  have hSl := w.S; have hTl := w.T
  have ad := (oregs L ext src dst).adder_slots w rfl (by omega)
  have il : (iregs L ext src dst).bank.length=64 := by simp only [iregs]; omega
  have ih : (iregs L ext src dst).h=32 := rfl
  have it := DiagSq.tiny_slots (iregs L ext src dst) wi (by rw [il,ih]) (by rw [ih]; omega)
  have oldit := (iregs L ext src dst).tiny_slots wi (by rw [ih]; omega) (by rw [il,ih]; omega) (by omega)
  have isb := (iregs L ext src dst).make_sub_slots wi
  have g2 := TrimSquare.tsq2_gateSlots_le (oregs L ext src dst).hi (oregs L ext src dst).dhi
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have g5 := TrimSquare.tsq2_gateSlots_le (oregs L ext src dst).S (oregs L ext src dst).T
    (oregs L ext src dst).pad (oregs L ext src dst).carry (oregs L ext src dst).cin
  have x2 : (oregs L ext src dst).hi.length*(12*((oregs L ext src dst).hi.length+1)+6*(oregs L ext src dst).dhi.length) ≤ 65*(12*66+6*130) :=
    Nat.mul_le_mul (by omega) (by omega)
  have x5 : (oregs L ext src dst).S.length*(12*((oregs L ext src dst).S.length+1)+6*(oregs L ext src dst).T.length) ≤ 66*(12*67+6*132) :=
    Nat.mul_le_mul (by omega) (by omega)
  by_cases h : src.length=128
  · rw [kg,if_pos h]
    have wj := jregsH_W L hw ext src dst h hlen he
    have jl : (jregsH L ext src dst).bank.length=64 := by simp only [jregsH]; omega
    have jh : (jregsH L ext src dst).h=32 := rfl
    have jt := DiagSq.tiny_slots (jregsH L ext src dst) wj (by rw [jl,jh]) (by omega)
    have st := KG.steps_slots2 (kgH L ext src dst)
    simp only [kgH,DiagSq.makeC,DiagSq.clearC,KRegs.m5,KRegs.c5,Challenge.gateSlots_append] at st ad ⊢
    omega
  · rw [kg,if_neg h]
    have wj := jregsS_W L hw ext src dst (by omega) hlen he
    have jl : (jregsS L ext src dst).bank.length=66 := by simp only [jregsS]; omega
    have jh : (jregsS L ext src dst).h=33 := rfl
    have jt := DiagSq.tiny_slots (jregsS L ext src dst) wj (by rw [jl,jh]) (by omega)
    have st := KG.steps_slots2 (kgS L ext src dst)
    simp only [kgS,DiagSq.makeC,DiagSq.clearC,KRegs.m2,KRegs.c2,Challenge.gateSlots_append] at st ad ⊢
    omega

end Inst4
end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

def withLowK2 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body : Program) : Program :=
  copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).make++
    eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).clear++
    eraseMask control src (L.inputBank.take src.length)

private theorem diag3_k2_xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem withLowK2_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (withLowK2 L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (withLowK2 L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (withLowK2 L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := kg_R L ext src dst
  have w := oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(oregs L ext src dst).S,q∈ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(kg L ext src dst).X,q∈ext ∨ q∈ktmp L := fun q h =>
    (kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈ktmp L,q∉L.core.out := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈ktmp L,q∉dst := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈ktmp L,q∉src := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈ktmp L,q∉ext := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have ctlB : control∉(L.inputBank.take src.length) := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlD : control∉dst := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have ctlE : control∉ext := fun h => hdx control h (by simp)
  have ctlO : control∉L.core.out := dj (r:=[control]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have srcB : ∀q∈src,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcD : ∀q∈src,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have srcOut : ∀q∈src,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bOut : ∀q∈(L.inputBank.take src.length),q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have dOut : ∀q∈dst,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have bD : ∀q∈(L.inputBank.take src.length),q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have padB : ∀q∈L.leafPad,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carB : ∀q∈L.leafCarry,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinB : L.core.cin∉(L.inputBank.take src.length) := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padOut : ∀q∈L.leafPad,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carOut : ∀q∈L.leafCarry,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinOut : L.core.cin∉L.core.out := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padD : ∀q∈L.leafPad,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carD : ∀q∈L.leafCarry,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinD : L.core.cin∉dst := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  have padE : ∀q∈L.leafPad,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have carE : ∀q∈L.leafCarry,q∉ext := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have cinE : L.core.cin∉ext := dj (r:=[L.core.cin]) (fun q => by
    simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
  -- generic "not a leaf scratch wire" from being outside ext and ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉ktmp L) :
      q∉(oregs L ext src dst).dst ∧ q∉(oregs L ext src dst).T ∧ q∉(kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  let P := if s.basis control then regValue src s.basis else 0
  obtain ⟨a6,r7,e7⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).make++eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).clear) (eraseMask control src (L.inputBank.take src.length)) records s
  obtain ⟨a5,r6,e6⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).make++eraseMask control src (L.inputBank.take src.length)++body++
    copyRegister (some control) src (L.inputBank.take src.length)) (kg L ext src dst).clear a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).make++eraseMask control src (L.inputBank.take src.length)++body)
    (copyRegister (some control) src (L.inputBank.take src.length)) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).make++eraseMask control src (L.inputBank.take src.length)) body a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).make) (eraseMask control src (L.inputBank.take src.length)) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (copyRegister (some control) src (L.inputBank.take src.length)) (kg L ext src dst).make a2 s
  rw [show withLowK2 L ext control src dst body=copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).make++
    eraseMask control src (L.inputBank.take src.length)++body++copyRegister (some control) src (L.inputBank.take src.length)++(kg L ext src dst).clear++
    eraseMask control src (L.inputBank.take src.length) from rfl,e7,e6,e5,e4,e3,e2]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := KG.make_correct (kg L ext src dst) sp hall u0 r2
    (by rw [hKR]; exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (tmpB q (xS q h))]; exact tmp0 q (xS q h)))
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by rw [u0s q (extB q (xT q h))]; exact ext0 q (xT q h)))
    X0
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))]
      exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR]; exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)]
      exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR]; exact (u0s _ cinB).trans hc.cin)
  have i1 := mk.2.2.2.2.1
  rw [kg_I1] at i1
  rw [hKR] at mk
  generalize run (kg L ext src dst).make r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(oregs L ext src dst).dst → q∉(oregs L ext src dst).T → q∉(kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈ktmp L
    · by_cases hX : q∈(kg L ext src dst).X
      · have hI : q∈((ktmp L).drop 66).take 33 := (kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- erase
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask u1 r3 (by
    rw [bank1,ctl1,src1])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r3 u1=u2 at ep1 ef1 ev1 ⊢
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev1 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · exact (ef1 q hb).trans ((u1z q hq hx).trans (u0s q hb))
  have u2ext : ∀q∈ext,u2.basis q=u1.basis q := fun q h => ef1 q (extB q h)
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact ef1 q (fun h => bD q h hq)
  have cb := callback u2' r4 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r4 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r4 u2'=v' at cb loc
  generalize hv : run body r4 u2=v at loc ⊢
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r4 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r4 u2 q hb,run_preserves_outside body r4 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply diag3_k2_xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  -- second copy
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB v r5
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r5 v=w0 at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := by
    rw [cv2,show regValue (L.inputBank.take src.length) v.basis=0 from (regValue_congr _ _ _ vB).trans banks.1,Nat.zero_xor]
    change (if v.basis control then regValue src v.basis else 0)=P
    rw [show v.basis control=s.basis control from (vFrame _ ctlO).trans (u2s _ ctlD ctlE),regValue_congr _ _ _ vSrc]
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    rw [cf2 q hb,vFrame q ho]
    by_cases hx : q∈ext
    · exact u2ext q hx
    · exact ef1 q hb
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (oregs L ext src dst).lo w0.basis=regValue (oregs L ext src dst).lo u0.basis ∧
      regValue (oregs L ext src dst).hi w0.basis=regValue (oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := KG.clear_correct (kg L ext src dst) sp hall w0 r6
    (by
      rw [hKR,show regValue (oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (oregs L ext src dst).dst w0.basis=regValue (oregs L ext src dst).dst u1.basis from
          regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => bD q h hq) (fun h => dOut q hq h))]
      exact dst1)
    (by
      rw [hKR,←mk.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (tmpB q (xS q hq)) (tmpOut q (xS q hq))))
    (by
      rw [hKR,bankLoHi.1,bankLoHi.2,←mk.2.2.2.1]
      exact regValue_congr _ _ _ (fun q hq => w0u1 q (fun h => extB q (xT q hq) h)
        (fun h => extOut q (xT q hq) h)))
    (by rw [hKR]; exact I1w) (by rw [hKR]; exact I2w) (by rw [hKR]; exact I5w)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (xz q hq)))
    (by rw [hKR]; exact (regValue_congr _ _ _ (fun q hq => w0s q (padB q hq) (padOut q hq) (padD q hq) (padE q hq))).trans banks.2.1)
    (by rw [hKR]; exact (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp carW q (List.mem_of_mem_take hq)))
    (by rw [hKR]; exact (w0s _ cinB cinOut cinD cinE).trans hc.cin)
  rw [hKR] at cl
  generalize run (kg L ext src dst).clear r6 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2 q (srcB q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2 _ ctlB).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r7 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r7 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (cp2.trans (vPhase.trans (ep1.trans (mk.1.trans cp1))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2 q (fun h => bOut q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX,cf2 q hb,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx

end ECDSAAdd.Entrant.OwnDiagLowK

namespace ECDSAAdd.Entrant.OwnDiagLowK
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

theorem kg_cnt (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
    (q : Wire) : (kg L ext src dst).all.count q≤(kbig2 L ext control src dst).count q := by
  by_cases c : src.length=128
  · rw [kg,if_pos c]
    have a := ext_split4 ext (2*(src.length-63)) 33 66 q
    have b := tmp_split2 L (src.length-63) q
    have d := carry_split L q
    simp only [KG.all,KG.X,kgH,KRegs.all,oregs,iregs,jregsH,kbig2,List.count_cons,List.count_append,List.count_nil] at a b d ⊢
    omega
  · rw [kg,if_neg c]
    have a := ext_split4 ext (2*(src.length-63)) 34 68 q
    have b := tmp_split2 L (src.length-63) q
    have d := carry_split L q
    have e : List.count q (((ext.drop 198).take 34).take 34)=List.count q ((ext.drop 198).take 34) := by
      rw [List.take_take,Nat.min_self]
    simp only [KG.all,KG.X,kgS,KRegs.all,oregs,iregs,jregsS,kbig2,List.count_cons,List.count_append,List.count_nil] at a b d e ⊢
    omega

theorem withLowK2_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hd : dst.length=2*src.length)
    (he : 300≤ext.length) :
    toffoliCount (withLowK2 L ext control src dst body)=
      2*src.length+2*lowkcost2 src.length+toffoliCount body ∧
    measurementCount (withLowK2 L ext control src dst body)=
      2*src.length+2*lowkcost2 src.length+measurementCount body := by
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have copy := copyRegister_counts (some control) src (L.inputBank.take src.length) inputLen.symm
  have erase := eraseMask_counts control src (L.inputBank.take src.length) inputLen.symm
  have k := kg_counts L hw ext src dst h128 hsmax hd he
  simp only [withLowK2,toffoliCount_append,measurementCount_append,copy.1,copy.2,erase.1,erase.2,
    k.1,k.2.1,k.2.2.1,k.2.2.2,inputLen,Option.isSome_some,if_true]
  constructor <;> omega

theorem withLowK2_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) (hb : ECDSAAdd.wires body⊆(control::L.wires).toFinset) :
    ECDSAAdd.wires (withLowK2 L ext control src dst body)⊆(control::L.wires++ext).toFinset := by
  have st := kg_support L hw ext src dst h128 hsmax hlen he
  have kin : (kg L ext src dst).all.toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq
    have a := List.count_pos_iff.mpr (List.mem_toFinset.mp hq)
    have b := kg_cnt L ext control src dst q
    have c := lst_le2 L control src dst hs hd q
    simp only [kbig2,List.count_append] at b c
    apply List.mem_toFinset.mpr
    simp only [List.mem_append]
    by_cases hx : q∈ext
    · exact Or.inr hx
    · have z : ext.count q=0 := List.count_eq_zero.mpr hx
      exact Or.inl (List.count_pos_iff.mp (by omega))
  have cin : ∀q∈control::src++L.inputBank.take src.length,q∈control::L.wires := by
    intro q h
    have a := List.count_pos_iff.mpr h
    have c := lst_le L control src dst hs hd q
    simp only [List.count_cons,List.count_append] at a c
    exact List.count_pos_iff.mp (by simp only [List.count_cons] at *; omega)
  have cp : ECDSAAdd.wires (copyRegister (some control) src (L.inputBank.take src.length))⊆
      (control::L.wires++ext).toFinset := by
    intro q hq
    have h := copyRegister_wires_subset (some control) src (L.inputBank.take src.length) hq
    simp only [List.mem_toFinset,Option.toList_some,List.singleton_append] at h
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl (cin q (by simpa using h))
  have er : ECDSAAdd.wires (eraseMask control src (L.inputBank.take src.length))⊆
      (control::L.wires++ext).toFinset := by
    intro q hq
    have h := eraseMask_wires_subset control src (L.inputBank.take src.length) hq
    simp only [List.mem_toFinset] at h
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl (cin q (by simpa using h))
  have bd : ECDSAAdd.wires body⊆(control::L.wires++ext).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp (hb hq)
    simp only [List.mem_toFinset,List.mem_append]
    exact Or.inl h
  simp only [withLowK2,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨cp,st.1.trans kin⟩,er⟩,bd⟩,cp⟩,st.2.trans kin⟩,er⟩

theorem withLowK2_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
    (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hb : GatePhysical body) :
    GatePhysical (withLowK2 L ext control src dst body) := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hall := kg_nodup L control hn ext src dst hs hd hx hdx
  have st := kg_physical L hw ext src dst h128 hsmax hlen he hall
  have ndCopy : (src++L.inputBank.take src.length).Nodup :=
    knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉L.inputBank.take src.length := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e
    exact kdis hbig (r:=[c]) (fun q => by
      simp only [kbig,List.count_cons,List.count_append,List.count_nil]; omega) c (by simp)
  have cp := copyRegister_physical (some control) src (L.inputBank.take src.length) ndCopy hcB
  have er := eraseMask_physical control src (L.inputBank.take src.length)
  simp only [withLowK2,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨⟨cp,st.1⟩,er⟩,hb⟩,cp⟩,st.2⟩,er⟩

theorem withLowK2_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (src dst : List Wire) (body : Program)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (he : 300≤ext.length) :
    Challenge.gateSlots (withLowK2 L ext control src dst body)≤1620000+Challenge.gateSlots body := by
  have sizes := L.measured_bank_widths hw
  have st := kg_slots L hw ext src dst h128 hsmax hlen he
  have hcopy := Nat.min_le_right src.length (L.inputBank.take src.length).length
  have hl : (L.inputBank.take src.length).length ≤ 129 := by simp [sizes.1]
  simp only [withLowK2,Challenge.gateSlots_append,Baselines.copyRegister_gateSlots,Baselines.eraseMask_gateSlots]
  omega

end ECDSAAdd.Entrant.OwnDiagLowK

end



-- DIAGONAL COMPONENT All12Primitive.lean

section
-- ===== SquareAccK =====

/-! The accumulated streamed square with all three leaves computed by one
Karatsuba level (`withLowK`), the sum and cross registers borrowed from `ext`. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.OwnDiagAll12Square
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout

structure ExtOK (L : CuccaroStreamedSquareWideLayout) (control : Wire) (ext : List Wire) : Prop where
  nodup : ext.Nodup
  away : ∀q∈ext,q∉control::L.wires
  len : 300≤ext.length

theorem ext_out (L : CuccaroStreamedSquareWideLayout) (control : Wire) (ext : List Wire)
    (he : ExtOK L control ext) (q : Wire) (hq : q∈ext) : q∉L.core.out := fun h =>
  he.away q hq (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])

theorem sum_in (L : CuccaroStreamedSquareWideLayout) (control : Wire) (q : Wire) (h : q∈L.core.sum) :
    q∈control::L.wires := by
  simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h
  · simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
      List.mem_of_mem_drop (List.mem_of_mem_take h)]
  · simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]

theorem withMixedK_contribution (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (hs2 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (orientation : Bool) (items : List MixItem)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (O P V : Nat) (hO : O<SquareReduction.p)
    (ho : regValue L.core.out s.basis=O)
    (hp : P=(if s.basis control then regValue src s.basis else 0)^2)
    (whole : ∀t : BasisState,regValue dst t=P → (∀q,q∉dst → t q=s.basis q) → regValue L.core.product t=P)
    (views : ∀t : BasisState,regValue L.core.product t=P → ∀i∈items,MixView L t i)
    (delta : ZMod SquareReduction.p)
    (payload : ∀t : BasisState,regValue L.core.product t=P → mixSignedSum t items=delta)
    (hV : V<SquareReduction.p)
    (target : measuredOrientationCast (mixFinal orientation items) V=
      measuredOrientationCast orientation O+delta)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) (hst : ∀i∈items,MixStatic L i) :
    (run (OwnDiagLowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).phase=s.phase ∧
    regValue L.core.out (run (OwnDiagLowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (OwnDiagLowK.withLowK2 L ext control src dst (mixFoldsQ L orientation items)) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (mixFoldsQ L orientation items) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (mixFoldsQ_support L hw nd control orientation items hst hw'))
  apply OwnDiagLowK.withLowK2_correct L hw control hn src dst hs hd hs2 hsmax hlen ext he.nodup he.away he.len
    (mixFoldsQ L orientation items) hbody s records hc hzero hz V
  intro t m dstValue same
  have pv : regValue L.core.product t.basis=P := whole t.basis (by simpa [hp] using dstValue) same
  have clean := L.measured_product_frame_clean nd dst hd s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉dst := by
    intro bad
    have dis := L.product_out_disjoint nd
    have pos := List.count_pos_iff.mpr bad
    have bound := hd q
    have product : q∈L.core.product := List.count_pos_iff.mp (by omega)
    exact List.disjoint_left.mp dis product hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have initial : SquareFrame L.core.out t.basis O t.basis := ⟨outO,fun _ _ => rfl⟩
  have folded := mixFoldsQ_frame L hw nd t.basis clean orientation O hO items (views t.basis pv) t m initial
  have cast := mixValue_cast t.basis orientation O items hO
  rw [payload t.basis pv] at cast
  have result : mixValue t.basis orientation O items=V :=
    measuredOrientationCast_injective _ _ _ (mixValue_lt _ _ _ _ hO) hV (cast.trans target.symm)
  exact ⟨folded.1,folded.2.1.trans result,folded.2.2⟩


/-- Branch C forms `high ← high + low` with the measured in-place adder (n-1
Toffolis) instead of the Cuccaro ripple (2n); the clean work register holds
its carries. The sum is removed by the measured in-place subtractor. -/
def sumSrc (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.low++[L.core.pad.getD 0 0]
def sumBank (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 128
def gPrep (L : CuccaroStreamedSquareWideLayout) : Program :=
  addInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin
def gClear (L : CuccaroStreamedSquareWideLayout) : Program :=
  subInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin


theorem sum_lengths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (sumSrc L).length=129 ∧ L.core.sum.length=129 ∧ (sumBank L).length=128 := by
  refine ⟨?_,L.core.sum_length hw.core,?_⟩
  · simp [sumSrc,L.core.low_length hw.core]
  · simp [sumBank,hw.core.work]

theorem sumPad_mem (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    L.core.pad.getD 0 0∈L.core.pad := by
  have h : 0<L.core.pad.length := by rw [hw.core.pad]; omega
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem sum_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    (L.core.cin::(sumSrc L++L.core.sum++sumBank L)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hnd q
  have hlo := (List.take_sublist 128 L.core.y).count_le q
  have hhi1 := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
  have hhi2 := (List.drop_sublist 128 L.core.y).count_le q
  have hsplit := congrArg (List.count q) (List.take_append_drop 128 L.core.y)
  have hbit := (List.singleton_sublist.mpr (sumPad_mem L hw)).count_le q
  have hwk := (List.take_sublist 128 L.core.work).count_le q
  simp only [List.count_cons,List.count_nil,Nat.add_zero] at hbit
  simp only [List.count_append] at hsplit
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,sumSrc,sumBank,
    CuccaroStreamedSquareLayout.low,CuccaroStreamedSquareLayout.high,
    CuccaroStreamedSquareLayout.sum,List.count_append,List.count_cons,
    List.count_nil] at h ⊢
  omega

theorem sumSrc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (base : BasisState) (A : Nat)
    (hA : regValue L.core.low base=A) (hpad : regValue L.core.pad base=0) :
    regValue (sumSrc L) base=A := by
  have bit0 : base (L.core.pad.getD 0 0)=false :=
    (regValue_zero _ _).mp hpad _ (sumPad_mem L hw)
  rw [sumSrc,regValue_append,hA]
  have hz : regValue [L.core.pad.getD 0 0] base=0 := by
    change (if base (L.core.pad.getD 0 0) then 1 else 0)=0
    rw [bit0]
    rfl
  rw [hz,Nat.mul_zero,Nat.add_zero]

theorem sumBank_zero (L : CuccaroStreamedSquareWideLayout) (base : BasisState)
    (hwork : regValue L.core.work base=0) : regValue (sumBank L) base=0 :=
  (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hwork q (List.mem_of_mem_take hq))

theorem gPrep_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hbound : A+B<2^129) (hpad : regValue L.core.pad base=0)
    (hcin : base L.core.cin=false) (hwork : regValue L.core.work base=0) :
    Triple (SquareFrame L.core.sum base B) (gPrep L)
      (SquareFrame L.core.sum base (A+B)) := by
  have lens := sum_lengths L hw
  have add := addInPlace_cin_frame L.core.cin (sumSrc L) L.core.sum (sumBank L)
    (sum_nodup L hw hnd) (lens.1.trans lens.2.1.symm) (by rw [lens.2.2,lens.2.1]) base false hcin
    (sumBank_zero L base hwork) B
  have val : (B+regValue (sumSrc L) base+false.toNat)%2^L.core.sum.length=A+B := by
    rw [sumSrc_value L hw base A hA hpad,lens.2.1]
    simp only [Bool.toNat_false,Nat.add_zero]
    rw [Nat.mod_eq_of_lt (by omega),Nat.add_comm]
  rw [val] at add
  exact add

theorem gClear_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hnd : L.wires.Nodup) (base : BasisState) (A B : Nat)
    (hA : regValue L.core.low base=A) (hbound : A+B<2^129) (hpad : regValue L.core.pad base=0)
    (hcin : base L.core.cin=false) (hwork : regValue L.core.work base=0) :
    Triple (SquareFrame L.core.sum base (A+B)) (gClear L)
      (SquareFrame L.core.sum base B) := by
  have lens := sum_lengths L hw
  have nd := sum_nodup L hw hnd
  have dis (w : Wire) (hw' : w∈L.core.cin::(sumSrc L++sumBank L)) : w∉L.core.sum := by
    intro hdw
    have hn := List.nodup_iff_count.mp nd w
    have h1 := List.count_pos_iff.mpr hw'
    have h2 := List.count_pos_iff.mpr hdw
    simp only [List.count_cons,List.count_append] at hn h1
    omega
  intro s m h
  unfold gClear
  have sv : regValue (sumSrc L) s.basis=A :=
    (regValue_congr _ _ _ (fun w hw' => h.2 w (dis w (by simp [hw'])))).trans
      (sumSrc_value L hw base A hA hpad)
  have kv : regValue (sumBank L) s.basis=0 :=
    (regValue_congr _ _ _ (fun w hw' => h.2 w (dis w (by simp [hw'])))).trans (sumBank_zero L base hwork)
  have cv : s.basis L.core.cin=false := (h.2 _ (dis _ (by simp))).trans hcin
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have spec := subInPlace_spec (sumSrc L) L.core.sum (sumBank L) L.core.cin nd hx hc A (A+B) s m
    ⟨⟨⟨sv,h.1⟩,cv⟩,kv⟩
  have hv : regValue L.core.sum (run (subInPlace (sumSrc L) L.core.sum (sumBank L) L.core.cin) m s).basis=
      (A+B+2^L.core.sum.length-A)%2^L.core.sum.length := spec.2.1.1.2
  refine ⟨spec.1,?_,?_⟩
  · rw [hv,lens.2.1,show A+B+2^129-A=B+2^129 by omega,Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]
  · intro w hw'
    exact (subInPlace_frame (sumSrc L) L.core.sum (sumBank L) L.core.cin nd hx hc s m cv kv w hw').trans
      (h.2 w hw')

theorem gSum_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (toffoliCount (gPrep L)=128 ∧ measurementCount (gPrep L)=128) ∧
    (toffoliCount (gClear L)=128 ∧ measurementCount (gClear L)=128) := by
  have lens := sum_lengths L hw
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have a := addInPlace_counts (sumSrc L) L.core.sum (sumBank L) L.core.cin hx hc
  have b := subInPlace_counts (sumSrc L) L.core.sum (sumBank L) L.core.cin hx hc
  rw [lens.2.1] at a b
  exact ⟨a,b⟩

theorem gSum_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire) :
    ECDSAAdd.wires (gPrep L)⊆(control::L.wires).toFinset ∧
    ECDSAAdd.wires (gClear L)⊆(control::L.wires).toFinset := by
  have lens := sum_lengths L hw
  have hx : (sumSrc L).length=L.core.sum.length := lens.1.trans lens.2.1.symm
  have hc : (sumBank L).length+1=L.core.sum.length := by rw [lens.2.2,lens.2.1]
  have sub : (L.core.cin::(sumSrc L++L.core.sum++sumBank L)).toFinset⊆(control::L.wires).toFinset := by
    intro q hq
    have pad := sumPad_mem L hw
    have inW : q∈L.wires → q∈(control::L.wires).toFinset := fun h => by simp [h]
    apply inW
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,or_assoc,
      sumSrc,sumBank,CuccaroStreamedSquareLayout.sum] at hq
    rcases hq with h|h|h|h|h|h
    · subst h; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
    · have hy : q∈L.core.y := List.mem_of_mem_take h
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hy]
    · subst h
      simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_append,
        pad,true_or,or_true]
    · have hy : q∈L.core.y := List.mem_of_mem_drop (List.mem_of_mem_take h)
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hy]
    · subst h; simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
    · have hk : q∈L.core.work := List.mem_of_mem_take h
      simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hk]
  exact ⟨(addInPlace_wires _ _ _ _ hx hc).trans_subset sub,(subInPlace_wires _ _ _ _ hx hc).trans_subset sub⟩

theorem gSum_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hnd : L.wires.Nodup) :
    GatePhysical (gPrep L) ∧ GatePhysical (gClear L) := by
  have nd := sum_nodup L hw hnd
  exact ⟨addInPlace_physical _ _ _ _ nd,subInPlace_physical _ _ _ _ nd⟩

theorem gSum_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    Challenge.gateSlots (gPrep L)≤12*129 ∧ Challenge.gateSlots (gClear L)≤12*129+2*129 := by
  have lens := sum_lengths L hw
  have a := Baselines.addInPlace_gateSlots_le (sumSrc L) L.core.sum (sumBank L) L.core.cin
  have b := Baselines.subInPlace_gateSlots_le (sumSrc L) L.core.sum (sumBank L) L.core.cin
  rw [lens.1] at a b
  rw [lens.2.1] at b
  exact ⟨a,b⟩



/-- Fold schedules ordered so the output orientation flips as often as possible;
every flip uses the comparison-free reflected core of `QFold`. -/
def accAMixQ (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (rot128F L),.inl (negP L),.inr ⟨false,[],earlyHTerms (L.core.product.drop 128),earlyHTerms (L.core.product.drop 128)⟩]
def accBMixQ (L : CuccaroStreamedSquareWideLayout) : List MixItem :=
  [.inl (negP L),.inl (rot128F L),.inl (rotC L true 4),.inl (rotC L false 6),
    .inl (rotC L true 10),.inr ⟨false,preW L,termsB L,sortedItems false (accBRaw L)⟩,.inl (rotC L true 32)]

theorem accAMixQ_mem (L : CuccaroStreamedSquareWideLayout) (i : MixItem) (h : i∈accAMixQ L) : i∈accAMix L := by
  simp only [accAMixQ,accAMix,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; tauto
theorem accBMixQ_mem (L : CuccaroStreamedSquareWideLayout) (i : MixItem) (h : i∈accBMixQ L) : i∈accBMix L := by
  simp only [accBMixQ,accBMix,List.mem_cons,List.not_mem_nil,or_false] at h ⊢; tauto
theorem accAMixQ_sum (L : CuccaroStreamedSquareWideLayout) (t : BasisState) :
    mixSignedSum t (accAMixQ L)=mixSignedSum t (accAMix L) := by
  simp only [accAMixQ,accAMix,mixSignedSum]; ring
theorem accBMixQ_sum (L : CuccaroStreamedSquareWideLayout) (t : BasisState) :
    mixSignedSum t (accBMixQ L)=mixSignedSum t (accBMix L) := by
  simp only [accBMixQ,accBMix,mixSignedSum]; ring
theorem accQ_orientations (L : CuccaroStreamedSquareWideLayout) :
    mixFinal true (accAMixQ L)=false ∧ mixFinal false (accBMixQ L)=true ∧
    mixFinal false (accCMix L)=true := by
  simp [mixFinal,mixNeg,accAMixQ,accBMixQ,accCMix,rot128F,negP,negRot,rotC]
theorem accQ_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈accAMixQ L,MixStatic L i) ∧ (∀i∈accBMixQ L,MixStatic L i) :=
  ⟨fun i hi => (acc_static L hw).1 i (accAMixQ_mem L i hi),
    fun i hi => (acc_static L hw).2.1 i (accBMixQ_mem L i hi)⟩
theorem accQ_item_prices (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (mixFoldsQT true (accAMixQ L)=3089 ∧ mixFoldsQM true (accAMixQ L)=3092) ∧
    (mixFoldsQT false (accBMixQ L)=7049 ∧ mixFoldsQM false (accBMixQ L)=7056) ∧
    (mixFoldsQT false (accCMix L)=2646 ∧ mixFoldsQM false (accCMix L)=2647) := by
  norm_num [mixFoldsQT,mixFoldsQM,mixNeg,accAMixQ,accBMixQ,accCMix,rot128F,negP,negRot,rotF,rotC,posTop,
    accARaw,accBRaw,accCRaw,sortedItems,nafMinusOneItems,List.filter_cons,Acc.buildT,Acc.sbuildT,preW,termsB,
    accPrice,accPriceQ,earlyHTerms,Acc.earlyTerm,Acc.EarlyH,Acc.earlyBuildT,Acc.baseBuildT,hw.core.product,hiReg]
  all_goals (try rw [if_neg (List.cons_ne_nil _ _)])
  all_goals norm_num

def resAQ (P O : Nat) : Nat :=
  ofCast false (measuredOrientationCast true O+((P : ZMod SquareReduction.p)*2^128-P))
def resBQ (P O : Nat) : Nat :=
  ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-SquareReduction.c*P))

theorem acbQ_complete_exact (enabled : Bool) (A B O : Nat) :
    resBQ ((if enabled then B else 0)^2)
      (resAQ ((if enabled then A else 0)^2) (resC ((if enabled then A+B else 0)^2) O))=
      SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resC PC O
  let OA := resAQ PA OC
  let OB := resBQ PB OA
  have ec : measuredOrientationCast true OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128) :=
    cast_ofCast _ _
  have ea : measuredOrientationCast false OA=measuredOrientationCast true OC+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  have eb : measuredOrientationCast true OB=measuredOrientationCast false OA+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have obBound : OB<SquareReduction.p := ofCast_lt _ _
  have cast : (OB : ZMod SquareReduction.p)=
      -1-(subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [subModValue_cast]
    linear_combination -eb-ec-ea-identity
  have targetBound : subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p :=
    Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have hp0 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e : ((SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O : Nat) : ZMod SquareReduction.p)=
      -1-(subModValue (if enabled then (A+2^128*B)^2 else 0) O : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]),Nat.cast_one,hp0]
    ring
  have value := congrArg ZMod.val (cast.trans e.symm)
  have lt2 : SquareReduction.p-1-subModValue (if enabled then (A+2^128*B)^2 else 0) O<SquareReduction.p := by omega
  simpa only [ZMod.val_natCast_of_lt obBound,ZMod.val_natCast_of_lt lt2] using value

/-! Branch C's accumulator is folded positively. A controlled complement
`acc ← acc XOR g·(2^163-1)` turns the negative item `-acc` into the positive item
`2^163-1-acc` plus the constant `g·(2^163-1)`, so both C items switch orientation
(comparison-free `Q` folds) and the square ends in the plain orientation. The
constant is absorbed by the following `3cx` correction. -/
def cFlipK : Nat := 2^163-1

theorem xorConstant_ones (r : List Wire) : xorConstant r (2^r.length-1)=notRegister r := by
  induction r with
  | nil => rfl
  | cons w ws ih =>
    have hp : 0<2^ws.length := Nat.two_pow_pos _
    have e : 2^(ws.length+1)=2*2^ws.length := by rw [Nat.pow_succ]; ring
    have h1 : (2^(ws.length+1)-1)%2=1 := by rw [e]; omega
    have h2 : (2^(ws.length+1)-1)/2=2^ws.length-1 := by rw [e]; omega
    simp only [List.length_cons,xorConstant,h1,if_true,h2,ih,notRegister,List.map_cons]
    rfl

theorem accReg_nodup (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) : (accReg L).Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h := List.nodup_iff_count_le_one.mp hn q
  have e1 : (L.core.work.take 163).count q+(L.core.work.drop 163).count q=L.core.work.count q := by
    rw [←List.count_append,List.take_append_drop]
  simp only [accReg]
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    List.count_append,List.count_cons,List.count_nil] at h
  omega

theorem accReg_in (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq : q∈accReg L) : q∈L.wires := by
  have w := accReg_work L q hq
  simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,w]

theorem flip_run (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉accReg L) (s : State) (m : List Bool) :
    (run (maskedConstant g (accReg L) cFlipK) m s).phase=s.phase ∧
    (∀q,q∉accReg L → (run (maskedConstant g (accReg L) cFlipK) m s).basis q=s.basis q) ∧
    regValue (accReg L) (run (maskedConstant g (accReg L) cFlipK) m s).basis=
      (if s.basis g then cFlipK-regValue (accReg L) s.basis else regValue (accReg L) s.basis) := by
  have len := (acc_lengths L hw).1
  have nd := accReg_nodup L hn
  rw [maskedConstant_run g _ _ hg]
  cases hs : s.basis g
  · simp
  · have e : cFlipK=2^(accReg L).length-1 := by rw [len]; rfl
    simp only [if_true]
    rw [e,xorConstant_ones,notRegister_correct _ nd]
    refine ⟨rfl,?_,?_⟩
    · intro q hq; simp [hq]
    · change regValue (accReg L) (fun w => if w∈accReg L then !s.basis w else s.basis w)=_
      rw [regValue_congr (accReg L) _ (fun w => !s.basis w) (by intro w hw; simp [hw]),regValue_complement]

def accFoldQF (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) : Program :=
  fillIn L a++(maskedConstant g (accReg L) cFlipK++(qprog L.measuredCore SquareReduction.p++
    (maskedConstant g (accReg L) cFlipK++fillOut L a)))

theorem accFoldQF_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (g : Wire) (hg : g∉L.wires) (base : BasisState) (a : AccItem)
    (hv : AccView L base a) (hc : L.PairClean base) (O : Nat) (hO : O<SquareReduction.p) :
    Triple (SquareFrame L.core.out base O) (accFoldQF L g a)
      (SquareFrame L.core.out base (((if base g then cFlipK-Acc.accVal base 0 a.spec else Acc.accVal base 0 a.spec)+
        (SquareReduction.p-1-O))%SquareReduction.p)) := by
  intro s m hf
  have lens := acc_lengths L hw
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  let b0 := s.basis
  have prodOut := L.product_out_disjoint hn
  have auxAway (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
      L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉L.core.out :=
    (L.pairAuxAway hn q hq).2
  have gAcc : g∉accReg L := fun h => hg (accReg_in L g h)
  have gOut : g∉L.core.out := fun h => hg (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h])
  have workZero : ∀q∈L.core.work,b0 q=false := (regValue_zero _ _).mp clean.work
  have padZero : ∀q∈L.foldPad,b0 q=false := (regValue_zero _ _).mp clean.pad
  have hz : ∀q∈accZ L,b0 q=false := by
    intro q hq
    rcases accZ_mem L q hq with h|h
    · exact padZero q h
    · exact workZero q (List.mem_of_mem_drop h)
  have hb : ∀q∈accBank L,b0 q=false := fun q hq => padZero q (List.mem_of_mem_take hq)
  have hW0 : ∀q∈wTemp L,b0 q=false := fun q hq => workZero q (wTemp_work L q hq)
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := Acc.accVal base 0 a.spec
  have hA : A<2^163 := Acc.accVal_lt base 163 a.spec 0 (by norm_num) hv.specValid
  have hAK : A≤cFlipK := by unfold cFlipK; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^163 := by
    simp only [A']; split
    · unfold cFlipK; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hbuild := fillIn_triple L hw hn base a hv b0 agree0 hz hb clean.cin hW0
  rw [accFoldQF,run_append,run_append,run_append,run_append]
  let mb := measurementCount (fillIn L a)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprog L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (fillIn L a) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 163) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 163) (L.core.work.drop 163) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 163) u1.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (keepU q (by simp [hq])).trans (workZero q (List.mem_of_mem_drop hq)))
    rw [sp,hi]
    simpa [accReg] using accU1
  have outU : regValue L.core.out u1.basis=O :=
    (regValue_congr _ _ _ (fun q hq => keepU q (by simp [hq]))).trans hf.1
  have coreNd : L.measuredCore.wires.Nodup :=
    (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have hp : SquareReduction.p+SquareReduction.c=2^256 := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hAp : A'<SquareReduction.p := lt_of_lt_of_le hA' (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have carryU : ∀q∈L.measuredCore.carry,u1.basis q=false := by
    intro q hq
    simp only [measuredCore,foldCarry,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with hq|rfl|rfl
    · exact (keepU q (by simp [hq])).trans (padZero q hq)
    · exact (keepU _ (by simp)).trans clean.productHigh
    · exact (keepU _ (by simp)).trans clean.workHigh
  have ek := QCore.qprog_correct L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprog L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis else regValue (accReg L) v.basis) at fl2
  rw [gV,accV] at fl2
  have back : (if base g then cFlipK-A' else A')=A := by
    simp only [A']
    cases base g
    · simp
    · simp only [if_true]; omega
  rw [back] at fl2
  let base2 : BasisState := fun q => if q∈L.core.out then v1.basis q else b0 q
  have b2off (q : Wire) (hq : q∉L.core.out) : base2 q=b0 q := by simp [base2,hq]
  have frame2 : SquareFrame (accReg L) base2 A v1.basis := by
    refine ⟨fl2.2.2,?_⟩
    intro q hq
    by_cases ho : q∈L.core.out
    · simp [base2,ho]
    · rw [b2off q ho,fl2.2.1 q hq,ek.2.2 q ho,fl.2.1 q hq]; exact eu.2.2 q hq
  have hz2 : ∀q∈accZ L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := by
      simp only [accZ,List.mem_append] at hq
      rcases hq with hq|hq
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
      · exact auxAway q (by simp [List.mem_of_mem_drop hq])
    rw [b2off q ho]; exact hz q hq
  have hb2 : ∀q∈accBank L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [List.mem_of_mem_take hq])
    rw [b2off q ho]; exact hb q hq
  have hi2 : base2 L.core.cin=false := by
    rw [b2off _ (auxAway _ (by simp))]; exact clean.cin
  have hW2 : ∀q∈wTemp L,base2 q=false := by
    intro q hq
    have ho : q∉L.core.out := auxAway q (by simp [wTemp_work L q hq])
    rw [b2off q ho]; exact hW0 q hq
  have agree2 : ∀q∈L.core.product,base2 q=base q :=
    fun q hq => (b2off q (prodNotOut q hq)).trans (agree0 q hq)
  have hun := fillOut_triple L hw hn base a hv base2 agree2 hz2 hb2 hi2 hW2
  have eo := hun v1 (m3.drop mc) frame2
  refine ⟨eo.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have e : regValue L.core.out (run (fillOut L a) (m3.drop mc) v1).basis=
        regValue L.core.out v.basis := by
      apply regValue_congr; intro q hq
      have na : q∉accReg L := fun h => accOut q h hq
      rw [eo.2.2 q na]; simp [base2,hq,fl2.2.1 q na]
    rw [e,ek.2.1]
  · intro q hq
    by_cases ha : q∈accReg L
    · have z := (regValue_zero _ _).mp eo.2.1 q ha
      rw [z]
      exact ((regValue_zero _ _).mp hc.work q (accReg_work L q ha)).symm
    · rw [eo.2.2 q ha,b2off q hq]; exact hf.2 q hq

theorem accFoldQF_counts (L : CuccaroStreamedSquareWideLayout) (g : Wire) (a : AccItem) :
    toffoliCount (accFoldQF L g a)=toffoliCount (accFoldQ L a) ∧
    measurementCount (accFoldQF L g a)=measurementCount (accFoldQ L a) := by
  have k := maskedConstant_counts g (accReg L) cFlipK
  simp only [accFoldQF,accFoldQ,toffoliCount_append,measurementCount_append,k.1,k.2]
  constructor <;> omega

theorem accFoldQF_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    ECDSAAdd.wires (accFoldQF L g a)⊆(g::L.wires).toFinset := by
  have full := accFoldQ_support L hw hn g a cnt ok cntP okP
  simp only [accFoldQ,wires_append,Finset.union_subset_iff] at full
  have mc : ECDSAAdd.wires (maskedConstant g (accReg L) cFlipK)⊆(g::L.wires).toFinset := by
    refine (maskedConstant_wires_subset _ _ _).trans ?_
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons] at hq ⊢
    rcases hq with h|h
    · exact Or.inl h
    · exact Or.inr (accReg_in L q h)
  simp only [accFoldQF,wires_append,Finset.union_subset_iff]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩

theorem accFoldQF_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires)
    (a : AccItem) (cnt : ∀f∈a.terms,SrcOK L f) (ok : ∀f∈a.terms,TermOK f)
    (cntP : ∀f∈a.pre,∀q,f.src.count q≤L.core.product.count q) (okP : ∀f∈a.pre,TermOK33 f) :
    GatePhysical (accFoldQF L g a) := by
  have full := accFoldQ_physical L hw hn a cnt ok cntP okP
  simp only [accFoldQ,gatePhysical_append] at full
  have mc := maskedConstant_physical g (accReg L) cFlipK (fun h => hg (accReg_in L g h))
  simp only [accFoldQF,gatePhysical_append]
  exact ⟨full.1.1,mc,full.1.2,mc,full.2⟩

theorem accFoldQF_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) (a : AccItem)
    (ok : ∀f∈a.terms,TermOK f) (okP : ∀f∈a.pre,TermOK33 f) :
    Challenge.gateSlots (accFoldQF L g a)≤
      2*(a.terms.length*(14*163))+4*(a.pre.length*(14*33))+(67*256+41)+7000+2*163 := by
  have full := accFoldQ_gateSlots L hw a ok okP
  have mc := Baselines.maskedConstant_gateSlots_le g (accReg L) cFlipK
  rw [(acc_lengths L hw).1] at mc
  simp only [accFoldQ,Challenge.gateSlots_append] at full
  simp only [accFoldQF,Challenge.gateSlots_append]
  omega

def accCItem (L : CuccaroStreamedSquareWideLayout) : AccItem :=
  ⟨true,[],earlyHTerms (L.core.product.drop 128)++[posTop L],earlyHTerms (L.core.product.drop 128)++[posTop L]⟩

theorem accCMix_eq (L : CuccaroStreamedSquareWideLayout) : accCMix L=[.inl (negRot L),.inr (accCItem L)] := rfl

/-- Branch C body: `negRot` by the switching fold, then the complemented accumulator, also switching. -/
def bodyC (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
  mixFoldsQ L false [.inl (negRot L)]++accFoldQF L g (accCItem L)

theorem bodyC_static (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
    (∀i∈[(.inl (negRot L) : MixItem)],MixStatic L i) ∧ MixStatic L (.inr (accCItem L)) := by
  have st := (acc_static L hw).2.2
  rw [accCMix_eq] at st
  exact ⟨fun i hi => st i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; exact Or.inl hi),
    st _ (by simp)⟩

theorem bodyC_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    toffoliCount (bodyC L g)=2390 ∧ measurementCount (bodyC L g)=2392 := by
  have st := bodyC_static L hw
  have nR : (negRot L).negative=true := rfl
  have cR : (negRot L).canonical=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have f := mixFoldsQ_counts L hw false _ st.1
  have f1 : mixFoldsQT false [(.inl (negRot L) : MixItem)]=767 := by simp [mixFoldsQT,mixNeg,nR,cR]
  have f2 : mixFoldsQM false [(.inl (negRot L) : MixItem)]=768 := by simp [mixFoldsQM,mixNeg,nR,cR]
  have q := accFoldQ_counts L hw (accCItem L) st.2.2.1 st.2.2.2.2
  have qf := accFoldQF_counts L g (accCItem L)
  have pr := (accQ_item_prices L hw).2.2
  rw [accCMix_eq] at pr
  simp [mixFoldsQT,mixFoldsQM,mixNeg,nR,cR,nC] at pr
  have rel : accPriceQ (accCItem L)+256=accPrice (accCItem L) := by simp only [accPriceQ,accPrice]; omega
  rw [bodyC]
  simp only [toffoliCount_append,measurementCount_append]
  rw [f.1,f.2,qf.1,qf.2,q.1,q.2,f1,f2]
  constructor <;> omega

theorem bodyC_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup) (g : Wire) :
    ECDSAAdd.wires (bodyC L g)⊆(g::L.wires).toFinset := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_support L hw hn g false _ st.1
  have b := accFoldQF_support L hw hn g (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyC,wires_append,Finset.union_subset_iff]
  exact ⟨a,b⟩

theorem bodyC_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (g : Wire) (hg : g∉L.wires) : GatePhysical (bodyC L g) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_physical L hw hn false _ st.1
  have b := accFoldQF_physical L hw hn g hg (accCItem L) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2
  simp only [bodyC,gatePhysical_append]
  exact ⟨a,b⟩

theorem bodyC_gateSlots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (g : Wire) :
    Challenge.gateSlots (bodyC L g)≤2*(41000+2*(20*(14*163))+(67*256+41)) := by
  have st := bodyC_static L hw
  have a := mixFoldsQ_gateSlots L hw false _ st.1 20 (by intro i hi a e; simp at hi; subst hi; cases e)
  have b := accFoldQF_gateSlots L hw g (accCItem L) st.2.2.1 st.2.2.2.2
  have lt : (accCItem L).terms.length=5 := by simp [accCItem,earlyHTerms]
  have lp : (accCItem L).pre.length=0 := rfl
  rw [lt,lp] at b
  simp only [List.length_singleton] at a
  simp only [bodyC,Challenge.gateSlots_append]
  omega

/-- C contribution with the complemented accumulator: plain orientation, plus `g·(2^163-1)`. -/
def resCF (g : Bool) (P O : Nat) : Nat :=
  ofCast false (measuredOrientationCast false O+(-(P : ZMod SquareReduction.p)*2^128)+
    ((if g then cFlipK else 0 : Nat) : ZMod SquareReduction.p))

theorem accC_zero (L : CuccaroStreamedSquareWideLayout) (t : BasisState) (hp : regValue L.core.product t=0) :
    Acc.accVal t 0 (accCItem L).spec=0 := by
  have z := (regValue_zero _ _).mp hp
  have h128 : regValue (L.core.product.drop 128) t=0 :=
    (regValue_zero _ _).mpr (fun q hq => z q (List.mem_of_mem_drop hq))
  have h256 : regValue (L.core.product.drop 256) t=0 :=
    (regValue_zero _ _).mpr (fun q hq => z q (List.mem_of_mem_drop hq))
  simp [accCItem,Acc.accVal,Acc.step,earlyHTerms,Acc.earlyTerm,posTop,h128,h256]

theorem accMiddleCF_body (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (M O : Nat) (hO : O<SquareReduction.p)
    (t : State) (m : List Bool) (pv : regValue L.core.product t.basis=M^2)
    (hM : t.basis control=false → M=0)
    (clean : L.PairClean t.basis) (outO : regValue L.core.out t.basis=O) :
    (run (bodyC L control) m t).phase=t.phase ∧
    regValue L.core.out (run (bodyC L control) m t).basis=resCF (t.basis control) (M^2) O ∧
    ∀q,q∉L.core.out → (run (bodyC L control) m t).basis q=t.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have gW : control∉L.wires := (List.nodup_cons.mp hn).1
  have views := accC_views L hw t.basis M pv
  rw [accCMix_eq] at views
  have v1 : ∀i∈[(.inl (negRot L) : MixItem)],MixView L t.basis i := fun i hi => views i (by simp at hi ⊢; exact Or.inl hi)
  have va : AccView L t.basis (accCItem L) := views (.inr (accCItem L)) (by simp)
  let mm := measurementCount (mixFoldsQ L false [.inl (negRot L)])
  let r1 := run (mixFoldsQ L false [.inl (negRot L)]) (m.take mm) t
  have e1 := mixFoldsQ_frame L hw nd t.basis clean false O hO [.inl (negRot L)] v1 t (m.take mm) ⟨outO,fun _ _ => rfl⟩
  let O1 := mixValue t.basis false O [.inl (negRot L)]
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have e2 := accFoldQF_frame L hw nd control gW t.basis (accCItem L) va clean O1 hO1 r1 (m.drop mm) e1.2
  rw [bodyC,run_append]
  refine ⟨e2.1.trans e1.1,?_,fun q hq => e2.2.2 q hq⟩
  rw [e2.2.1]
  have nR : (negRot L).negative=true := rfl
  have nC : (accCItem L).negative=true := rfl
  have cast1 := mixValue_cast t.basis false O [.inl (negRot L)] hO
  have sum := (accC_mixSum L hw t.basis).trans (L.measuredC_sum hw t.basis (M^2) pv)
  rw [accCMix_eq] at sum
  simp only [mixFinal,mixNeg,nR,nC,mixSignedSum,mixSignedPayload,mixPayload,↓reduceIte,add_zero] at cast1 sum
  simp only [measuredOrientationCast,↓reduceIte,Bool.false_eq_true] at cast1
  have hA : Acc.accVal t.basis 0 (accCItem L).spec<2^163 := Acc.accVal_lt _ 163 _ 0 (by norm_num) va.specValid
  set A := Acc.accVal t.basis 0 (accCItem L).spec with hAdef
  set O1 := mixValue t.basis false O [.inl (negRot L)] with hO1def
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have hp1 : ((SquareReduction.p : Nat) : ZMod SquareReduction.p)=0 := ZMod.natCast_self _
  have e3 : ((SquareReduction.p-1-O1 : Nat) : ZMod SquareReduction.p)=-1-(O1 : ZMod SquareReduction.p) := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one,hp1]; ring
  have target : ((((if t.basis control then cFlipK-A else A)+(SquareReduction.p-1-O1)) : Nat) : ZMod SquareReduction.p)=
      measuredOrientationCast false O+(-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)+
        ((if t.basis control then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := by
    simp only [measuredOrientationCast,Bool.false_eq_true,↓reduceIte]
    cases hg : t.basis control
    · have m0 := hM hg
      have a0 : A=0 := by
        have pz : regValue L.core.product t.basis=0 := by rw [pv,m0]; rfl
        exact accC_zero L t.basis pz
      simp only [Bool.false_eq_true,↓reduceIte]
      rw [Nat.cast_add,e3,a0,Nat.cast_zero]
      rw [a0,Nat.cast_zero] at sum
      linear_combination cast1+sum
    · have hAK : A≤cFlipK := by unfold cFlipK; omega
      simp only [↓reduceIte]
      rw [Nat.cast_add,Nat.cast_sub hAK,e3]
      linear_combination cast1+sum
  unfold resCF ofCast
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [←target,ZMod.val_natCast]

def accBranchAK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagLowK.withLowK2 L ext control L.core.low (L.core.product.take 256) (mixFoldsQ L true (accAMixQ L))
def accBranchBK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagLowK.withLowK2 L ext control L.core.high (L.core.product.take 256) (mixFoldsQ L false (accBMixQ L))
def accMiddleCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  OwnDiagLowK.withLowK2 L ext control L.core.sum L.core.product (bodyC L control)
def accBranchCK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  gPrep L++accMiddleCK L ext control++gClear L
def accPrefixK (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) : Program :=
  accBranchCK L ext control++accBranchBK L ext control++accBranchAK L ext control

theorem accBranchAK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (ha : regValue L.core.low s.basis=A)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchAK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchAK L ext control) records s).basis=
      resAQ ((if s.basis control then A else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchAK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then A else 0
  have ab : A<2^128 := by simpa [L.core.low_length hw.core,ha] using regValue_lt L.core.low s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.low.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixedK_contribution L hw ext control hn L.core.low (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.low_length hw.core]) (by simp [L.core.low_length hw.core])
    (by simp [hw.core.product,L.core.low_length hw.core]) true (accAMixQ L) s records hc dstZero
    O (M^2) (resAQ (M^2) O) hO ho (by rw [ha])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp i hi => accA_views L hw t M mb hp i (accAMixQ_mem L i hi))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accAMixQ_sum L t).trans ((accA_mixSum L hw t).trans (L.measuredA_sum hw t (M^2) hp pb)))
    (ofCast_lt _ _) (by
      rw [(accQ_orientations L).1]
      exact cast_ofCast _ _) he hz (accQ_static L hw).1
  exact result

theorem accBranchBK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (B O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=B)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchBK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchBK L ext control) records s).basis=
      resBQ ((if s.basis control then B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchBK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then B else 0
  have bb : B<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have pb : M^2<2^256 := by simpa using square_bound M 128 mb
  have srcCount (q : Wire) : L.core.high.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (L.core.product.take 256).count q≤L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have result := withMixedK_contribution L hw ext control hn L.core.high (L.core.product.take 256)
    srcCount dstCount (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) false (accBMixQ L) s records hc dstZero
    O (M^2) (resBQ (M^2) O) hO ho (by rw [hb])
    (fun t hp same => L.measured_partial_product_value (List.nodup_cons.mp hn).2 s.basis t hp0 (M^2) hp same)
    (fun t hp i hi => accB_views L hw t M mb hp i (accBMixQ_mem L i hi))
    (((M^2 : Nat) : ZMod SquareReduction.p)*2^128-SquareReduction.c*((M^2 : Nat) : ZMod SquareReduction.p))
    (fun t hp => (accBMixQ_sum L t).trans ((accB_mixSum L hw t (M^2) hp pb).trans (L.measuredB_sum hw t (M^2) hp pb)))
    (ofCast_lt _ _) (by
      rw [(accQ_orientations L).2.1]
      exact cast_ofCast _ _) he hz (accQ_static L hw).2
  exact result

theorem accMiddleCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (S O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hs : regValue L.core.sum s.basis=S)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accMiddleCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accMiddleCK L ext control) records s).basis=
      resCF (s.basis control) ((if s.basis control then S else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accMiddleCK L ext control) records s).basis q=s.basis q := by
  let M := if s.basis control then S else 0
  have nd := (List.nodup_cons.mp hn).2
  have srcCount (q : Wire) : L.core.sum.count q≤(L.core.y++[L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (L.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.sum,CuccaroStreamedSquareLayout.high,List.count_append] at h ⊢
    omega
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires (bodyC L control) := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (bodyC_support L hw nd control hw'))
  apply OwnDiagLowK.withLowK2_correct L hw control hn L.core.sum L.core.product srcCount (fun _ => le_rfl)
    (by simp [L.core.sum_length hw.core]) (by simp [L.core.sum_length hw.core])
    (by simp [hw.core.product,L.core.sum_length hw.core]) ext he.nodup he.away he.len (bodyC L control) hbody
    s records hc hp0 hz
  intro t m dstValue same
  have ctrlT : t.basis control=s.basis control :=
    same control (fun h => (List.nodup_cons.mp hn).1
      (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]))
  have pv : regValue L.core.product t.basis=M^2 := by simpa [M,hs] using dstValue
  have clean := L.measured_product_frame_clean nd L.core.product (fun _ => le_rfl) s.basis t.basis hc same
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q
      (fun hp => List.disjoint_left.mp (L.product_out_disjoint nd) hp hq))).trans ho
  have r := accMiddleCF_body L hw control hn M O hO t m pv
    (by intro h; rw [ctrlT] at h; simp [M,h]) clean outO
  rw [ctrlT] at r
  exact r

theorem accBranchCK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (A B O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (hb : regValue L.core.sum s.basis=B)
    (bound : A+B<2^129) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accBranchCK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accBranchCK L ext control) records s).basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
    ∀q,q∉L.core.out → (run (accBranchCK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have dis := L.measured_sum_disjoint nd
  have ctrlAway : control∉L.core.sum := by
    intro bad
    have h := List.nodup_iff_count.mp hn control
    have pos := List.count_pos_iff.mpr bad
    have sumBound := L.measured_sum_count control
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,
      List.count_nil,beq_self_eq_true,if_true] at h sumBound
    omega
  let middle := accMiddleCK L ext control
  let mp := measurementCount (gPrep L)
  let rest := records.drop mp
  let u := run (gPrep L) (records.take mp) s
  let v := run middle (rest.take (measurementCount middle)) u
  let out := run (gClear L) (rest.drop (measurementCount middle)) v
  have prep := gPrep_frame L hw nd s.basis A B ha bound (PairClean.corePad L s.basis hc) hc.cin hc.work
    s (records.take mp) (show SquareFrame L.core.sum s.basis B s.basis from ⟨hb,fun _ _ => rfl⟩)
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.1 bad hq))).trans hp0
  have outU : regValue L.core.out u.basis=O :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq))).trans ho
  have ctrlU : u.basis control=s.basis control := prep.2.2 control ctrlAway
  have cleanU : L.PairClean u.basis := by
    have keep (q : Wire) (hq : q∈L.foldPad++L.core.work++[L.core.productHigh,L.core.outHigh,
        L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : u.basis q=s.basis q :=
      prep.2.2 q (L.measured_sum_aux_away nd q hq)
    constructor
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.pad
    · exact (regValue_congr _ _ _ (fun q hq => keep q (by simp [hq]))).trans hc.work
    · exact (keep _ (by simp)).trans hc.productHigh
    · exact (keep _ (by simp)).trans hc.outHigh
    · exact (keep _ (by simp)).trans hc.workHigh
    · exact (keep _ (by simp)).trans hc.cin
    · exact (keep _ (by simp)).trans hc.normFlag
    · exact (keep _ (by simp)).trans hc.modFlag
  have hzU : regValue ext u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => prep.2.2 q (fun bad => he.away q hq (sum_in L control q bad)))).trans hz
  have used := accMiddleCK_correct L hw ext control hn (A+B) O hO u
    (rest.take (measurementCount middle)) prep.2.1 outU productU cleanU he hzU
  rw [ctrlU] at used
  let restoreBase : BasisState := fun q => if q∈L.core.out then v.basis q else s.basis q
  have lowOutAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out := by
    intro bad
    have h := List.nodup_iff_count.mp nd q
    have a := List.count_pos_iff.mpr (List.mem_of_mem_take hq)
    have b := List.count_pos_iff.mpr bad
    simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.count_append,List.count_cons,List.count_nil] at h
    omega
  have lowRestore : regValue L.core.low restoreBase=A := by
    apply Eq.trans (regValue_congr _ _ _ ?_) ha
    intro q hq
    simp [restoreBase,lowOutAway q hq]
  have sumRestore : regValue L.core.sum restoreBase=B := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    simp [restoreBase,List.disjoint_left.mp dis.2 hq]
  have padRestore : regValue L.core.pad restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) (PairClean.corePad L s.basis hc)
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [CuccaroStreamedSquareWideLayout.foldPad,hq])).2
    simp [restoreBase,away]
  have cinRestore : restoreBase L.core.cin=false := by
    have away := (L.pairAuxAway nd L.core.cin (by simp)).2
    simp [restoreBase,away,hc.cin]
  have clearPre : SquareFrame L.core.sum restoreBase (A+B) v.basis := by
    refine ⟨?_,?_⟩
    · exact (regValue_congr _ _ _ (fun q hq => used.2.2 q (List.disjoint_left.mp dis.2 hq))).trans prep.2.1
    · intro q hq
      by_cases outSite : q∈L.core.out
      · simp [restoreBase,outSite]
      · simp only [restoreBase,if_neg outSite]
        exact (used.2.2 q outSite).trans (prep.2.2 q hq)
  have workRestore : regValue L.core.work restoreBase=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hc.work
    intro q hq
    have away := (L.pairAuxAway nd q (by simp [hq])).2
    simp [restoreBase,away]
  have cleared := gClear_frame L hw nd restoreBase A B lowRestore bound padRestore cinRestore workRestore
    v (rest.drop (measurementCount middle)) clearPre
  have finalValue : regValue L.core.out out.basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O := by
    apply Eq.trans (regValue_congr _ _ _ ?_) used.2.1
    intro q hq
    have same := cleared.2.2 q (fun bad => List.disjoint_left.mp dis.2 bad hq)
    simpa [restoreBase,hq] using same
  have final : out.phase=s.phase ∧ regValue L.core.out out.basis=
      resCF (s.basis control) ((if s.basis control then A+B else 0)^2) O ∧
      ∀q,q∉L.core.out → out.basis q=s.basis q := by
    refine ⟨cleared.1.trans (used.1.trans prep.1),finalValue,?_⟩
    intro q hq
    by_cases sumSite : q∈L.core.sum
    · exact (regValue_eq_iff L.core.sum out.basis s.basis).mp (cleared.2.1.trans hb.symm) q sumSite
    · have same := cleared.2.2 q sumSite
      simpa [restoreBase,hq] using same
  simpa [accBranchCK,middle,u,v,out,rest,mp,run_append] using final

theorem cbaF_complete_exact (enabled : Bool) (A B O : Nat) :
    resAQ ((if enabled then A else 0)^2)
      (resBQ ((if enabled then B else 0)^2) (resCF enabled ((if enabled then A+B else 0)^2) O))=
      (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p := by
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resCF enabled PC O
  let OB := resBQ PB OC
  let OA := resAQ PA OB
  have ec : measuredOrientationCast false OC=measuredOrientationCast false O+(-(PC : ZMod SquareReduction.p)*2^128)+
      ((if enabled then cFlipK else 0 : Nat) : ZMod SquareReduction.p) := cast_ofCast _ _
  have eb : measuredOrientationCast true OB=measuredOrientationCast false OC+
      ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB) := cast_ofCast _ _
  have ea : measuredOrientationCast false OA=measuredOrientationCast true OB+((PA : ZMod SquareReduction.p)*2^128-PA) :=
    cast_ofCast _ _
  simp only [measuredOrientationCast,Bool.false_eq_true,if_false,if_true] at ea eb ec
  have identity := measured_controlled_square_identity enabled A B
  change (PA : ZMod SquareReduction.p)*2^128-PA+
    ((PB : ZMod SquareReduction.p)*2^128-SquareReduction.c*PB)-(PC : ZMod SquareReduction.p)*2^128=
      -((if enabled then (A+2^128*B)^2 else 0 : Nat) : ZMod SquareReduction.p) at identity
  have oaBound : OA<SquareReduction.p := ofCast_lt _ _
  have targetBound : (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p<
      SquareReduction.p := Nat.mod_lt _ (by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c])
  have cast : (OA : ZMod SquareReduction.p)=
      (((subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then cFlipK else 0))%SquareReduction.p : Nat) :
        ZMod SquareReduction.p) := by
    rw [ZMod.natCast_mod,Nat.cast_add,subModValue_cast]
    linear_combination ea+eb+ec+identity
  have value := congrArg ZMod.val cast
  simpa only [ZMod.val_natCast_of_lt oaBound,ZMod.val_natCast_of_lt targetBound] using value

theorem accPrefixK_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Y O : Nat)
    (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (hy : regValue L.core.y s.basis=Y) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hs0 : s.basis L.core.sumCarry=false)
    (hc : L.PairClean s.basis)
    (he : ExtOK L control ext) (hz : regValue ext s.basis=0) :
    (run (accPrefixK L ext control) records s).phase=s.phase ∧
    regValue L.core.out (run (accPrefixK L ext control) records s).basis=
      ((O+SquareReduction.p-(if s.basis control then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if s.basis control then cFlipK else 0))%SquareReduction.p ∧
    ∀q,q∉L.core.out → (run (accPrefixK L ext control) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have disInput := L.measured_input_out_disjoint nd
  have disProduct := L.product_out_disjoint nd
  have ctrlAway : control∉L.core.out := by
    intro bad
    exact (List.nodup_cons.mp hn).1 (by simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,bad])
  let A := regValue L.core.low s.basis
  let B := regValue L.core.high s.basis
  let enabled := s.basis control
  let PA := (if enabled then A else 0)^2
  let PB := (if enabled then B else 0)^2
  let PC := (if enabled then A+B else 0)^2
  let OC := resCF enabled PC O
  let OB := resBQ PB OC
  let OA := resAQ PA OB
  let restC := records.drop (measurementCount (accBranchCK L ext control))
  let restB := restC.drop (measurementCount (accBranchBK L ext control))
  let u := run (accBranchCK L ext control) (records.take (measurementCount (accBranchCK L ext control))) s
  let v := run (accBranchBK L ext control) (restC.take (measurementCount (accBranchBK L ext control))) u
  let w := run (accBranchAK L ext control) restB v
  have lowAway (q : Wire) (hq : q∈L.core.low) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_take hq))
  have highAway (q : Wire) (hq : q∈L.core.high) : q∉L.core.out :=
    List.disjoint_left.mp disInput (List.mem_append_left _ (List.mem_of_mem_drop (List.mem_of_mem_take hq)))
  have sumB : regValue L.core.sum s.basis=B := by
    simp [CuccaroStreamedSquareLayout.sum,regValue_append,regValue,hs0,B]
  have ab : A<2^128 := by simpa [A,L.core.low_length hw.core] using regValue_lt L.core.low s.basis
  have bb : B<2^128 := by simpa [B,L.core.high_length hw.core] using regValue_lt L.core.high s.basis
  have sumBound : A+B<2^129 := by norm_num at ab bb ⊢;omega
  have ec := accBranchCK_correct L hw ext control hn A B O hO s
    (records.take (measurementCount (accBranchCK L ext control))) rfl sumB sumBound ho hp0 hc he hz
  have cleanU : L.PairClean u.basis :=
    L.squareFrame_clean nd s.basis u.basis OC ⟨ec.2.1,ec.2.2⟩ hc
  have productU : regValue L.core.product u.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => ec.2.2 q (List.disjoint_left.mp disProduct hq))).trans hp0
  have highU : regValue L.core.high u.basis=B := regValue_congr _ _ _ (fun q hq => ec.2.2 q (highAway q hq))
  have ctrlU : u.basis control=enabled := ec.2.2 control ctrlAway
  have eb := accBranchBK_correct L hw ext control hn B OC (ofCast_lt _ _) u
    (restC.take (measurementCount (accBranchBK L ext control))) highU ec.2.1 productU cleanU he
    ((regValue_congr _ _ _ (fun q hq => ec.2.2 q (ext_out L control ext he q hq))).trans hz)
  rw [ctrlU] at eb
  have sameV (q : Wire) (hq : q∉L.core.out) : v.basis q=s.basis q :=
    (eb.2.2 q hq).trans (ec.2.2 q hq)
  have cleanV : L.PairClean v.basis :=
    L.squareFrame_clean nd s.basis v.basis OB ⟨eb.2.1,sameV⟩ hc
  have productV : regValue L.core.product v.basis=0 :=
    (regValue_congr _ _ _ (fun q hq => sameV q (List.disjoint_left.mp disProduct hq))).trans hp0
  have lowV : regValue L.core.low v.basis=A :=
    regValue_congr _ _ _ (fun q hq => sameV q (lowAway q hq))
  have ctrlV : v.basis control=enabled := sameV control ctrlAway
  have ea := accBranchAK_correct L hw ext control hn A OB (ofCast_lt _ _) v restB lowV eb.2.1 productV cleanV he
    ((regValue_congr _ _ _ (fun q hq => sameV q (ext_out L control ext he q hq))).trans hz)
  rw [ctrlV] at ea
  have sameW (q : Wire) (hq : q∉L.core.out) : w.basis q=s.basis q := (ea.2.2 q hq).trans (sameV q hq)
  have split : A+2^128*B=Y := by
    have highEq : L.core.high=L.core.y.drop 128 := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
    have value := regValue_append (L.core.y.take 128) (L.core.y.drop 128) s.basis
    rw [List.take_append_drop,hy,List.length_take,hw.core.y] at value
    simpa only [A,B,CuccaroStreamedSquareLayout.low,highEq,show min 128 256=128 by decide] using value.symm
  have fullValue : regValue L.core.out w.basis=
      ((O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if enabled then cFlipK else 0))%SquareReduction.p := by
    have exactResult := cbaF_complete_exact enabled A B O
    rw [split] at exactResult
    unfold subModValue at exactResult
    rw [ea.2.1]
    exact exactResult
  have final : w.phase=s.phase ∧ regValue L.core.out w.basis=
      ((O+SquareReduction.p-(if enabled then Y^2 else 0)%SquareReduction.p)%SquareReduction.p+
        (if enabled then cFlipK else 0))%SquareReduction.p ∧
      ∀q,q∉L.core.out → w.basis q=s.basis q :=
    ⟨ea.1.trans (eb.1.trans ec.1),fullValue,sameW⟩
  simpa [accPrefixK,u,v,w,restB,restC,enabled,run_append,Nat.add_assoc] using final


theorem accPrefixK_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire)
    (control : Wire) (he : 300≤ext.length) :
    toffoliCount (accPrefixK L ext control)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13554 ∧ measurementCount (accPrefixK L ext control)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13566 := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have lo := L.core.low_length hw.core
  have hi := L.core.high_length hw.core
  have su := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_counts L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) (by omega) (by omega) (by omega) he
  have b := OwnDiagLowK.withLowK2_counts L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) (by omega) (by omega) (by omega) he
  have c := OwnDiagLowK.withLowK2_counts L hw ext control L.core.sum L.core.product
    (bodyC L control) (by omega) (by omega) (by rw [hw.core.product,su]) he
  have fa := mixFoldsQ_counts L hw true (accAMixQ L) stQ.1
  have fb := mixFoldsQ_counts L hw false (accBMixQ L) stQ.2
  have fc := bodyC_counts L hw control
  have prices := accQ_item_prices L hw
  rw [prices.1.1,prices.1.2] at fa
  rw [prices.2.1.1,prices.2.1.2] at fb
  have sum := gSum_counts L hw
  rw [lo] at a
  rw [hi] at b
  rw [su] at c
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,toffoliCount_append,
    measurementCount_append,a.1,a.2,b.1,b.2,c.1,c.2,fa.1,fa.2,fb.1,fb.2,fc.1,fc.2,
    sum.1.1,sum.1.2,sum.2.1,sum.2.2]
  constructor <;> omega

theorem accPrefixK_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    ECDSAAdd.wires (accPrefixK L ext control)⊆(control::L.wires++ext).toFinset := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have a := mixFoldsQ_support L hw hn control true (accAMixQ L) stQ.1
  have b := mixFoldsQ_support L hw hn control false (accBMixQ L) stQ.2
  have c := bodyC_support L hw hn control
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have sa := OwnDiagLowK.withLowK2_support L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) hl hp (by omega) (by omega) (by omega) he a
  have sb := OwnDiagLowK.withLowK2_support L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) hb hp (by omega) (by omega) (by omega) he b
  have sc := OwnDiagLowK.withLowK2_support L hw ext control L.core.sum L.core.product
    (bodyC L control) hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) he c
  have embed : (control::L.wires).toFinset⊆(control::L.wires++ext).toFinset := by
    intro q hq; simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢; tauto
  have prep := (gSum_support L hw control).1.trans embed
  have unprep := (gSum_support L hw control).2.trans embed
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,wires_append,
    Finset.union_subset_iff]
  exact ⟨⟨⟨⟨prep,sc⟩,unprep⟩,sb⟩,sa⟩

theorem accPrefixK_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control :: L.wires).Nodup) (he : ExtOK L control ext) :
    GatePhysical (accPrefixK L ext control) := by
  have nd := (List.nodup_cons.mp hn).2
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have hl (q : Wire) : L.core.low.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 L.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.low,List.count_append] at h ⊢; omega
  have hh (q : Wire) : L.core.high.count q ≤ L.core.y.count q :=
    ((List.take_sublist 128 (L.core.y.drop 128)).count_le q).trans
      ((List.drop_sublist 128 L.core.y).count_le q)
  have hb (q : Wire) : L.core.high.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [List.count_append]; omega
  have hs (q : Wire) : L.core.sum.count q ≤ (L.core.y ++ [L.core.sumCarry]).count q := by
    have h := hh q; simp only [CuccaroStreamedSquareLayout.sum,List.count_append]; omega
  have hp (q : Wire) : (L.core.product.take 256).count q ≤ L.core.product.count q :=
    (List.take_sublist 256 L.core.product).count_le q
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hl hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (mixFoldsQ_physical L hw nd true (accAMixQ L) stQ.1)
  have b := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hb hp (by omega) (by omega) (by omega)
    ext he.nodup he.away he.len _ (mixFoldsQ_physical L hw nd false (accBMixQ L) stQ.2)
  have c := OwnDiagLowK.withLowK2_physical L hw control hn _ _ hs (fun _ => le_rfl) (by omega) (by omega)
    (by rw [hw.core.product,sum]) ext he.nodup he.away he.len _
    (bodyC_physical L hw nd control (List.nodup_cons.mp hn).1)
  have prep := (gSum_physical L hw nd).1
  have clear := (gSum_physical L hw nd).2
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,gatePhysical_append]
  exact ⟨⟨⟨⟨prep,c⟩,clear⟩,b⟩,a⟩

theorem accPrefixK_gateSlots_le (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (he : 300≤ext.length) :
    Challenge.gateSlots (accPrefixK L ext control) ≤ 8000000 := by
  have st := acc_static L hw
  have stQ := accQ_static L hw
  have bd (items : List MixItem) (h : items=accAMixQ L ∨ items=accBMixQ L ∨ items=accCMix L) :
      ∀i∈items,∀a,i=.inr a → a.terms.length≤20 ∧ a.pre.length≤4 := by
    intro i hi a e
    subst e
    rcases h with rfl|rfl|rfl <;>
      simp [accAMixQ,accBMixQ,accCMix] at hi <;> rw [hi] <;>
      simp [sortedItems,accARaw,accBRaw,accCRaw,termsB,earlyHTerms,Acc.earlyTerm,preW,nafMinusOneItems,List.filter_cons,posTop]
  have ha := mixFoldsQ_gateSlots L hw true (accAMixQ L) stQ.1 20 (bd _ (Or.inl rfl))
  have hb := mixFoldsQ_gateSlots L hw false (accBMixQ L) stQ.2 20 (bd _ (Or.inr (Or.inl rfl)))
  have hc := bodyC_gateSlots L hw control
  have la : (accAMixQ L).length = 3 := rfl
  have lb : (accBMixQ L).length = 7 := rfl
  have lc : (accCMix L).length = 2 := rfl
  rw [la] at ha
  rw [lb] at hb
  have low := L.core.low_length hw.core
  have high := L.core.high_length hw.core
  have sum := L.core.sum_length hw.core
  have p256 : (L.core.product.take 256).length=256 := by simp [hw.core.product]
  have a := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.low (L.core.product.take 256)
    (mixFoldsQ L true (accAMixQ L)) (by omega) (by omega) (by omega) he
  have b := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.high (L.core.product.take 256)
    (mixFoldsQ L false (accBMixQ L)) (by omega) (by omega) (by omega) he
  have c := OwnDiagLowK.withLowK2_gateSlots_le L hw ext control L.core.sum L.core.product
    (bodyC L control) (by omega) (by omega) (by rw [hw.core.product,sum]) he
  have gs := gSum_gateSlots L hw
  simp only [accPrefixK,accBranchAK,accBranchBK,accBranchCK,accMiddleCK,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.OwnDiagAll12Square

end

section
-- ===== FastSquare =====

/-! Point-layout binding of the sign-grouped streamed square, with the same
pool relabeling as the Skywalk Step 4 square. -/

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace ECDSAAdd.Entrant.OwnDiagAll12Square
open Arithmetic ControlledPointLayout Secp256k1 CompressedPointSquare

/-- Zero pool sites 978..1028, 1284..1529 and 1533..1535: in the
certified site inventory, outside the square's placed prefix, fixed by its pool permutations. -/
def kext (L : ControlledPointLayout) : List Wire :=
  wireBlock L.core.poolWire 978 51++wireBlock L.core.poolWire 1284 246++wireBlock L.core.poolWire 1533 3

theorem kext_index (L : ControlledPointLayout) (q : Wire) (hq : q∈kext L) :
    ∃i,978 ≤ i ∧ i < 1536 ∧ (i < 1029 ∨ (1284 ≤ i ∧ i < 1530) ∨ 1533 ≤ i) ∧ q=L.core.poolWire i := by
  rcases List.mem_append.mp hq with h|h
  · rcases List.mem_append.mp h with h|h <;> obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h <;>
      simp only [List.mem_range'_1] at hj <;> exact ⟨j,by omega,by omega,by omega,rfl⟩
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    exact ⟨j,by omega,by omega,by omega,rfl⟩

theorem dialogPool_nodup' (L : ControlledPointLayout) (hn : L.wires.Nodup) : L.dialogPool.Nodup :=
  (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.1

theorem kpool_block (L : ControlledPointLayout) (hw : L.Widths) :
    L.dialogPool.take 2613=wireBlock L.core.poolWire 0 2613 := by
  simp only [dialogPool,List.take_take,Nat.min_self]
  exact (L.core.pool_prefix hw 2613 (by omega)).symm

theorem kpool_inj (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (i j : Nat) (hi : i < 2613) (hj : j < 2613)
    (h : L.core.poolWire i = L.core.poolWire j) : i = j := by
  have nd : (wireBlock L.core.poolWire 0 2613).Nodup := by
    rw [← kpool_block L hw]
    exact (List.take_sublist _ _).nodup (dialogPool_nodup' L hn)
  exact List.inj_on_of_nodup_map nd (x := i) (y := j)
    (by simp [List.mem_range'_1]; omega) (by simp [List.mem_range'_1]; omega) h

theorem kext_mem (L : ControlledPointLayout) (hw : L.Widths) (q : Wire) (hq : q∈kext L) :
    q∈L.dialogPool := by
  obtain ⟨i,h1,h2,h3,rfl⟩ := kext_index L q hq
  have h : L.core.poolWire i∈L.dialogPool.take 2613 := by
    rw [kpool_block L hw]
    exact List.mem_map.mpr ⟨i,by simp only [List.mem_range'_1]; omega,rfl⟩
  exact List.mem_of_mem_take h

theorem kext_props (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (kext L).Nodup ∧ ∀q∈kext L,q∉L.dialogPool.take 945 := by
  refine ⟨?_,?_⟩
  · have e : kext L=(List.range' 978 51++List.range' 1284 246++List.range' 1533 3).map L.core.poolWire := by
      simp only [kext,wireBlock,List.map_append]
    rw [e]
    apply List.Nodup.map_on
    · intro x hx y hy hxy
      simp only [List.mem_append,List.mem_range'_1] at hx hy
      exact kpool_inj L hw hn x y (by omega) (by omega) hxy
    · apply List.nodup_append.mpr
      refine ⟨List.nodup_append.mpr ⟨List.nodup_range',List.nodup_range',?_⟩,List.nodup_range',?_⟩
      · intro x hx y hy hxy
        simp only [List.mem_range'_1] at hx hy
        omega
      · intro x hx y hy hxy
        simp only [List.mem_append,List.mem_range'_1] at hx hy
        omega
  · intro q hq hm
    obtain ⟨i,h1,h2,h3,rfl⟩ := kext_index L q hq
    have b : L.dialogPool.take 945=wireBlock L.core.poolWire 0 945 := by
      simp only [dialogPool,List.take_take,Nat.min_eq_left (show 945 ≤ 2613 by omega)]
      exact (L.core.pool_prefix hw 945 (by omega)).symm
    rw [b] at hm
    obtain ⟨j,hj,e⟩ := List.mem_map.mp hm
    simp only [List.mem_range'_1] at hj
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega

theorem kext_not_resident (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈kext L) (hr : q∈PointAddLayout.pointWires L.point++[L.control]++L.inPlaceFlags) :
    False :=
  (List.nodup_append.mp (L.dialogUsed_nodup hn)).2.2 q (by simpa [dialogUsedWires] using hr) q
    (kext_mem L hw q hq) rfl

theorem kext_fixed (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈kext L) :
    poolPermutation L.core.poolWire (layout_bounded_injective L hw hn) q=q := by
  obtain ⟨j,hj1,hj2,hj3,rfl⟩ := kext_index L q hq
  apply outside_fixed
  · rintro ⟨i,h1,h2,e⟩
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega
  · rintro ⟨i,h1,h2,e⟩
    have := kpool_inj L hw hn j i (by omega) (by omega) e
    omega

theorem kext_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ExtOK L.dialogStreamedSquareWide L.core.generic (kext L) := by
  have kp := kext_props L hw hn
  refine ⟨kp.1,?_,by simp [kext,wireBlock_length]⟩
  intro q hq hm
  rw [List.mem_cons,L.streamedSquare_wires_eq hw] at hm
  simp only [List.mem_append] at hm
  rcases hm with h|(h|h)|h
  · subst h
    exact kext_not_resident L hw hn _ hq (by simp [inPlaceFlags])
  · exact kext_not_resident L hw hn q hq (by simp [PointAddLayout.pointWires,h])
  · exact kext_not_resident L hw hn q hq (by simp [PointAddLayout.pointWires,h])
  · apply kp.2 q hq
    have e : (L.dialogPool.take 945).take 775=L.dialogPool.take 775 := by
      rw [List.take_take,Nat.min_eq_left (by omega)]
    rw [←e] at h
    exact List.mem_of_mem_take h

def fastCandidate (L : ControlledPointLayout) : Program :=
  accPrefixK L.dialogStreamedSquareWide (kext L) L.core.generic

theorem fastCandidate_counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (fastCandidate L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13554 ∧ measurementCount (fastCandidate L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13566 :=
  accPrefixK_counts L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
    L.core.generic (by simp [kext,wireBlock_length])

theorem fastCandidate_support (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) :
    wires (fastCandidate L)⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776++kext L).toFinset := by
  have support := accPrefixK_support L.dialogStreamedSquareWide
    (L.dialogStreamedSquareWide_widths hw) (L.dialogStreamedSquareWide_nodup hw hn) (kext L)
    L.core.generic (by simp [kext,wireBlock_length])
  have embed : (L.core.generic::L.dialogStreamedSquareWide.wires++kext L).toFinset⊆
      (L.core.generic::L.point.y++L.point.x++L.dialogPool.take 776++kext L).toFinset := by
    rw [L.streamedSquare_wires_eq hw]
    have small : L.dialogPool.take 775⊆L.dialogPool.take 776 := by
      intro q hq
      have e : (L.dialogPool.take 776).take 775=L.dialogPool.take 775 := by
        rw [List.take_take,Nat.min_eq_left (by omega)]
      rw [←e] at hq
      exact List.mem_of_mem_take hq
    intro q hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at hq ⊢
    have hp : q∈L.dialogPool.take 775 → q∈L.dialogPool.take 776 := fun h => small h
    tauto
  exact support.trans embed

theorem fastCandidate_correct (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) (X Y : Nat) (B : Bool) (hX : X<p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic=B)
    (hx : regValue L.point.x s.basis=X) (hy : regValue L.point.y s.basis=Y)
    (hc : regValue L.dialogPool s.basis=0) :
    (run (fastCandidate L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastCandidate L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then cFlipK else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastCandidate L) m s).basis q=s.basis q := by
  let K := L.dialogStreamedSquareWide
  have hwK := L.dialogStreamedSquareWide_widths hw
  have ndK := L.dialogStreamedSquareWide_nodup hw hn
  have controlND : (L.core.generic::K.wires).Nodup := by
    change (L.core.generic::L.dialogStreamedSquareWide.wires).Nodup
    have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢
    omega
  have auxZero (q : Wire)
      (hq : q∈K.core.product++K.core.pad++K.core.work++
        [K.core.productHigh,K.core.outHigh,K.core.workHigh,K.core.cin,
          K.core.normFlag,K.core.modFlag,K.core.sumCarry]++K.overflowPad) :
      s.basis q=false := by
    change q∈L.dialogStreamedSquareWide.core.product++
      L.dialogStreamedSquareWide.core.pad++L.dialogStreamedSquareWide.core.work++
      [L.dialogStreamedSquareWide.core.productHigh,L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh,L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag,L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry]++L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad,List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry=false := auxZero _ (by simp)
  have hp : SquareReduction.p=p := by
    norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c,p]
  have hz : regValue (kext L) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc q (kext_mem L hw q hq))
  have kernel := accPrefixK_correct K hwK (kext L) L.core.generic controlND Y X
    (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean (kext_ok L hw hn) hz
  simpa only [fastCandidate,hb,hp,pow_two] using kernel

theorem fastCandidate_physical (L : ControlledPointLayout) (hw : L.Widths)
    (hn : L.wires.Nodup) : GatePhysical (fastCandidate L) := by
  apply accPrefixK_physical L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
  · have nd := L.streamedSquare_control_nodup hw hn
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp nd q
    simp only [List.count_cons] at h ⊢; omega
  · exact kext_ok L hw hn

/-- Computable relabeled square: the emitted Step 4 program. -/
def fastSquare (L : ControlledPointLayout) : Program :=
  renameProgram (labelFn L.core.poolWire) (fastCandidate L)

noncomputable def fastSquareN (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) : Program :=
  renameProgram (poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)) (fastCandidate L)

theorem fastSquare_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    fastSquare L=fastSquareN L hw hn := by
  apply renameProgram_congr_support
  intro q _
  exact label_matches _ (layout_bounded_injective L hw hn) q

private theorem diag4_pool_away_x' (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.dialogPool) : q∉L.point.x := by
  have nd := L.dialogUsed_nodup hn
  have dis := (List.nodup_append'.mp nd).2.2
  intro hx
  have res : q∈residents L := by
    simp only [residents,PointAddLayout.pointWires,List.mem_append,List.mem_cons]
    tauto
  exact List.disjoint_left.mp dis res hq

private theorem diag4_pull_injective' (e : Equiv.Perm Wire) : Function.Injective (pullState e) := by
  intro s t eq
  apply State.extensionality
  · have ph := congrArg (fun u : State => u.phase) eq
    exact ph
  · funext q
    have bit := congrArg (fun u : State => u.basis (e.symm q)) eq
    simpa only [pullState,e.apply_symm_apply] using bit

section StateEq
attribute [local irreducible] run wires fastCandidate

theorem fastSquare_state_eq (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    run (fastSquare L) m s=run (fastCandidate L) m s := by
  let e := poolPermutation L.core.poolWire (layout_bounded_injective L hw hn)
  have old := fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc
  have cleanIn : ∀q∈L.dialogPool,s.basis q=false := (regValue_zero _ _).mp hc
  have cleanOut : ∀q∈L.dialogPool,(run (fastCandidate L) m s).basis q=false := by
    intro q hq
    exact (old.2.2 q (diag4_pool_away_x' L hn q hq)).trans (cleanIn q hq)
  have input := zero_pool_boundary L hw hn s cleanIn
  have output := zero_pool_boundary L hw hn (run (fastCandidate L) m s) cleanOut
  rw [fastSquare_eq L hw hn,fastSquareN]
  apply diag4_pull_injective' e
  have semantic := run_rename e e.injective (fastCandidate L) m s
  rw [input] at semantic
  exact semantic.trans output.symm

theorem fastSquare_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Nat) (B : Bool) (hX : X < p) (s : State) (m : List Bool)
    (hb : s.basis L.core.generic=B) (hx : regValue L.point.x s.basis=X)
    (hy : regValue L.point.y s.basis=Y) (hc : regValue L.dialogPool s.basis=0) :
    (run (fastSquare L) m s).phase=s.phase ∧
    regValue L.point.x (run (fastSquare L) m s).basis=
      ((X+p-(if B then Y*Y else 0)%p)%p+(if B then cFlipK else 0))%p ∧
    ∀q,q∉L.point.x → (run (fastSquare L) m s).basis q=s.basis q := by
  rw [fastSquare_state_eq L hw hn X Y B hX s m hb hx hy hc]
  exact fastCandidate_correct L hw hn X Y B hX s m hb hx hy hc

end StateEq

theorem fastSquare_physical (L : ControlledPointLayout)
    (hw : L.Widths) (hn : L.wires.Nodup) : GatePhysical (fastSquare L) := by
  rw [fastSquare_eq L hw hn]
  apply gatePhysical_rename _ (poolPermutation L.core.poolWire
    (layout_bounded_injective L hw hn)).injective
  exact fastCandidate_physical L hw hn

theorem fastSquare_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (fastSquare L) ≤ 8000000 := by
  simpa only [fastSquare,Baselines.rename_gateSlots,fastCandidate]
    using accPrefixK_gateSlots_le L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw) (kext L)
      L.core.generic (by simp [kext,wireBlock_length])

end ECDSAAdd.Entrant.OwnDiagAll12Square

end


-- DIAGONAL COMPONENT SquareTriple.lean

namespace ECDSAAdd.Entrant.OwnDiagAll12Square
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
private theorem diag5_sub_val' (x y : Fp) : (x-y).val=(x.val+p-y.val)%p := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.add_mod_mod]
  rw [←Nat.add_sub_assoc (le_of_lt (ZMod.val_lt y))]

section SquareStep
attribute [local irreducible] run fastSquare fastCandidate
private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩

theorem fast_step_square (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (base : BasisState) :
    Triple (PointDialogValues L X Y G base) (fastSquare L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (cFlipK : Fp) else 0)) Y G base) := by
  intro s m v
  obtain ⟨hp,hx,hf⟩ := fastSquare_correct L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean
  refine ⟨hp,v.withX hn ?_ hf⟩
  have hK : ((cFlipK : Nat) : Fp).val=cFlipK := ZMod.val_natCast_of_lt (by norm_num [cFlipK,p])
  rw [ZMod.val_add,diag5_sub_val']
  cases G
  · simpa using hx
  · simpa [ZMod.val_mul,hK] using hx

end SquareStep
end ECDSAAdd.Entrant.OwnDiagAll12Square


-- DIAGONAL COMPONENT Placement.lean

namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

def SquareCorrect (L : ControlledPointLayout) (P : Program) : Prop :=
  ∀ (X Y : Fp) (G : Bool) (origin : BasisState),
    Triple (PointDialogValues L X Y G origin) P
      (PointDialogValues L (X-(if G then Y*Y else 0)+
        (if G then (OwnDiagAll12Square.cFlipK : Fp) else 0)) Y G origin)

theorem relabel (L : ControlledPointLayout) (e : Equiv.Perm Wire)
    (hp : ∀q∈L.dialogPool,e q∈L.dialogPool)
    (hf : ∀q,q∉L.dialogPool → e q=q) (P : Program) (correct : SquareCorrect L P) :
    SquareCorrect L (renameProgram e P) := by
  intro X Y G origin s m v
  have old:=correct X Y G origin s m v
  have eq:=Square5Placement.pool_relabel_state_eq L e hp hf P s m v.clean old.2.clean
  simpa only [eq] using old

def initial (L : ControlledPointLayout) : Program :=
  renameProgram (Square5Placement.blockPerm L 202) (OwnDiagAll12Square.fastCandidate L)
def plus (L : ControlledPointLayout) : Program := renameProgram (OwnPlusSquare.swap L) (initial L)
def guard (L : ControlledPointLayout) : Program := renameProgram (OwnGuardSquare.swap L) (plus L)
def minus (L : ControlledPointLayout) : Program := renameProgram (OwnQ4Square.swap L) (guard L)
def program (L : ControlledPointLayout) : Program := renameProgram (OwnQ5Square.swap L) (minus L)

theorem candidate_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrect L (OwnDiagAll12Square.fastCandidate L) := by
  intro X Y G origin s m v
  have old:=OwnDiagAll12Square.fast_step_square L hw hn X Y G origin s m v
  rw [OwnDiagAll12Square.fastSquare_state_eq L hw hn X.val Y.val G X.isLt s m
    v.generic v.x v.y v.clean] at old
  exact old

theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    SquareCorrect L (program L) := by
  have a:=relabel L (Square5Placement.blockPerm L 202)
    (Square5Placement.block_pool L hw 202 (le_refl _))
    (Square5Placement.block_outside L hw 202 (le_refl _)) _ (candidate_correct L hw hn)
  have b:=relabel L (OwnPlusSquare.swap L) (OwnPlusSquare.pool L hw)
    (OwnPlusSquare.outside L hw) _ a
  have c:=relabel L (OwnGuardSquare.swap L) (OwnGuardSquare.pool L hw)
    (OwnGuardSquare.outside L hw) _ b
  have d:=relabel L (OwnQ4Square.swap L) (OwnQ4Square.pool L hw)
    (OwnQ4Square.outside L hw) _ c
  exact relabel L (OwnQ5Square.swap L) (OwnQ5Square.pool L hw)
    (OwnQ5Square.outside L hw) _ d

end ECDSAAdd.Entrant.OwnDiagAll12Placed


-- DIAGONAL COMPONENT Resources.lean

namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13554 ∧
    measurementCount (program L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13566 := by
  have a:=renameProgram_counts (Square5Placement.blockPerm L 202) (OwnDiagAll12Square.fastCandidate L)
  have b:=renameProgram_counts (OwnPlusSquare.swap L) (initial L)
  have c:=renameProgram_counts (OwnGuardSquare.swap L) (plus L)
  have d:=renameProgram_counts (OwnQ4Square.swap L) (guard L)
  have e:=renameProgram_counts (OwnQ5Square.swap L) (minus L)
  have base:=OwnDiagAll12Square.fastCandidate_counts L hw
  exact ⟨e.1.trans (d.1.trans (c.1.trans (b.1.trans (a.1.trans base.1)))),
    e.2.trans (d.2.trans (c.2.trans (b.2.trans (a.2.trans base.2))))⟩

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) := by
  apply gatePhysical_rename (OwnQ5Square.swap L) (OwnQ5Square.swap L).injective
  apply gatePhysical_rename (OwnQ4Square.swap L) (OwnQ4Square.swap L).injective
  apply gatePhysical_rename (OwnGuardSquare.swap L) (OwnGuardSquare.swap L).injective
  apply gatePhysical_rename (OwnPlusSquare.swap L) (OwnPlusSquare.swap L).injective
  exact gatePhysical_rename (Square5Placement.blockPerm L 202)
    (Square5Placement.blockPerm L 202).injective _ (OwnDiagAll12Square.fastCandidate_physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 := by
  simpa only [program,minus,guard,plus,initial,Baselines.rename_gateSlots,
    OwnDiagAll12Square.fastCandidate] using
      OwnDiagAll12Square.accPrefixK_gateSlots_le L.dialogStreamedSquareWide
        (L.dialogStreamedSquareWide_widths hw) (OwnDiagAll12Square.kext L)
        L.core.generic (by simp [OwnDiagAll12Square.kext,wireBlock_length])

end ECDSAAdd.Entrant.OwnDiagAll12Placed


-- DIAGONAL COMPONENT Support.lean
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag8_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem swap_support (P : Program) (a b : Wire) (S : Finset Wire)
    (old : wires P⊆S) (ha : a∈S) (hb : b∈S) :
    wires (renameProgram (Equiv.swap a b) P)⊆S := by
  rw [renameProgram_support]
  intro q hq
  obtain ⟨w,used,rfl⟩:=Finset.mem_image.mp hq
  by_cases x:w=a
  · subst w; simpa only [Equiv.swap_apply_left] using hb
  · by_cases y:w=b
    · subst w; simpa only [Equiv.swap_apply_right] using ha
    · simpa only [Equiv.swap_apply_of_ne_of_ne x y] using old used

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L) ⊆ (OB5Support.sites L).toFinset := by
  have oldGuard : wires (guard L)⊆(OB5Support.sites L).toFinset := by
    have previous : wires (plus L)⊆(OB5Support.sites L).toFinset := by
      have old : wires (initial L)⊆(OB5Support.sites L).toFinset := by
        rw [initial,renameProgram_support]
        intro q hq
        obtain ⟨old, used, rfl⟩ := Finset.mem_image.mp hq
        have support := OwnDiagAll12Square.fastCandidate_support L hw hn used
        simp only [List.mem_toFinset, List.mem_cons, List.mem_append, or_assoc] at support
        apply List.mem_toFinset.mpr
        rcases support with h | h | h | h | h
        · subst old
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _
            (diag8_resident_away L hn _ (by simp [CompressedPointSquare.residents, inPlaceFlags]))]
          simp [OB5Support.sites]
        · have away := diag8_resident_away L hn old (by simp [CompressedPointSquare.residents, PointAddLayout.pointWires, h])
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
          simp only [OB5Support.sites, List.mem_cons, List.mem_append]
          exact Or.inl (Or.inr h)
        · have away := diag8_resident_away L hn old (by simp [CompressedPointSquare.residents, PointAddLayout.pointWires, h])
          rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away]
          simp only [OB5Support.sites, List.mem_cons, List.mem_append]
          exact Or.inl (Or.inl (Or.inr h))
        · rw [pool_block L hw 776 (by omega)] at h
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
          have bound : i < 776 := by simp only [List.mem_range'_1] at hi; omega
          rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
          apply OB5Support.pool_in_sites
          apply OB5Support.pool_mem
          unfold Square5Placement.blockIndex
          split_ifs <;> omega
        · obtain ⟨i, h1, h2, h3, rfl⟩ := OwnDiagAll12Square.kext_index L _ h
          rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)]
          apply OB5Support.pool_in_sites
          apply OB5Support.pool_mem
          unfold Square5Placement.blockIndex
          split_ifs <;> omega
      exact swap_support (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) _ old
        (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 766 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
        (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1530 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    exact swap_support (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) _ previous
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 765 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
      (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1531 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
  have oldQ4 := swap_support (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) _ oldGuard
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 767 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1532 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

  exact swap_support (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) _ oldQ4
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 770 (Or.inr (Or.inl ⟨by omega,by omega⟩)))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1536 (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

end ECDSAAdd.Entrant.OwnDiagAll12Placed


-- DIAGONAL COMPONENT Omissions.lean
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag9_q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem original_spare_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (n : Nat) (allowed : n∈[1530,1531,1532,1536,1537]) :
    L.core.poolWire n∉wires (initial L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at allowed
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnDiagAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=diag9_q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=diag9_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · have away:=diag9_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw n (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ n (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

theorem swap_target_free (P : Program) (a b : Wire) (free : b∉wires P) :
    a∉wires (renameProgram (Equiv.swap a b) P) := by
  rw [renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have back : (Equiv.swap a b) b=a := Equiv.swap_apply_right _ _
  have same : old=b := (Equiv.swap a b).injective (e.trans back.symm)
  exact free (same ▸ used)

private theorem diag9_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b n : Nat) (ha : a<2613) (hb : b<2613) (hnn : n<2613)
    (hna : n≠a) (hnb : n≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn n a hnn ha eq)
  · intro eq;exact hnb (pool_inj L hw hn n b hnn hb eq)


theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1530 (by simp)
  have p1 : L.core.poolWire 766∉wires (plus L) :=
    swap_target_free (initial L) (L.core.poolWire 766) (L.core.poolWire 1530) p0
  have p2 : L.core.poolWire 766∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 766∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 766∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 766 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1531 (by simp)
  have p1 : L.core.poolWire 1531∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1531 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 765∉wires (guard L) :=
    swap_target_free (plus L) (L.core.poolWire 765) (L.core.poolWire 1531) p1
  have p3 : L.core.poolWire 765∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 765 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 765∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 765 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1532 (by simp)
  have p1 : L.core.poolWire 1532∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1532 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1532∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1532 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 767∉wires (minus L) :=
    swap_target_free (guard L) (L.core.poolWire 767) (L.core.poolWire 1532) p2
  have p4 : L.core.poolWire 767∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 767 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1536 (by simp)
  have p1 : L.core.poolWire 1536∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1536∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1536∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 1536 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 770∉wires (program L) :=
    swap_target_free (minus L) (L.core.poolWire 770) (L.core.poolWire 1536) p3
  exact p4

theorem free1537 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1537∉wires (program L) := by
  have p0:=original_spare_free L hw hn 1537 (by simp)
  have p1 : L.core.poolWire 1537∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 766 1530 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1537∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 765 1531 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1537∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 767 1532 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1537∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag9_fix L hw hn 770 1536 1537 (by omega) (by omega) (by omega) (by omega) (by omega)) p3
  exact p4

end ECDSAAdd.Entrant.OwnDiagAll12Placed


-- DIAGONAL COMPONENT PlacementQ6.lean
namespace ECDSAAdd.Entrant.OwnDiagAll12PlacedQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] run wires

def swap (L : ControlledPointLayout) : Equiv.Perm Wire :=
  Equiv.swap (L.core.poolWire 1285) (L.core.poolWire 1537)
def program (L : ControlledPointLayout) : Program :=
  renameProgram (swap L) (OwnDiagAll12Placed.program L)

theorem pool (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈L.dialogPool,swap L q∈L.dialogPool := by
  intro q hq
  by_cases a:q=L.core.poolWire 1285
  · subst q; simpa only [swap,Equiv.swap_apply_left] using Square5Placement.pool_member L hw 1537 (by omega)
  · by_cases b:q=L.core.poolWire 1537
    · subst q; simpa only [swap,Equiv.swap_apply_right] using Square5Placement.pool_member L hw 1285 (by omega)
    · simpa only [swap,Equiv.swap_apply_of_ne_of_ne a b] using hq

theorem outside (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q,q∉L.dialogPool → swap L q=q := by
  intro q hq
  have a:q≠L.core.poolWire 1285:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1285 (by omega))
  have b:q≠L.core.poolWire 1537:=fun e=>hq (e.symm ▸ Square5Placement.pool_member L hw 1537 (by omega))
  exact Equiv.swap_apply_of_ne_of_ne a b


theorem correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    OwnDiagAll12Placed.SquareCorrect L (program L) :=
  OwnDiagAll12Placed.relabel L (swap L) (pool L hw) (outside L hw) _
    (OwnDiagAll12Placed.correct L hw hn)

theorem retired_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1285∉wires (program L) :=
  OwnDiagAll12Placed.swap_target_free _ _ _ (OwnDiagAll12Placed.free1537 L hw hn)

theorem counts (L : ControlledPointLayout) (hw : L.Widths) :
    toffoliCount (program L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13554 ∧
    measurementCount (program L)=4*OwnDiagLowK.lowkcost2 128+2*OwnDiagLowK.lowkcost2 129+13566 := by
  have e:=renameProgram_counts (swap L) (OwnDiagAll12Placed.program L)
  have c:=OwnDiagAll12Placed.counts L hw
  exact ⟨e.1.trans c.1,e.2.trans c.2⟩

theorem physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    GatePhysical (program L) :=
  gatePhysical_rename (swap L) (swap L).injective _ (OwnDiagAll12Placed.physical L hw hn)

theorem slots (L : ControlledPointLayout) (hw : L.Widths) :
    Challenge.gateSlots (program L)≤8000000 :=
  (Baselines.rename_gateSlots _ _).le.trans (OwnDiagAll12Placed.slots L hw)

theorem support (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    wires (program L)⊆(OB5Support.sites L).toFinset :=
  OwnDiagAll12Placed.swap_support _ _ _ _ (OwnDiagAll12Placed.support L hw hn)
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1285
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))
    (List.mem_toFinset.mpr (OB5Support.pool_in_sites L _ (OB5Support.pool_mem L 1537
      (Or.inr (Or.inr (Or.inl ⟨by omega,by omega⟩))))))

private theorem diag10_fix (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (n : Nat) (hnn : n<2613) (a : n≠1285) (b : n≠1537) : swap L (L.core.poolWire n)=L.core.poolWire n := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact a (pool_inj L hw hn n 1285 hnn (by omega) eq)
  · intro eq;exact b (pool_inj L hw hn n 1537 hnn (by omega) eq)

theorem free765 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 765∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 765 (by omega) (by omega) (by omega))
    (OwnDiagAll12Placed.free765 L hw hn)

theorem free766 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 766∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 766 (by omega) (by omega) (by omega))
    (OwnDiagAll12Placed.free766 L hw hn)

theorem free767 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 767∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 767 (by omega) (by omega) (by omega))
    (OwnDiagAll12Placed.free767 L hw hn)

theorem free770 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 770∉wires (program L) :=
  OwnPlusHost.rename_avoid _ _ _ (diag10_fix L hw hn 770 (by omega) (by omega) (by omega))
    (OwnDiagAll12Placed.free770 L hw hn)

end ECDSAAdd.Entrant.OwnDiagAll12PlacedQ6


-- DIAGONAL COMPONENT TailOmissions.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.OwnDiagAll12Placed
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires
private theorem diag11_q5_Square770_resident_away (L : ControlledPointLayout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈CompressedPointSquare.residents L) : q∉L.dialogPool :=
  List.disjoint_left.mp (List.nodup_append'.mp (L.dialogUsed_nodup hn)).2.2 hq

theorem initial1800_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (initial L) := by
  rw [initial,renameProgram_support]
  intro used
  obtain ⟨old,used,e⟩:=Finset.mem_image.mp used
  have support:=OwnDiagAll12Square.fastCandidate_support L hw hn used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append,or_assoc] at support
  rcases support with h|h|h|h|h
  · subst old
    have away:=diag11_q5_Square770_resident_away L hn L.core.generic (by simp [CompressedPointSquare.residents,inPlaceFlags])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · have away:=diag11_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · have away:=diag11_q5_Square770_resident_away L hn old (by simp [CompressedPointSquare.residents,PointAddLayout.pointWires,h])
    rw [Square5Placement.block_outside L hw 202 (le_refl _) _ away] at e
    exact away (e.symm ▸ Square5Placement.pool_member L hw 1800 (by omega))
  · rw [pool_block L hw 776 (by omega)] at h
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp h
    have bound:i<776:=by simp only [List.mem_range'_1] at hi;omega
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1800 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega
  · obtain ⟨i,h1,h2,h3,rfl⟩:=OwnDiagAll12Square.kext_index L _ h
    rw [Square5Placement.block_apply L hw hn 202 (le_refl _) i (by omega)] at e
    have same:=pool_inj L hw hn _ 1800 (by unfold Square5Placement.blockIndex;split_ifs <;> omega) (by omega) e
    unfold Square5Placement.blockIndex at same
    split_ifs at same <;> omega

private theorem diag11_fix1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (a b : Nat) (ha : a<2613) (hb : b<2613) (hna : 1800≠a) (hnb : 1800≠b) :
    (Equiv.swap (L.core.poolWire a) (L.core.poolWire b)) (L.core.poolWire 1800)=L.core.poolWire 1800 := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro eq;exact hna (pool_inj L hw hn 1800 a (by omega) ha eq)
  · intro eq;exact hnb (pool_inj L hw hn 1800 b (by omega) hb eq)

theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  have p0:=initial1800_free L hw hn
  have p1 : L.core.poolWire 1800∉wires (plus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 766 1530 (by omega) (by omega) (by omega) (by omega)) p0
  have p2 : L.core.poolWire 1800∉wires (guard L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 765 1531 (by omega) (by omega) (by omega) (by omega)) p1
  have p3 : L.core.poolWire 1800∉wires (minus L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 767 1532 (by omega) (by omega) (by omega) (by omega)) p2
  have p4 : L.core.poolWire 1800∉wires (program L) :=
    OwnPlusHost.rename_avoid _ _ _ (diag11_fix1800 L hw hn 770 1536 (by omega) (by omega) (by omega) (by omega)) p3
  exact p4
end ECDSAAdd.Entrant.OwnDiagAll12Placed
namespace ECDSAAdd.Entrant.OwnDiagAll12PlacedQ6
open Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
attribute [local irreducible] wires

theorem free1800 (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) :
    L.core.poolWire 1800∉wires (program L) := by
  have same: swap L (L.core.poolWire 1800)=L.core.poolWire 1800 := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e
      have :=pool_inj L hw hn 1800 1285 (by omega) (by omega) e
      omega
    · intro e
      have :=pool_inj L hw hn 1800 1537 (by omega) (by omega) e
      omega
  exact OwnPlusHost.rename_avoid _ _ _ same (OwnDiagAll12Placed.free1800 L hw hn)

theorem square_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) :
    L.core.poolWire k∉wires (program L) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl
  · exact free1800 L hw hn
  · exact free766 L hw hn
  · exact free765 L hw hn
  · exact free767 L hw hn
  · exact free770 L hw hn
  · exact retired_free L hw hn
end ECDSAAdd.Entrant.OwnDiagAll12PlacedQ6


-- DIAGONAL COMPONENT CountsDiag.lean
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.DiagEndpointCounts
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
attribute [local irreducible] toffoliCount measurementCount

theorem generic_diff (L : ControlledPointLayout) (D : Fp→Program) (S Sold P : Program)
 (delta : Nat) (hS : toffoliCount S+delta=toffoliCount Sold ∧
   measurementCount S+delta=measurementCount Sold) (cx cy : Fp) :
 toffoliCount (All12Generic.generic L D S P cx cy)+delta=
   toffoliCount (All12Generic.generic L D Sold P cx cy) ∧
 measurementCount (All12Generic.generic L D S P cx cy)+delta=
   measurementCount (All12Generic.generic L D Sold P cx cy) := by
 simp only [All12Generic.generic,toffoliCount_append,measurementCount_append]
 constructor <;> omega

theorem gen_diff (L : ControlledPointLayout) (D : Fp→Program) (S Sold P : Program)
 (delta : Nat) (hS : toffoliCount S+delta=toffoliCount Sold ∧
   measurementCount S+delta=measurementCount Sold) (cx cy : Fp) :
 toffoliCount (All12Generic.gen L D S P cx cy)+delta=
   toffoliCount (All12Generic.gen L D Sold P cx cy) ∧
 measurementCount (All12Generic.gen L D S P cx cy)+delta=
   measurementCount (All12Generic.gen L D Sold P cx cy) := by
 have h:=generic_diff L D S Sold P delta hS cx cy
 simp only [All12Generic.gen,All12Generic.mid,toffoliCount_append,measurementCount_append,
   renameProgram_counts]
 constructor <;> omega
end ECDSAAdd.Entrant.DiagEndpointCounts


-- DIAGONAL COMPONENT ActualDiag.lean
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic ECDSAAdd.Secp256k1
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.OwnDiagEndpointActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite
attribute [local irreducible] wires run fastConstAdd fastConstNeg fastConstRefl ExitFusionResearch.exitY

def genericE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.generic L (OwnEndpointEntryQ6.fusedDivisionF L) (OwnDiagAll12PlacedQ6.program L)
    (OwnExitFuseQ6.arithExit L) cx cy

def genE (L : ControlledPointLayout) (cx cy : Fp) : Program :=
  All12Generic.gen L (OwnEndpointEntryQ6.fusedDivisionF L) (OwnDiagAll12PlacedQ6.program L)
    (OwnExitFuseQ6.arithExit L) cx cy



theorem square_step (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (X Y : Fp) (G : Bool) (origin : BasisState) :
    Triple (PointDialogValues L X Y G origin) (OwnDiagAll12PlacedQ6.program L)
      (PointDialogValues L (X-(if G then Y*Y else 0)+(if G then (2^163-1 : Nat) else 0)) Y G origin) := by
  have h:=OwnDiagAll12PlacedQ6.correct L hw hn X Y G origin
  cases G <;> simpa only [OwnDiagAll12Square.cFlipK,Bool.false_eq_true,if_false,if_true,Nat.cast_zero] using h

private theorem diag13_square_diff (L : ControlledPointLayout) (hw : L.Widths) :
 toffoliCount (OwnDiagAll12PlacedQ6.program L)+362=toffoliCount (OwnAll12PlacedQ6.program L) ∧
 measurementCount (OwnDiagAll12PlacedQ6.program L)+362=measurementCount (OwnAll12PlacedQ6.program L) := by
 have a:=OwnDiagAll12PlacedQ6.counts L hw
 have b:=OwnAll12PlacedQ6.counts L hw
 norm_num [OwnDiagLowK.lowkcost2,lowkcost2] at a b
 constructor <;> omega

theorem genericE_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
 toffoliCount (genericE L cx cy)+872=toffoliCount (OwnQ6Producer.genericE L cx cy) ∧
 measurementCount (genericE L cx cy)+617=measurementCount (OwnQ6Producer.genericE L cx cy) := by
 have a:=DiagEndpointCounts.generic_diff L (OwnEndpointEntryQ6.fusedDivisionF L)
   (OwnDiagAll12PlacedQ6.program L) (OwnAll12PlacedQ6.program L) (OwnExitFuseQ6.arithExit L)
   362 (diag13_square_diff L hw) cx cy
 have b:=OwnEndpointActual.genericE_counts_diff L hw cx cy
 change toffoliCount (genericE L cx cy)+362=toffoliCount (OwnEndpointActual.genericE L cx cy) ∧
   measurementCount (genericE L cx cy)+362=measurementCount (OwnEndpointActual.genericE L cx cy) at a
 constructor <;> omega

theorem genE_counts_diff (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
 toffoliCount (genE L cx cy)+872=toffoliCount (OwnQ6Producer.genE L cx cy) ∧
 measurementCount (genE L cx cy)+617=measurementCount (OwnQ6Producer.genE L cx cy) := by
 have a:=DiagEndpointCounts.gen_diff L (OwnEndpointEntryQ6.fusedDivisionF L)
   (OwnDiagAll12PlacedQ6.program L) (OwnAll12PlacedQ6.program L) (OwnExitFuseQ6.arithExit L)
   362 (diag13_square_diff L hw) cx cy
 have b:=OwnEndpointActual.genE_counts_diff L hw cx cy
 change toffoliCount (genE L cx cy)+362=toffoliCount (OwnEndpointActual.genE L cx cy) ∧
   measurementCount (genE L cx cy)+362=measurementCount (OwnEndpointActual.genE L cx cy) at a
 constructor <;> omega

theorem genE_gateSlots_le (L : ControlledPointLayout) (hw : L.Widths) (cx cy : Fp) :
    gateSlots (genE L cx cy)≤49200000 :=
  All12Generic.gen_slots_le L hw _ _ _ (EndpointEntryProperties.division_slots L hw)
    (OwnDiagAll12PlacedQ6.slots L hw) ((OwnExitFuseQ6.arithExit_slots_le L).trans (by decide)) cx cy


theorem genericE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genericE L cx cy)⊆(OB5Support.sites L).toFinset :=
  All12Generic.generic_sites L hw _ _ _ (EndpointEntryProperties.division_support L hw)
    (OwnDiagAll12PlacedQ6.support L hw hn) (OwnExitFuseQ6.arithExit_support L hw) cx cy

theorem genE_sites (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    wires (genE L cx cy)⊆(OB5Support.genericSites L).toFinset := by
  rw [genE,All12Generic.gen_shape]
  exact GenericQ5Geometry.wrapG_sites L hw hn _ (genericE_sites L hw hn cx cy)

theorem genE_physical (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (cx cy : Fp) :
    GatePhysical (genE L cx cy) :=
  All12Generic.gen_physical L hw hn _ _ _ (EndpointEntryProperties.division_physical L hw hn)
    (OwnDiagAll12PlacedQ6.physical L hw hn) (OwnExitFuseQ6.arithExit_physical L hw hn) cx cy


theorem genericE_free (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (k : Nat) (hk : k∈[1800,766,765,767,770,1285]) (cx cy : Fp) :
    L.core.poolWire k∉wires (genericE L cx cy) := by
  have bounds:515≤k ∧ k<2613 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
  exact All12Generic.generic_free L hw hn _ _ _ k bounds
    (EndpointEntryProperties.division_free L hw hn k hk)
    (OwnDiagAll12PlacedQ6.square_free L hw hn k hk)
    (Q6FusionOmissions.exit_avoids L hw hn exitFree k hk) cx cy

theorem genE_ok (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS)
    (logicalND : (skywalkSharedWires base).Nodup) (hlo : History5.HistoryAbove base)
    (logicalAway : ∀q∈[base 2400,base 2409,base 2410],q∉skywalkSharedWires base)
    (logicalReplay : MixedTranscriptReplayLayout base (base 2400) (base 2409) (base 2410)
      (mixedTranscriptTape base)) {cx cy : Fp} (hc : curve.toAffine.Nonsingular cx cy) :
    GenericOK L hc (genE L cx cy) :=
  All12Generic.genFFused_ok L hw hn _ _ _
    (OwnExitFuseQ6.arithExit_correct exitFree L hw hn)
    (OwnEndpointEntryQ6.fusedDivisionF_step L hw hn logicalND hlo logicalAway logicalReplay)
    (square_step L hw hn) hc
end ECDSAAdd.Entrant.OwnDiagEndpointActual


-- DIAGONAL COMPONENT InventoryDiag.lean
namespace ECDSAAdd.Entrant.OwnDiagEndpointActual
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk BalancedField History5 EntryFuse EntryFuseFinite

theorem genE_qubits1593
    (entryFree : base 1541∉wires Q5FusionFields.hostField5S)
    (exitFree : base 1541∉wires OwnExitFuseQ5.hostMulS) (C : Point) (cx cy : Fp) :
    qubits (Edges.wrapper layout C cy (genE layout cx cy))≤1593 := by
  rw [genE,All12Generic.gen_shape]
  apply GenericQ6Geometry.edges_wrapG_qubits _ (genericE_sites layout layout_widths layout_nodup cx cy)
  · intro k hk
    exact genericE_free layout layout_widths layout_nodup entryFree
      exitFree k (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
        rcases hk with h|h|h|h|h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) cx cy
  · exact genericE_free layout layout_widths layout_nodup entryFree
      exitFree 1285 (by simp) cx cy
end ECDSAAdd.Entrant.OwnDiagEndpointActual

