import ECDSAAdd.Submission.Entrant.MainPart04

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! Bank-bit parking for the 128-bit square leaves (part A: definitions and structural facts).

Four `ext` wires are outside every register of the 128-bit leaf KG (`kgH`): the outer `T`
uses `ext[0..130)`, the inner `T` uses `ext[132..198)`, the high inner `S` uses
`ext[198..231)` and the high inner `T` uses `ext[232..298)`. The wires
`ext[131]`, `ext[231]`, `ext[298]`, `ext[299]` (`ext[130]` is the retired-760 body host) are therefore zero during the whole branch.
They hold the last four bank bits through the body, so the second controlled copy needs
four Toffoli gates fewer. -/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout

def hostIdx : List Nat := [131,231,298,299]

def hosts (ext : List Wire) : List Wire := hostIdx.map (fun i => ext.getD i 0)

/-- Measurements of zero wires without corrections: they keep the record alignment. -/
def dummies (hs : List Wire) : Program := hs.map (fun h => Instr.measureX h [] [])

/-- Move a register into a zero register (and back): two CX passes. -/
def move (a b : List Wire) : Program := copyRegister none a b ++ copyRegister none b a

theorem hosts_length (ext : List Wire) : (hosts ext).length=4 := rfl

/-- Index characterisation of membership in a slice of a duplicate-free list. -/
theorem getD_mem_slice (l : List Wire) (hl : l.Nodup) (i a b : Nat) (hi : i<l.length) :
    l.getD i 0∈(l.drop a).take b ↔ a ≤ i ∧ i<a+b := by
  rw [List.getD_eq_getElem _ _ hi]
  constructor
  · intro h
    obtain ⟨j,hj,e⟩ := List.getElem_of_mem h
    simp only [List.getElem_take,List.getElem_drop] at e
    have := (List.Nodup.getElem_inj_iff hl).mp e
    simp only [List.length_take,List.length_drop] at hj
    omega
  · rintro ⟨h1,h2⟩
    have hj : i-a<((l.drop a).take b).length := by
      simp only [List.length_take,List.length_drop]; omega
    have e : ((l.drop a).take b)[i-a]'hj=l[i] := by
      simp only [List.getElem_take,List.getElem_drop]
      congr 1; omega
    rw [←e]; exact List.getElem_mem _

theorem getD_mem_take (l : List Wire) (hl : l.Nodup) (i b : Nat) (hi : i<l.length) :
    l.getD i 0∈l.take b ↔ i<b := by
  have h := getD_mem_slice l hl i 0 b hi
  simpa using h

theorem headD_take (l : List Wire) (k : Nat) (hk : 0<k) : (l.take k).headD 0=l.headD 0 := by
  cases l with
  | nil => simp
  | cons a l =>
    cases k with
    | zero => omega
    | succ k => simp

theorem getD_mem (l : List Wire) (i : Nat) (hi : i<l.length) : l.getD i 0∈l := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

section Hosts
variable (ext : List Wire) (hx : ext.Nodup) (he : 300≤ext.length)

include he in
theorem hosts_sub : ∀h∈hosts ext,h∈ext := by
  intro h hh
  simp only [hosts,hostIdx,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hh
  rcases hh with rfl|rfl|rfl|rfl <;> exact getD_mem _ _ (by omega)

include hx he in
theorem hosts_nodup : (hosts ext).Nodup := by
  have inj (i j : Nat) (hi : i<ext.length) (hj : j<ext.length) (e : ext.getD i 0=ext.getD j 0) : i=j := by
    rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj] at e
    exact (List.Nodup.getElem_inj_iff hx).mp e
  simp only [hosts,hostIdx,List.map_cons,List.map_nil,List.nodup_cons,List.mem_cons,
    List.not_mem_nil,or_false,List.nodup_nil,and_true]
  refine ⟨?_,?_,?_,?_⟩ <;> (try refine ⟨?_,?_⟩) <;> (try refine ⟨?_,?_⟩) <;> (try refine ⟨?_,?_⟩)
  all_goals first
    | (intro e; rcases e with e|e|e|e <;> (have := inj _ _ (by omega) (by omega) e; omega))
    | (intro e; rcases e with e|e|e <;> (have := inj _ _ (by omega) (by omega) e; omega))
    | (intro e; rcases e with e|e <;> (have := inj _ _ (by omega) (by omega) e; omega))
    | (intro e; have := inj _ _ (by omega) (by omega) e; omega)
    | trivial

/-- Each host index avoids all four `ext` slices used by the 128-bit leaf KG and `ext[0]`. -/
theorem idx_free (i : Nat) (hi : i∈hostIdx) :
    ¬ i < 131 ∧ ¬(132 ≤ i ∧ i<132+66) ∧ ¬(198 ≤ i ∧ i<198+33) ∧ ¬(232 ≤ i ∧ i<232+66) ∧ i≠0 ∧ i<300 := by
  simp only [hostIdx,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl <;> omega

include hx he in
theorem host_not_T (h : Wire) (hh : h∈hosts ext) : h∉(ext.take 132).take 130 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  have f := idx_free i hi
  rw [List.take_take,show min 130 132=130 by omega,getD_mem_take ext hx i 130 (by have := f.2.2.2.2.2; omega)]
  have := f.1; omega

include hx he in
theorem host_not_iT (h : Wire) (hh : h∈hosts ext) : h∉(ext.drop 132).take 66 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [getD_mem_slice ext hx i 132 66 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.1

include hx he in
theorem host_not_jS (h : Wire) (hh : h∈hosts ext) : h∉((ext.drop 198).take 34).take 33 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [List.take_take,show min 33 34=33 by omega,
    getD_mem_slice ext hx i 198 33 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.2.1

include hx he in
theorem host_not_jT (h : Wire) (hh : h∈hosts ext) : h∉(ext.drop 232).take 66 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  rw [getD_mem_slice ext hx i 232 66 (by have := (idx_free i hi).2.2.2.2.2; omega)]
  exact (idx_free i hi).2.2.2.1

include hx he in
theorem host_ne_zero (h : Wire) (hh : h∈hosts ext) : h≠ext.getD 0 0 := by
  simp only [hosts,List.mem_map] at hh
  obtain ⟨i,hi,rfl⟩ := hh
  intro e
  have f := idx_free i hi
  rw [List.getD_eq_getElem _ _ (by have := f.2.2.2.2.2; omega),List.getD_eq_getElem _ _ (by omega)] at e
  have := (List.Nodup.getElem_inj_iff hx).mp e
  exact f.2.2.2.2.1 this

end Hosts

section KGH
variable (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire)

/-- For the 128-bit leaf, an `ext` wire outside the three inner slices is not a KG `X` wire. -/
theorem host_not_X (hx : ext.Nodup) (he : 300≤ext.length) (h128 : src.length=128)
    (hE : ∀q∈(LowZero18LowK.ktmp L),q∉ext) (h : Wire) (hh : h∈hosts ext) :
    h∉(LowZero18LowK.kg L ext src dst).X := by
  intro hX
  rw [LowZero18LowK.kg,if_pos h128] at hX
  simp only [KG.X,LowZero18LowK.kgH] at hX
  have hext := hosts_sub ext he h hh
  rcases List.mem_append.mp hX with hX|hX
  · rcases List.mem_append.mp hX with hX|hX
    · rcases List.mem_append.mp hX with hX|hX
      · exact hE h (List.mem_of_mem_drop (List.mem_of_mem_take (hX : h∈((LowZero18LowK.ktmp L).drop 66).take 33))) hext
      · exact host_not_iT ext hx he h hh hX
    · rcases List.mem_append.mp hX with hX|hX
      · exact host_not_jS ext hx he h hh hX
      · exact host_not_jT ext hx he h hh hX
  · exact List.not_mem_nil hX

theorem host_not_oT (hx : ext.Nodup) (he : 300≤ext.length) (h128 : src.length=128)
    (h : Wire) (hh : h∈hosts ext) : h∉(LowZero18LowK.oregs L ext src dst).T := by
  simp only [LowZero18LowK.oregs,h128]
  exact host_not_T ext hx he h hh

end KGH

/-! Program-shape lemmas. -/

theorem eraseMask_split (c : Wire) : ∀ (k : Nat) (src dst : List Wire), src.length=dst.length →
    eraseMask c src dst=eraseMask c (src.take k) (dst.take k)++eraseMask c (src.drop k) (dst.drop k)
  | 0, src, dst, _ => by simp [eraseMask]
  | k+1, [], dst, h => by
    have : dst=[] := List.eq_nil_of_length_eq_zero h.symm
    subst this; rfl
  | k+1, a::src, [], h => by simp at h
  | k+1, a::src, b::dst, h => by
    simp only [List.take_succ_cons,List.drop_succ_cons,eraseMask,List.cons_append]
    rw [eraseMask_split c k src dst (by simpa using h)]

theorem copyRegister_split (c : Option Wire) : ∀ (k : Nat) (src dst : List Wire), src.length=dst.length →
    copyRegister c src dst=copyRegister c (src.take k) (dst.take k)++copyRegister c (src.drop k) (dst.drop k)
  | 0, src, dst, _ => by simp [copyRegister]
  | k+1, [], dst, h => by
    have : dst=[] := List.eq_nil_of_length_eq_zero h.symm
    subst this; rfl
  | k+1, a::src, [], h => by simp at h
  | k+1, a::src, b::dst, h => by
    simp only [List.take_succ_cons,List.drop_succ_cons,copyRegister,List.cons_append,List.singleton_append]
    rw [copyRegister_split c k src dst (by simpa using h)]
    simp only [List.nil_append,List.append_assoc]

theorem dummies_run (hs : List Wire) (t : State) (m : List Bool)
    (h0 : ∀q∈hs,t.basis q=false) : run (dummies hs) m t=t := by
  induction hs generalizing t m with
  | nil => rfl
  | cons a hs ih =>
    have ha : t.basis a=false := h0 a (by simp)
    have step : measureAndCorrect a [] [] (m.headD false) t=t := by
      apply State.extensionality
      · cases m.headD false <;> simp [measureAndCorrect,correct,ha]
      · funext q
        by_cases e : q=a
        · subst e; cases m.headD false <;> simp [measureAndCorrect,correct,writeBit,ha]
        · cases m.headD false <;> simp [measureAndCorrect,correct,writeBit,e]
    change run (dummies hs) m.tail (measureAndCorrect a [] [] (m.headD false) t)=t
    rw [step]
    exact ih t m.tail (fun q hq => h0 q (by simp [hq]))

theorem dummies_counts (hs : List Wire) :
    toffoliCount (dummies hs)=0 ∧ measurementCount (dummies hs)=hs.length := by
  induction hs with
  | nil => exact ⟨rfl,rfl⟩
  | cons a hs ih =>
    constructor
    · change toffoliCount (Instr.measureX a [] [] :: dummies hs)=0
      simpa [toffoliCount] using ih.1
    · have h := ih.2
      change measurementCount (Instr.measureX a [] [] :: dummies hs)=hs.length+1
      simp [measurementCount]
      omega

end ECDSAAdd.Entrant.ParkCopy

/-! Part B: the parked 128-bit leaf and its correctness (appended after part A). -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

section Pieces
variable (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
  (body : Program)

def pA : Program := copyRegister (some control) src (L.inputBank.take src.length)
def pM : Program := LowZero18Square.make L (LowZero18LowK.kg L ext src dst)
def pE1 : Program := eraseMask control (src.take 124) ((L.inputBank.take src.length).take 124)
def pD : Program := dummies (hosts ext)
def pMI : Program := move ((L.inputBank.take src.length).drop 124) (hosts ext)
def pB : Program := renameProgram (LowZero18Square.foldPerm L ext) body
def pC1 : Program := CachedSquareCopy.copy control (LowZero18Square.cacheWire L dst) (src.take 124) ((L.inputBank.take src.length).take 124)
def pMO : Program := move (hosts ext) ((L.inputBank.take src.length).drop 124)
def pCL : Program := LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)
def pE : Program := eraseMask control src (L.inputBank.take src.length)

/-- The 128-bit leaf with its last four bank bits parked on five free `ext` wires. -/
def withLowK2P : Program :=
  pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++
    pC1 L control src dst++pMO L ext src++pCL L ext src dst++pE L control src

end Pieces

private theorem xor_false_eq {a b : Bool} (h : (a ^^ b)=false) : a=b := by
  cases a <;> cases b <;> simp_all

theorem move_correct (a b : List Wire) (hl : a.length=b.length) (hnd : (a++b).Nodup)
    (t : State) (m : List Bool) (hb : regValue b t.basis=0) :
    (run (move a b) m t).phase=t.phase ∧
    (∀w,w∉a → w∉b → (run (move a b) m t).basis w=t.basis w) ∧
    regValue b (run (move a b) m t).basis=regValue a t.basis ∧
    regValue a (run (move a b) m t).basis=0 := by
  have hnd' : (b++a).Nodup := (List.perm_append_comm.nodup_iff).mp hnd
  unfold move
  rw [run_append]
  obtain ⟨p1,f1,v1⟩ := copyRegister_correct none a b hl hnd (by simp) t (m.take (measurementCount (copyRegister none a b)))
  generalize run (copyRegister none a b) (m.take (measurementCount (copyRegister none a b))) t=t1 at p1 f1 v1
  obtain ⟨p2,f2,v2⟩ := copyRegister_correct none b a hl.symm hnd' (by simp) t1 (m.drop (measurementCount (copyRegister none a b)))
  generalize run (copyRegister none b a) (m.drop (measurementCount (copyRegister none a b))) t1=t2 at p2 f2 v2
  have aDisj : ∀w∈a,w∉b := fun w hw hwb => by
    have := List.nodup_append.mp hnd
    exact this.2.2 w hw w hwb rfl
  have v1' : regValue b t1.basis=regValue a t.basis := by
    rw [v1,hb,Nat.zero_xor]; rfl
  have a1 : regValue a t1.basis=regValue a t.basis :=
    regValue_congr _ _ _ (fun w hw => f1 w (aDisj w hw))
  refine ⟨p2.trans p1,fun w ha hb' => (f2 w ha).trans (f1 w hb'),?_,?_⟩
  · rw [←v1']
    exact regValue_congr _ _ _ (fun w hw => f2 w (fun ha => aDisj w ha hw))
  · rw [v2]
    change regValue a t1.basis ^^^ regValue b t1.basis=0
    rw [a1,v1',Nat.xor_self]

end ECDSAAdd.Entrant.ParkCopy


namespace ECDSAAdd.Entrant.ParkCopy
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout
attribute [local irreducible] run wires

open LowZero18Square in
theorem withLowK2P_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup) (src dst : List Wire)
    (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
    (hd : ∀q,dst.count q≤L.core.product.count q)
    (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
    (h128' : src.length=128)
    (ext : List Wire) (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
    (body : Program) (hbody : ∀q∈ext,q∉ECDSAAdd.wires body)
    (s : State) (records : List Bool) (hc : L.PairClean s.basis)
    (hzero : regValue dst s.basis=0) (hz : regValue ext s.basis=0) (V : Nat)
    (callback : ∀t : State,∀m : List Bool,
      regValue dst t.basis=(if s.basis control then regValue src s.basis else 0)^2 →
      (∀q,q∉dst → t.basis q=s.basis q) →
      (run body m t).phase=t.phase ∧ regValue L.core.out (run body m t).basis=V ∧
        ∀q,q∉L.core.out → (run body m t).basis q=t.basis q) :
    (run (withLowK2P L ext control src dst body) records s).phase=s.phase ∧
    regValue L.core.out (run (withLowK2P L ext control src dst body) records s).basis=V ∧
    ∀q,q∉L.core.out → (run (withLowK2P L ext control src dst body) records s).basis q=s.basis q := by
  have hbig := kbig_nodup L control hn src dst hs hd ext hx hdx
  have hbig2 := LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have sizes := L.measured_bank_widths hw
  have inputLen : (L.inputBank.take src.length).length=src.length := by simp [sizes.1,hsmax]
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have dj {r t : List Wire} (h : ∀q,r.count q+t.count q≤(kbig L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig h
  have dj2 {r t : List Wire} (h : ∀q,r.count q+t.count q≤(LowZero18LowK.kbig2 L ext control src dst).count q) :
      ∀q∈r,q∉t := kdis hbig2 h
  -- register placement
  have xS : ∀q∈(LowZero18LowK.oregs L ext src dst).S,q∈LowZero18LowK.ktmp L := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xT : ∀q∈(LowZero18LowK.oregs L ext src dst).T,q∈ext := fun q h => List.mem_of_mem_take (List.mem_of_mem_take h)
  have xX : ∀q∈(LowZero18LowK.kg L ext src dst).X,q∈ext ∨ q∈LowZero18LowK.ktmp L := fun q h =>
    (LowZero18LowK.kg_X L ext src dst q h).elim Or.inl (fun h' => Or.inr (List.mem_of_mem_drop (List.mem_of_mem_take h')))
  have xz : ∀q∈(LowZero18LowK.oregs L ext src dst).z,q∈L.leafCarry := fun q h =>
    List.mem_of_mem_drop (List.mem_of_mem_take h)
  have ext0 : ∀q∈ext,s.basis q=false := (regValue_zero _ _).mp hz
  have tmp0 : ∀q∈LowZero18LowK.ktmp L,s.basis q=false := fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)
  have extOut : ∀q∈ext,q∉L.core.out := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extB : ∀q∈ext,q∉(L.inputBank.take src.length) := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extD : ∀q∈ext,q∉dst := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have extSrc : ∀q∈ext,q∉src := dj (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have tmpOut : ∀q∈LowZero18LowK.ktmp L,q∉L.core.out := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpB : ∀q∈LowZero18LowK.ktmp L,q∉(L.inputBank.take src.length) := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpD : ∀q∈LowZero18LowK.ktmp L,q∉dst := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpSrc : ∀q∈LowZero18LowK.ktmp L,q∉src := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpE : ∀q∈LowZero18LowK.ktmp L,q∉ext := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpC : ∀q∈LowZero18LowK.ktmp L,q∉L.leafCarry := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have tmpP : ∀q∈LowZero18LowK.ktmp L,q∉L.leafPad := dj2 (fun q => by simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append]; omega)
  have ctlT : control∉LowZero18LowK.ktmp L := dj2 (r:=[control]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) control (by simp)
  have cinT : L.core.cin∉LowZero18LowK.ktmp L := dj2 (r:=[L.core.cin]) (fun q => by
    simp only [LowZero18LowK.kbig2,List.count_cons,List.count_append,List.count_nil]; omega) _ (by simp)
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
  -- generic "not a leaf scratch wire" from being outside ext and LowZero18LowK.ktmp and dst
  have nK (q : Wire) (hD : q∉dst) (hE : q∉ext) (hT : q∉LowZero18LowK.ktmp L) :
      q∉(LowZero18LowK.oregs L ext src dst).dst ∧ q∉(LowZero18LowK.oregs L ext src dst).T ∧ q∉(LowZero18LowK.kg L ext src dst).X :=
    ⟨hD,fun h => hE (xT q h),fun h => (xX q h).elim hE hT⟩
  have ndCopy : (src++(L.inputBank.take src.length)).Nodup := knd hbig (fun q => by simp only [kbig,List.count_cons,List.count_append]; omega)
  have ndMask : (control::(src++(L.inputBank.take src.length))).Nodup := knd hbig (fun q => by
    simp only [kbig,List.count_cons,List.count_append]; omega)
  have hcB : ∀c∈some control,c∉(L.inputBank.take src.length) := by
    intro c hc; have e : c=control := by simpa [eq_comm] using hc
    subst e; exact ctlB
  have cacheFix : earlyPerm L (dst.headD 0)=dst.headD 0 := by
    have mem : dst.headD 0∈dst := by
      rcases dst with _|⟨d,ds⟩
      · have hz : src.length=0 := by simpa using hlen.symm
        omega
      · exact List.mem_cons_self
    have targetM : target L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 67 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 67 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    have hostM : earlyHost L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    change (SquareCarryLoan719.earlyPerm L) (dst.headD 0)=dst.headD 0
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne (fun e => tmpD _ targetM (by simpa only [e] using mem))
      (fun e => tmpD _ hostM (by simpa only [e] using mem))
  let P := if s.basis control then regValue src s.basis else 0
  -- parking data
  have Blen : (L.inputBank.take src.length).length=128 := by rw [inputLen,h128']
  have hHx : ∀h∈hosts ext,h∈ext := hosts_sub ext he
  have hHnd : (hosts ext).Nodup := hosts_nodup ext hx he
  have hHT : ∀h∈hosts ext,h∉(LowZero18LowK.oregs L ext src dst).T := fun h hh => host_not_oT L ext src dst hx he h128' h hh
  have hHX : ∀h∈hosts ext,h∉(LowZero18LowK.kg L ext src dst).X := fun h hh => host_not_X L ext src dst hx he h128' tmpE h hh
  have hH0 : ∀h∈hosts ext,h≠ext.getD 0 0 := host_ne_zero ext hx he
  have hHB : ∀h∈hosts ext,h∉(L.inputBank.take src.length) := fun h hh => extB h (hHx h hh)
  have hHD : ∀h∈hosts ext,h∉dst := fun h hh => extD h (hHx h hh)
  have hHo : ∀h∈hosts ext,h∉L.core.out := fun h hh => extOut h (hHx h hh)
  have hHs : ∀q∈src,q∉hosts ext := fun q hq hh => extSrc q (hHx q hh) hq
  have ctlH : control∉hosts ext := fun h => ctlE (hHx _ h)
  have bNd : (L.inputBank.take src.length).Nodup := (List.nodup_append.mp ndCopy).2.1
  have b15 : ∀q∈(L.inputBank.take src.length).take 124,q∉(L.inputBank.take src.length).drop 124 := by
    intro q h1 h5
    have nd : ((L.inputBank.take src.length).take 124++(L.inputBank.take src.length).drop 124).Nodup := by
      rw [List.take_append_drop]; exact bNd
    exact (List.nodup_append.mp nd).2.2 q h1 q h5 rfl
  have b51 : ∀q∈(L.inputBank.take src.length).drop 124,q∉(L.inputBank.take src.length).take 124 :=
    fun q h5 h1 => b15 q h1 h5
  have ndMI : ((L.inputBank.take src.length).drop 124++hosts ext).Nodup :=
    List.nodup_append.mpr ⟨bNd.sublist (List.drop_sublist _ _),hHnd,
      fun a ha b hb e => hHB b hb (e ▸ List.mem_of_mem_drop ha)⟩
  have ndMO : (hosts ext++(L.inputBank.take src.length).drop 124).Nodup :=
    (List.perm_append_comm.nodup_iff).mp ndMI
  have lenMI : ((L.inputBank.take src.length).drop 124).length=(hosts ext).length := by
    rw [List.length_drop,Blen,hosts_length]
  obtain ⟨a9,r10,e10⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src++pCL L ext src dst) (pE L control src) records s
  obtain ⟨a8,r9,e9⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src) (pCL L ext src dst) a9 s
  obtain ⟨a7,r8,e8⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body++pC1 L control src dst) (pMO L ext src) a8 s
  obtain ⟨a6,r7,e7⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src++pB L ext body) (pC1 L control src dst) a7 s
  obtain ⟨a5,r6,e6⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext++pMI L ext src) (pB L ext body) a6 s
  obtain ⟨a4,r5,e5⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src++pD ext) (pMI L ext src) a5 s
  obtain ⟨a3,r4,e4⟩ := kseq (pA L control src++pM L ext src dst++pE1 L control src) (pD ext) a4 s
  obtain ⟨a2,r3,e3⟩ := kseq (pA L control src++pM L ext src dst) (pE1 L control src) a3 s
  obtain ⟨r1,r2,e2⟩ := kseq (pA L control src) (pM L ext src dst) a2 s
  rw [show withLowK2P L ext control src dst body=pA L control src++pM L ext src dst++pE1 L control src++pD ext++
    pMI L ext src++pB L ext body++pC1 L control src dst++pMO L ext src++pCL L ext src dst++pE L control src from rfl,
    e10,e9,e8,e7,e6,e5,e4,e3,e2]
  simp only [pA,pM,pE1,pD,pMI,pB,pC1,pMO,pCL,pE]
  -- copy
  obtain ⟨cp1,cf1,cv1⟩ := copyRegister_correct (some control) src (L.inputBank.take src.length) inputLen.symm ndCopy hcB s r1
  generalize run (copyRegister (some control) src (L.inputBank.take src.length)) r1 s=u0 at cp1 cf1 cv1 ⊢
  have bank0 : regValue (L.inputBank.take src.length) u0.basis=P := by rw [cv1,banks.1,Nat.zero_xor]; rfl
  have u0s : ∀q,q∉(L.inputBank.take src.length) → u0.basis q=s.basis q := cf1
  have X0 : regValue (LowZero18LowK.kg L ext src dst).X u0.basis=0 := (regValue_zero _ _).mpr (fun q h => by
    rcases xX q h with e|e
    · rw [u0s q (extB q e)]; exact ext0 q e
    · rw [u0s q (tmpB q e)]; exact tmp0 q e)
  -- make
  have mk := LowZero18KG.make_correct (LowZero18LowK.kg L ext src dst) sp hall u0 r2
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
  have mkEq := make_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
    sp u0 r2
    (by rw [hKR];exact (kkeep u0s (fun q h hb => bD q hb h)).trans hzero)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (tmpB q (xS q h))];exact tmp0 q (xS q h)))
    X0
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      rw [u0s q (carB q (xz q h))];exact (regValue_zero _ _).mp banks.2.2 q (xz q h)))
    (by rw [hKR];exact (kkeep u0s padB).trans banks.2.1)
    (by rw [hKR];exact (regValue_zero _ _).mpr (fun q h => by
      have hq : q∈L.leafCarry := List.mem_of_mem_take h
      rw [u0s q (carB q hq)];exact (regValue_zero _ _).mp banks.2.2 q hq))
    (by rw [hKR];exact (u0s _ cinB).trans hc.cin)
  simp only [←mkEq] at mk
  have i1 := mk.2.2.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  rw [hKR] at mk
  generalize run (LowZero18Square.make L (LowZero18LowK.kg L ext src dst)) r2 u0=u1 at mk i1 ⊢
  have u1s : ∀q,q∉(LowZero18LowK.oregs L ext src dst).dst → q∉(LowZero18LowK.oregs L ext src dst).T → q∉(LowZero18LowK.kg L ext src dst).X →
      u1.basis q=u0.basis q := mk.2.2.2.2.2.2.2
  have u1z : ∀q,q∉dst → q∉ext → u1.basis q=u0.basis q := by
    intro q hD hE
    by_cases hT : q∈LowZero18LowK.ktmp L
    · by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · have hI : q∈((LowZero18LowK.ktmp L).drop 66).take 33 := (LowZero18LowK.kg_X L ext src dst q hX).elim (fun e => absurd e hE) id
        rw [(regValue_zero _ _).mp i1.1 q hI,u0s q (tmpB q hT),tmp0 q hT]
      · exact u1s q hD (fun h => hE (xT q h)) hX
    · exact u1s q hD (fun h => hE (xT q h)) (fun h => (xX q h).elim hE hT)
  have bank1 : regValue (L.inputBank.take src.length) u1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => u1z q (bD q hq) (fun h => extB q h hq))).trans bank0
  have src1 : regValue src u1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq)))
  have ctl1 : u1.basis control=s.basis control := (u1z _ ctlD ctlE).trans (u0s _ ctlB)
  have dst1 : regValue dst u1.basis=P^2 := by rw [←bank0]; exact mk.2.1
  -- hosts stay zero through the copy and the producer
  have hU1 : ∀h∈hosts ext,u1.basis h=false := fun h hh =>
    (u1s h (hHD h hh) (hHT h hh) (hHX h hh)).trans ((u0s h (hHB h hh)).trans (ext0 h (hHx h hh)))
  have srcw1 : ∀q∈src,u1.basis q=s.basis q := fun q hq =>
    (u1z q (srcD q hq) (fun h => extSrc q h hq)).trans (u0s q (srcB q hq))
  have mask1 : regValue ((L.inputBank.take src.length).take 124) u1.basis=
      if u1.basis control then regValue (src.take 124) u1.basis else 0 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_take_mod _ 124 (by rw [inputLen]; omega) u1.basis,bank1,
      CuccaroStreamedSquareWideLayout.regValue_take_mod src 124 (by omega) u1.basis,ctl1,src1]
    simp only [P]
    split_ifs <;> simp
  -- erase only the first 124 bank bits
  have ndMask1 : (control::(src.take 124++(L.inputBank.take src.length).take 124)).Nodup :=
    ndMask.sublist (List.Sublist.cons₂ _ (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _)))
  obtain ⟨ep1,ef1,ev1⟩ := eraseMask_correct control (src.take 124) ((L.inputBank.take src.length).take 124)
    (by simp only [List.length_take,inputLen]) ndMask1 u1 r3 mask1
  generalize run (eraseMask control (src.take 124) ((L.inputBank.take src.length).take 124)) r3 u1=u2a at ep1 ef1 ev1 ⊢
  -- record-preserving dummies on the (zero) hosts
  have hU2a : ∀h∈hosts ext,u2a.basis h=false := fun h hh =>
    (ef1 h (fun hb => hHB h hh (List.mem_of_mem_take hb))).trans (hU1 h hh)
  rw [dummies_run (hosts ext) u2a r4 hU2a]
  -- park the last four bank bits on the hosts
  obtain ⟨mp1,mf1,mv1,mz1⟩ := move_correct ((L.inputBank.take src.length).drop 124) (hosts ext) lenMI ndMI u2a r5
    ((regValue_zero _ _).mpr hU2a)
  generalize run (move ((L.inputBank.take src.length).drop 124) (hosts ext)) r5 u2a=u2 at mp1 mf1 mv1 mz1 ⊢
  have x5 : regValue (hosts ext) u2.basis=regValue ((L.inputBank.take src.length).drop 124) u1.basis := by
    rw [mv1]; exact regValue_congr _ _ _ (fun q hq => ef1 q (b51 q hq))
  have u2B : ∀q∈(L.inputBank.take src.length),u2.basis q=false := by
    intro q hq
    have hsplit : q∈(L.inputBank.take src.length).take 124 ∨ q∈(L.inputBank.take src.length).drop 124 := by
      rw [←List.mem_append,List.take_append_drop]; exact hq
    rcases hsplit with h1|h5
    · rw [mf1 q (b15 q h1) (fun hh => hHB q hh hq)]; exact (regValue_zero _ _).mp ev1 q h1
    · exact (regValue_zero _ _).mp mz1 q h5
  have u2s : ∀q,q∉dst → q∉ext → u2.basis q=s.basis q := by
    intro q hq hx'
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact (u2B q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [mf1 q (fun h => hb (List.mem_of_mem_drop h)) (fun h => hx' (hHx q h)),
        ef1 q (fun h => hb (List.mem_of_mem_take h))]
      exact (u1z q hq hx').trans (u0s q hb)
  have u2ext : ∀q∈ext,q∉hosts ext → u2.basis q=u1.basis q := fun q h hH =>
    (mf1 q (fun h5 => extB q h (List.mem_of_mem_drop h5)) hH).trans (ef1 q (fun h1 => extB q h (List.mem_of_mem_take h1)))
  have u2u1 : ∀q,q∉(L.inputBank.take src.length) → q∉hosts ext → u2.basis q=u1.basis q := fun q hb hH =>
    (mf1 q (fun h => hb (List.mem_of_mem_drop h)) hH).trans (ef1 q (fun h => hb (List.mem_of_mem_take h)))
  -- body
  let u2' : State := ⟨u2.phase,fun q => if q∈ext then s.basis q else u2.basis q⟩
  have dst2' : regValue dst u2'.basis=P^2 := by
    rw [←dst1]
    apply regValue_congr
    intro q hq
    have hx : q∉ext := fun h => extD q h hq
    simp only [u2',hx,if_false]
    exact u2u1 q (fun h => bD q h hq) (fun h => hHD q h hq)
  have cb := callback u2' r6 dst2' (by
    intro q hq
    by_cases hx : q∈ext
    · simp only [u2',hx,if_true]
    · simp only [u2',hx,if_false]; exact u2s q hq hx)
  have loc := run_local_increment body u2 u2' r6 (by
    intro q hq
    have hx : q∉ext := fun h => hbody q h hq
    simp only [u2',hx,if_false])
  generalize hv' : run body r6 u2'=v' at cb loc
  generalize hv : run body r6 u2=v at loc
  have vIn : ∀q∈ext,v.basis q=u2.basis q := by
    intro q hq; rw [←hv]; exact run_preserves_outside body r6 u2 q (hbody q hq)
  have vOut : ∀q,q∉ext → v.basis q=v'.basis q := by
    intro q hq
    by_cases hb : q∈ECDSAAdd.wires body
    · exact loc.2 q hb
    · rw [←hv,←hv',run_preserves_outside body r6 u2 q hb,run_preserves_outside body r6 u2' q hb]
      simp only [u2',hq,if_false]
  have vPhase : v.phase=u2.phase := by
    apply xor_false_eq
    rw [loc.1,cb.1]
    cases u2'.phase <;> rfl
  have vFrame : ∀q,q∉L.core.out → v.basis q=u2.basis q := by
    intro q hq
    by_cases hx : q∈ext
    · exact vIn q hx
    · rw [vOut q hx,cb.2.2 q hq]; simp only [u2',hx,if_false]
  have vVal : regValue L.core.out v.basis=V :=
    (regValue_congr _ _ _ (fun q hq => vOut q (fun h => extOut q h hq))).trans cb.2.1
  have targetTmp : target L∈LowZero18LowK.ktmp L := by
    apply DiagSq.getD_in
    rw [LowZero18LowK.ktmp_length L hw]
    omega
  have targetIn : u2.basis (target L)=false :=
    (u2s _ (tmpD _ targetTmp) (tmpE _ targetTmp)).trans (tmp0 _ targetTmp)
  have targetOut : (run body r6 u2).basis (target L)=false := by
    rw [hv]
    exact (vFrame _ (tmpOut _ targetTmp)).trans targetIn
  have extMember : ext.getD 0 0∈ext := DiagSq.getD_in _ 0 (by omega)
  have hostIn : u2.basis (ext.getD 0 0)=false :=
    (u2ext _ extMember (fun hm => hH0 _ hm rfl)).trans
      (cross_host_zero L ext src dst h128 he u1.basis _ _ mk.2.2.2.1)
  have foldEq := fold_run_eq L hw ext body u2 r6 targetIn targetOut hostIn (hbody _ extMember)
  rw [hv] at foldEq
  rw [foldEq]
  -- second copy
  have vDst : regValue dst v.basis=P^2 := by
    calc
      regValue dst v.basis = regValue dst u2.basis :=
        regValue_congr _ _ _ (fun q hq => vFrame q (dOut q hq))
      _ = regValue dst u1.basis :=
        regValue_congr _ _ _ (fun q hq => u2u1 q (fun hb => bD q hb hq) (fun h => hHD q h hq))
      _ = P^2 := dst1
  have vControl : v.basis control=s.basis control :=
    (vFrame _ ctlO).trans (u2s _ ctlD ctlE)
  have vSource : regValue src v.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq =>
      (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq)))
  have cached : v.basis (dst.headD 0)=(v.basis control && v.basis (src.headD 0)) :=
    CachedSquareCopy.square_head src dst control v (by omega) (by omega)
      (by simpa only [P,vControl,vSource] using vDst)
  rw [cacheWire,cacheFix,CachedSquareCopy.run_eq control (dst.headD 0) (src.take 124) ((L.inputBank.take src.length).take 124) v r7
    (by rw [headD_take src 124 (by omega)]; exact cached)]
  have inputLen1 : (src.take 124).length=((L.inputBank.take src.length).take 124).length := by
    simp only [List.length_take,inputLen]
  have ndCopy1 : (src.take 124++(L.inputBank.take src.length).take 124).Nodup :=
    ndCopy.sublist (List.Sublist.append (List.take_sublist _ _) (List.take_sublist _ _))
  have hcB1 : ∀c∈some control,c∉(L.inputBank.take src.length).take 124 := fun c hc' h =>
    hcB c hc' (List.mem_of_mem_take h)
  obtain ⟨cp2,cf2,cv2⟩ := copyRegister_correct (some control) (src.take 124) ((L.inputBank.take src.length).take 124)
    inputLen1 ndCopy1 hcB1 v r7
  generalize run (copyRegister (some control) (src.take 124) ((L.inputBank.take src.length).take 124)) r7 v=w0' at cp2 cf2 cv2 ⊢
  have vB : ∀q∈(L.inputBank.take src.length),v.basis q=s.basis q := fun q hq =>
    (vFrame q (bOut q hq)).trans (u2s q (bD q hq) (fun h => extB q h hq))
  have vSrc : ∀q∈src,v.basis q=s.basis q := fun q hq =>
    (vFrame q (srcOut q hq)).trans (u2s q (srcD q hq) (fun h => extSrc q h hq))
  have w0'B5 : regValue ((L.inputBank.take src.length).drop 124) w0'.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (cf2 q (b51 q hq)).trans ((vB q (List.mem_of_mem_drop hq)).trans
      ((regValue_zero _ _).mp banks.1 q (List.mem_of_mem_drop hq))))
  -- unpark: hosts back into the bank, hosts cleared
  obtain ⟨mp2,mf2,mv2,mz2⟩ := move_correct (hosts ext) ((L.inputBank.take src.length).drop 124) lenMI.symm ndMO w0' r8 w0'B5
  generalize run (move (hosts ext) ((L.inputBank.take src.length).drop 124)) r8 w0'=w0 at mp2 mf2 mv2 mz2 ⊢
  have cf2n : ∀q,q∉(L.inputBank.take src.length) → q∉hosts ext → w0.basis q=v.basis q := fun q hb hH =>
    (mf2 q hH (fun h => hb (List.mem_of_mem_drop h))).trans (cf2 q (fun h => hb (List.mem_of_mem_take h)))
  have w0B5 : regValue ((L.inputBank.take src.length).drop 124) w0.basis=
      regValue ((L.inputBank.take src.length).drop 124) u1.basis := by
    rw [mv2,←x5]
    apply regValue_congr; intro q hq
    rw [cf2 q (fun h => hHB q hq (List.mem_of_mem_take h)),vIn q (hHx q hq)]
  have vCtl1 : v.basis control=u1.basis control := (vFrame _ ctlO).trans ((u2s _ ctlD ctlE).trans ctl1.symm)
  have w0B1 : regValue ((L.inputBank.take src.length).take 124) w0.basis=
      regValue ((L.inputBank.take src.length).take 124) u1.basis := by
    have v0 : regValue ((L.inputBank.take src.length).take 124) v.basis=0 :=
      (regValue_zero _ _).mpr (fun q hq => (vB q (List.mem_of_mem_take hq)).trans
        ((regValue_zero _ _).mp banks.1 q (List.mem_of_mem_take hq)))
    have vs1 : regValue (src.take 124) v.basis=regValue (src.take 124) u1.basis :=
      regValue_congr _ _ _ (fun q hq => (vSrc q (List.mem_of_mem_take hq)).trans (srcw1 q (List.mem_of_mem_take hq)).symm)
    rw [show regValue ((L.inputBank.take src.length).take 124) w0.basis=
        regValue ((L.inputBank.take src.length).take 124) w0'.basis from
      regValue_congr _ _ _ (fun q hq => mf2 q (fun h => hHB q h (List.mem_of_mem_take hq)) (b15 q hq)),
      cv2,mask1,v0,Nat.zero_xor]
    change (if v.basis control then regValue (src.take 124) v.basis else 0)=_
    rw [vCtl1,vs1]
  have wB : ∀q∈(L.inputBank.take src.length),w0.basis q=u1.basis q := by
    intro q hq
    have hsplit : q∈(L.inputBank.take src.length).take 124 ∨ q∈(L.inputBank.take src.length).drop 124 := by
      rw [←List.mem_append,List.take_append_drop]; exact hq
    rcases hsplit with h1|h5
    · exact (regValue_eq_iff _ _ _).mp w0B1 q h1
    · exact (regValue_eq_iff _ _ _).mp w0B5 q h5
  have bankW : regValue (L.inputBank.take src.length) w0.basis=P := (regValue_congr _ _ _ wB).trans bank1
  have w0u1 : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → w0.basis q=u1.basis q := by
    intro q hb ho
    by_cases hH : q∈hosts ext
    · rw [(regValue_zero _ _).mp mz2 q hH,hU1 q hH]
    · rw [cf2n q hb hH,vFrame q ho]
      by_cases hx' : q∈ext
      · exact u2ext q hx' hH
      · exact u2u1 q hb hH
  have w0s : ∀q,q∉(L.inputBank.take src.length) → q∉L.core.out → q∉dst → q∉ext → w0.basis q=s.basis q :=
    fun q hb ho hD hE => (w0u1 q hb ho).trans ((u1z q hD hE).trans (u0s q hb))
  have bankLoHi : regValue (LowZero18LowK.oregs L ext src dst).lo w0.basis=regValue (LowZero18LowK.oregs L ext src dst).lo u0.basis ∧
      regValue (LowZero18LowK.oregs L ext src dst).hi w0.basis=regValue (LowZero18LowK.oregs L ext src dst).hi u0.basis := by
    have l1 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) w0.basis
    have l2 := CuccaroStreamedSquareWideLayout.regValue_take_mod (L.inputBank.take src.length) 64 (by omega) u0.basis
    have h1 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) w0.basis
    have h2 := CuccaroStreamedSquareWideLayout.regValue_drop_div (L.inputBank.take src.length) 64 (by omega) u0.basis
    rw [bankW] at l1 h1
    rw [bank0] at l2 h2
    exact ⟨l1.trans l2.symm,h1.trans h2.symm⟩
  have xE (q : Wire) (h : q∈ext ∨ q∈LowZero18LowK.ktmp L) : q∉(L.inputBank.take src.length) ∧ q∉L.core.out :=
    h.elim (fun e => ⟨extB q e,extOut q e⟩) (fun e => ⟨tmpB q e,tmpOut q e⟩)
  have Xw : ∀q∈(LowZero18LowK.kg L ext src dst).X,w0.basis q=u1.basis q := fun q h =>
    w0u1 q (xE q (xX q h)).1 (xE q (xX q h)).2
  have X1w : ∀q∈(LowZero18LowK.kg L ext src dst).X1,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X2w : ∀q∈(LowZero18LowK.kg L ext src dst).X2,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have X5w : ∀q∈(LowZero18LowK.kg L ext src dst).X5,u1.basis q=w0.basis q := fun q h =>
    (Xw q (by simp [KG.X,h])).symm
  have carW : regValue L.leafCarry w0.basis=0 :=
    ((regValue_congr _ _ _ (fun q hq => w0s q (carB q hq) (carOut q hq) (carD q hq) (carE q hq)))).trans banks.2.2
  have I1w := sp.lc1 _ u1.basis w0.basis X1w mk.2.2.2.2.1
  have I2w := sp.lc2 _ u1.basis w0.basis X2w mk.2.2.2.2.2.1
  have I5w := sp.lc5 _ u1.basis w0.basis X5w mk.2.2.2.2.2.2.1
  rw [←bankLoHi.1] at I1w
  rw [←bankLoHi.2] at I2w
  rw [←bankLoHi.1,←bankLoHi.2] at I5w
  have cl := LowZero18KG.clear_correct (LowZero18LowK.kg L ext src dst) sp hall w0 r9
    (by
      rw [hKR,show regValue (LowZero18LowK.oregs L ext src dst).bank w0.basis=P from bankW,
        show regValue (LowZero18LowK.oregs L ext src dst).dst w0.basis=regValue (LowZero18LowK.oregs L ext src dst).dst u1.basis from
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
  have free := LowZero18SquareSupport.earlyHost_Q1_free
    L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have clEq := clear_run_eq_of_boundaries L hw (LowZero18LowK.kg L ext src dst) w0 r9
    (LowZero18SquareSupport.target_clearPrefix_free
      L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he) free.2
    (by
      have inv := I1w
      rw [LowZero18LowK.kg_I1] at inv
      exact (regValue_zero _ _).mp inv.1 _
        (SquareCarryLoan719Support.target_mem_inner L hw ext src dst))
    ((regValue_zero _ _).mp cl.2.2.2.2.1 _ (by
      have member := LowZero18SquareSupport.target_mem_X1 L hw ext src dst
      simp only [KG.X,List.mem_append]
      tauto))
    ((regValue_zero _ _).mp cl.2.2.1 _
      (LowZero18SquareSupport.earlyHost_mem_outer L hw ext src dst h128))
  simp only [←clEq] at cl
  rw [hKR] at cl
  generalize run (LowZero18Square.clear L (LowZero18LowK.kg L ext src dst)) r9 w0=w1 at cl ⊢
  have w1s : ∀q,q∉dst → q∉ext → q∉LowZero18LowK.ktmp L → w1.basis q=w0.basis q := fun q hD hE hT =>
    let o := nK q hD hE hT; cl.2.2.2.2.2 q o.1 o.2.1 o.2.2
  have w1B : regValue (L.inputBank.take src.length) w1.basis=P :=
    (regValue_congr _ _ _ (fun q hq => w1s q (bD q hq) (fun h => extB q h hq) (fun h => tmpB q h hq))).trans bankW
  have w1src : regValue src w1.basis=regValue src s.basis :=
    regValue_congr _ _ _ (fun q hq => (w1s q (srcD q hq) (fun h => extSrc q h hq) (fun h => tmpSrc q h hq)).trans
      ((cf2n q (srcB q hq) (hHs q hq)).trans (vSrc q hq)))
  have w1ctl : w1.basis control=s.basis control :=
    (w1s _ ctlD ctlE ctlT).trans ((cf2n _ ctlB ctlH).trans ((vFrame _ ctlO).trans (u2s _ ctlD ctlE)))
  obtain ⟨ep2,ef2,ev2⟩ := eraseMask_correct control src (L.inputBank.take src.length) inputLen.symm ndMask w1 r10 (by
    rw [w1B,w1ctl,w1src])
  generalize run (eraseMask control src (L.inputBank.take src.length)) r10 w1=w2 at ep2 ef2 ev2 ⊢
  refine ⟨ep2.trans (cl.1.trans (mp2.trans (cp2.trans (vPhase.trans (mp1.trans (ep1.trans (mk.1.trans cp1))))))),?_,?_⟩
  · rw [←vVal]
    apply regValue_congr
    intro q hq
    have o := nK q (fun h => dOut q h hq) (fun h => extOut q h hq) (fun h => tmpOut q h hq)
    rw [ef2 q (fun h => bOut q h hq),cl.2.2.2.2.2 q o.1 o.2.1 o.2.2,cf2n q (fun h => bOut q h hq) (fun h => hHo q h hq)]
  · intro q hq
    by_cases hb : q∈(L.inputBank.take src.length)
    · exact ((regValue_zero _ _).mp ev2 q hb).trans ((regValue_zero _ _).mp banks.1 q hb).symm
    · rw [ef2 q hb]
      by_cases hD : q∈(LowZero18LowK.oregs L ext src dst).dst
      · exact ((regValue_zero _ _).mp cl.2.1 q hD).trans ((regValue_zero _ _).mp hzero q hD).symm
      by_cases hT : q∈(LowZero18LowK.oregs L ext src dst).T
      · exact ((regValue_zero _ _).mp cl.2.2.2.1 q hT).trans (ext0 q (xT q hT)).symm
      by_cases hX : q∈(LowZero18LowK.kg L ext src dst).X
      · rw [(regValue_zero _ _).mp cl.2.2.2.2.1 q hX]
        rcases xX q hX with e|e
        · exact (ext0 q e).symm
        · exact (tmp0 q e).symm
      rw [cl.2.2.2.2.2 q hD hT hX]
      by_cases hH : q∈hosts ext
      · rw [(regValue_zero _ _).mp mz2 q hH]; exact (ext0 q (hHx q hH)).symm
      rw [cf2n q hb hH,vFrame q hq]
      by_cases hx : q∈ext
      · rw [u2ext q hx hH,u1s q hD hT hX,u0s q hb]
      · exact u2s q hD hx

end ECDSAAdd.Entrant.ParkCopy
