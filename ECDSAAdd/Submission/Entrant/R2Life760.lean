import ECDSAAdd.Submission.Entrant.MainA

/-! # R2Life760: the 1016 generic field-kernel halves with retired carry `base 760`

AUX R2 (2026-11-02).  Retires pool wire 760 (virtual `base 760` = carry #248 of the generic
half `w = base`, `sign = base 2409`) from the 1016 generic kernel halves.

Everything up to the `R2Life760` sections is GordoAR's lifetime development
(`/root/work/r2scope/life/LifeProof.lean`, itself a consolidation of the Q6Lifetime* modules),
copied verbatim except for:
* `Rolling1588Lifetime.half_ports_nodup` is renamed `half_ports_nodup760` (MainB declares the
  same name);
* the support/physical theorems are stated for `retired=719∨retired=720∨retired=760`
  (all proofs unchanged except one extra `rfl` case).
The run equalities (`Q6LifetimeProof.half_run_eq`, `half_frame`) are generic in `retired`.

`half760 divide` is the lifetime half followed, for the inverse (`divide=false`), by one
empty-correction erasure of the clean `one` flag `base 1027`: the inverse lifetime half makes
1020 measurements against the old 1021, the pad restores identical record and count shapes. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.Q6LifetimeResearch
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum Challenge

def move (retired host : Wire) (P : Program) : Program :=
  renameProgram (Equiv.swap retired host) P

def rawAdd (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  let ys := L.ylow
  let rs := L.low
  let cs := (Q6Structural.q6Carry L).take 255
  let a := ys.getD 0 0
  let b := rs.getD 0 0
  let c := cs.getD 0 0
  let clear := [Instr.CX L.parity b, .CX a b, .CX L.sign b]
  signComplement L.sign L.y ++ majority a b L.sign c ++ clear ++
    move retired b
      (CoherentTail.addPrefix (ys.drop 1) (rs.drop 1) (cs.drop 1)
        L.ymsb L.rmsb L.one c) ++ clear.reverse ++
    eraseCarry a b L.sign c ++ [.CX a b, .CX L.sign b] ++
    signComplement L.sign L.y

/-- Forward: after the raw shift, rmsb=lower. Only the low255 bits enter
the adder. Both CNOTs are charged, including restoration before the old tail. -/
def fold (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  [.CCX L.parity L.lower L.one, .CX L.lower L.rmsb] ++
    move retired L.rmsb
      (mappedAdd (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one) ++
    [.CX L.lower L.rmsb, .CX L.parity L.rmsb, .CX L.parity L.lower,
     .CX L.rmsb L.lower,
     .measureX L.one [] [.Z L.parity, .CZ L.parity L.rmsb]]

/-- Inverse: after its two leading CNOTs, rmsb=lower xor parity. -/
def unfoldStep (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  [.CX L.parity L.lower, .CX L.rmsb L.lower, .CCX L.parity L.lower L.one,
   .CX L.lower L.rmsb, .CX L.parity L.rmsb] ++
    move retired L.rmsb
      (mappedSub (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one) ++
    [.CX L.parity L.rmsb, .CX L.lower L.rmsb,
     .CX L.parity L.rmsb, .CX L.rmsb L.lower,
     .measureX L.one [] [.CZ L.parity L.rmsb]]

/-- A final comparator result is the final carry with a fixed complement.
Forward erases the known comparison result directly; inverse computes that
result directly. No scratch is used for the terminal carry. -/
def compareLeaf (forward : Bool) (a b cin target : Wire) : Program :=
  if forward then [.X target] ++ eraseCarry a b cin target
  else majority a b cin target ++ [.X target]

def compareChain (forward : Bool) :
    List Wire → List Wire → List Wire → Wire → Wire → Program
  | [a], [b], _, cin, target => compareLeaf forward a b cin target
  | a::a'::as, b::b'::bs, c::cs, cin, target =>
      majority a b cin c ++ compareChain forward (a'::as) (b'::bs) cs c target ++
        eraseCarry a b cin c
  | _, _, _, _, _ => []

/-- The original head computes its carry, then flips the initialized input
flag one back to zero. That clean flag hosts the retired ordinary carry in
the complete remaining chain, and is restored before the head correction. -/
def compare (retired : Wire) (forward : Bool) (L : BalancedCircuit.Layout) : Program :=
  let a := L.y.getD 0 0
  let b := L.r.getD 0 0
  let cs := (Q6Structural.q6Carry L).take 255
  let c := cs.getD 0 0
  notRegister (L.one::L.r) ++ majority a b L.one c ++ [.X L.one] ++
    move retired L.one
      (compareChain forward (L.y.drop 1) (L.r.drop 1) (cs.drop 1) c L.parity) ++
    [.X L.one] ++ eraseCarry a b L.one c ++ notRegister (L.one::L.r)

/-- The repeated top source and sign-extended output imply a quadratic
predicate for the old high data bit. Its X measurement replaces the old
affine top-carry target, with an immediate correction for every record. -/
def dependentTop (a b cin z : Wire) : Program :=
  [.measureX z [] [.CZ a b, .CZ a cin, .CZ b cin, .Z b, .Z cin],
   .CX a b, .CX cin b, .CX b z]

def addTop : List Wire → List Wire → List Wire → Wire → Program
  | [a,_], [b,z], _, cin => dependentTop a b cin z
  | a::a'::as, b::b'::bs, c::cs, cin =>
      majority a b cin c ++ addTop (a'::as) (b'::bs) cs c ++
        eraseCarry a b cin c ++ [.CX a b, .CX cin b]
  | _, _, _, _ => []

/-- Retain parity=r0 through rawSub. The complemented old r0 can be cleared
for the upper recursion and reconstructed before the head measurement.
The final two CNOTs erase parity from the reconstructed low result/source. -/
def rawSubTail (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  let xs := GuardCompression.source L
  let ys := BalancedCircuit.rawTarget L
  let cs := (Q6Structural.q6Carry L).take 255
  let a := xs.getD 0 0
  let b := ys.getD 0 0
  let c := cs.getD 0 0
  signComplement L.sign L.y ++ notRegister ys ++ majority a b L.sign c ++
    [.X b, .CX L.parity b] ++
    move retired b (addTop (xs.drop 1) (ys.drop 1) (cs.drop 1) c) ++
    [.CX L.parity b, .X b] ++ eraseCarry a b L.sign c ++
    [.CX a b, .CX L.sign b] ++ notRegister ys ++ signComplement L.sign L.y ++
    [.CX b L.parity, .CX (L.ylow.getD 0 0) L.parity, .CX L.rmsb L.one]

/-- prepareSign has made rmsb exactly zero. Both literal programs exclude
that site, and return the borrowed carry zero before inverse prepareSign. -/
def normalize (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  move retired L.rmsb (BalancedCleanup.normalize L.toLayout)
def unnormalize (retired : Wire) (endpoint : Bool) (L : BalancedCircuit.Layout) : Program :=
  move retired L.rmsb
    (if endpoint then FifthCarry2.unnormalizeE L.toLayout
     else BalancedCleanup.unnormalize L.toLayout)

def forward (retired : Wire) (endpoint : Bool) (L : BalancedCircuit.Layout) : Program :=
  GuardCompression.seed L ++ rawAdd retired L ++ OneReuse.newPrepare L ++
    rotateRight (BalancedCircuit.rawTarget L) ++ fold retired L ++
    BalancedCleanup.prepareSign L.toLayout ++ BiasedCircuit.flipBias L ++
    BalancedCleanup.prepareCompare L.toLayout ++ Q6StructuralCell.exposure L ++
    compare retired true L ++ (Q6StructuralCell.exposure L).reverse ++
    (BalancedCleanup.prepareCompare L.toLayout).reverse ++ unnormalize retired endpoint L ++
    (BalancedCleanup.prepareSign L.toLayout).reverse ++ [.measureX L.one [] []]

def inverse (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  BalancedCleanup.prepareSign L.toLayout ++ normalize retired L ++
    BalancedCleanup.prepareCompare L.toLayout ++ Q6StructuralCell.exposure L ++
    compare retired false L ++ (Q6StructuralCell.exposure L).reverse ++
    (BalancedCleanup.prepareCompare L.toLayout).reverse ++ BiasedInverse.unbiasView L ++
    unfoldStep retired L ++ rotateLeft (BalancedCircuit.rawTarget L) ++
    [.CX L.parity L.r0] ++ rawSubTail retired L

def half (retired : Wire) (divide : Bool) (w : Nat → Wire) (sign : Wire) : Program :=
  let L := Q6EndpointCell.ports w sign
  [.X sign] ++ (if divide then forward retired false L else inverse retired L) ++ [.X sign]

def halfE (retired : Wire) (divide : Bool) (w : Nat → Wire) (sign : Wire) : Program :=
  if divide then [.X sign] ++ forward retired true (Q6EndpointCell.ports w sign) ++ [.X sign]
  else half retired false w sign

end ECDSAAdd.Entrant.Q6LifetimeResearch

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeLoans =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Half
-- consolidated import: import ECDSAAdd.Arithmetic.DisjointPrograms
-- consolidated import: import ECDSAAdd.Framework.GateInverse

/-! The two raw arithmetic windows clear a data bit, use its name for a
clean carry, then restore it. The complete State and tape are retained. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic

private theorem loan_append_run (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

private theorem loan_triple_run (P Q R : Program) (m : List Bool) (s : State) :
    run (P++Q++R) m s=run R (m.drop (measurementCount P+measurementCount Q))
      (run Q (m.drop (measurementCount P)) (run P m s)) := by
  rw [loan_append_run,loan_append_run,measurementCount_append]

theorem raw_loan_sandwich (prepare P : Program) (retired host : Wire)
    (proper : ProperProgram prepare) (apart : Disjoint (wires prepare) (wires P))
    (hostIn : host∈wires prepare) (s : State) (m : List Bool)
    (retiredBefore : (run prepare m s).basis retired=false)
    (hostBefore : (run prepare m s).basis host=false)
    (retiredAfter : (run P m (run prepare m s)).basis retired=false) :
    run (prepare++renameProgram (Equiv.swap retired host) P++prepare.reverse) m s=
      run P m s := by
  have hostFree : host∉wires P := fun used => Finset.disjoint_left.mp apart hostIn used
  have hostAfter : (run P m (run prepare m s)).basis host=false :=
    (run_preserves_outside P m _ host hostFree).trans hostBefore
  have rebound:=FieldFrameOB5.rebind_swap_run retired host P (run prepare m s) m
    retiredBefore hostBefore retiredAfter hostAfter
  have zero : measurementCount prepare=0 := properProgram_measurementCount prepare proper
  have renamed : measurementCount (renameProgram (Equiv.swap retired host) P)=measurementCount P :=
    (renameProgram_counts _ _).2
  have reverseApart : Disjoint (wires prepare.reverse) (wires P) := by
    simpa only [wires_reverse] using apart
  rw [loan_triple_run]
  simp only [zero,Nat.zero_add,List.drop_zero,renamed]
  rw [rebound,run_disjoint_commute prepare.reverse P reverseApart
    (m.drop (measurementCount P)) m (run prepare m s),
    run_reverse_proper prepare proper s m (m.drop (measurementCount P))]

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeRawAdd =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeProgram
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeLoans

/-! The raw-add loan clears the first target after its carry is computed.
The existing coherent adder restores the borrowed carry for every tape. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic

theorem coherent_prefix_frame (x y carry : List Wire) (a t z last cin : Wire)
    (hy : y.length=x.length) (hc : carry.length=x.length)
    (nd : (x++[a]++y++[t,z]++carry++[last,cin]).Nodup)
    (s : State) (m : List Bool) (top : s.basis z=s.basis t)
    (clean : ∀q∈carry++[last],s.basis q=false) :
    (run (CoherentTail.addPrefix x y carry a t z cin) m s).phase=s.phase ∧
    ∀q,q∉y++[t,z]→
      (run (CoherentTail.addPrefix x y carry a t z cin) m s).basis q=s.basis q := by
  have targetND:(cin::((y++[t,z])++(carry++[last]))).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have apart:List.Disjoint (x++[a,a]) (cin::((y++[t,z])++(carry++[last]))) := by
    have split:((x++[a])++(y++[t,z]++carry++[last,cin])).Nodup:=by
      simpa only [List.append_assoc] using nd
    have dis:=(List.nodup_append'.mp split).2.2
    apply List.disjoint_left.mpr
    intro q hq bad
    apply List.disjoint_left.mp dis
    · simpa only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] using hq
    · simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at bad ⊢
      tauto
  have old:=GuardCompression.addInPlace_readonly_correct (x++[a,a]) (y++[t,z])
    (carry++[last]) cin targetND apart (by simp [hy]) (by simp [hy,hc]) s m clean
  have eq:=CoherentTail.same_records x y carry a t z last cin hy hc nd s m top clean
  rw [eq] at old
  exact ⟨old.1,old.2.1⟩

theorem raw_add_head_loan_eq (x y carry : List Wire)
    (a b sign first parity topSource topTarget topCopy unused retired : Wire)
    (hy : y.length=x.length) (hc : carry.length=x.length)
    (nd : ([a,b,sign,first,parity]++x++[topSource]++y++[topTarget,topCopy]++
      carry++[unused]).Nodup) (member : retired∈carry)
    (s : State) (m : List Bool)
    (parityValue : s.basis parity=(s.basis b ^^ s.basis a ^^ s.basis sign))
    (top : s.basis topCopy=s.basis topTarget)
    (clean : ∀q∈first::(carry++[unused]),s.basis q=false) :
    let clear:Program:=[.CX parity b,.CX a b,.CX sign b]
    let body:=CoherentTail.addPrefix x y carry topSource topTarget topCopy first
    run (majority a b sign first++clear++
        renameProgram (Equiv.swap retired b) body++clear.reverse++
        eraseCarry a b sign first++[.CX a b,.CX sign b]) m s=
      run (majority a b sign first++body++eraseCarry a b sign first++
        [.CX a b,.CX sign b]) m s := by
  let clear:Program:=[.CX parity b,.CX a b,.CX sign b]
  let body:=CoherentTail.addPrefix x y carry topSource topTarget topCopy first
  have counts:=List.nodup_iff_count.mp nd
  have four:[a,b,sign,first].Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=counts q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have split:([a,b,sign,parity]++(x++[topSource]++y++[topTarget,topCopy]++
      carry++[unused,first])).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=counts q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have bodyND:(x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]).Nodup:=
    (List.nodup_append'.mp split).2.1
  have dis:List.Disjoint [a,b,sign,parity]
      (x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]):=
    (List.nodup_append'.mp split).2.2
  have clearNe:parity≠b∧a≠b∧sign≠b:=by
    have hn:([a,b,sign,parity]:List Wire).Nodup:=(List.nodup_append'.mp split).1
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at hn
    tauto
  have proper:ProperProgram clear:=by
    intro i hi
    simp only [clear,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl
    · exact clearNe.1
    · exact clearNe.2.1
    · exact clearNe.2.2
  have bodySupport:wires body⊆
      (x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]).toFinset:=by
    intro q hq
    have h:=CoherentTail.addPrefix_support x y carry topSource topTarget topCopy first q hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have apart:Disjoint (wires clear) (wires body):=by
    apply Finset.disjoint_left.mpr
    intro q left right
    have ls:q∈[a,b,sign,parity]:=by
      simp [clear,wires,Instr.wires] at left
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      tauto
    exact List.disjoint_left.mp dis ls (List.mem_toFinset.mp (bodySupport right))
  have hostIn:b∈wires clear:=by simp [clear,wires,Instr.wires]
  let u:=run (majority a b sign first) [] s
  have firstEq:u=⟨s.phase,writeBit s.basis first
      (carryBit (s.basis a) (s.basis b) (s.basis sign))⟩:=by
    rw [show u=run (majority a b sign first) [] s from rfl,
      majority_correct a b sign first four]
    simp only [clean first (by simp),Bool.false_xor]
  have beforeFirst(q:Wire)(hq:q∈[a,b,sign,parity]++x++[topSource]++y++
      [topTarget,topCopy]++carry++[unused]):q≠first:=by
    intro eq
    have h:=counts first
    have pos:=List.count_pos_iff.mpr (eq ▸ hq)
    simp only [List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h pos
    omega
  have keep(q:Wire)(hq:q∈[a,b,sign,parity]++x++[topSource]++y++
      [topTarget,topCopy]++carry++[unused]):u.basis q=s.basis q:=by
    rw [firstEq]
    simp only [writeBit,Function.update_of_ne (beforeFirst q hq)]
  have bAway(q:Wire)(hq:q∈x++[topSource]++y++[topTarget,topCopy]++carry++
      [unused,first]):q≠b:=by
    intro eq
    exact List.disjoint_left.mp dis (by simp) (eq ▸ hq)
  have clearKeeps(q:Wire)(hq:q≠b)(ms:List Bool):
      (run clear ms u).basis q=u.basis q:=by
    simp [clear,run,writeBit,hq]
  have ready(ms:List Bool):
      (run clear ms u).basis b=false∧
      (run clear ms u).basis topCopy=(run clear ms u).basis topTarget∧
      (∀q∈carry++[unused],(run clear ms u).basis q=false):=by
    refine ⟨?_,?_,?_⟩
    · have rel:u.basis parity=(u.basis b ^^ u.basis a ^^ u.basis sign):=by
        simpa only [keep parity (by simp),keep b (by simp),keep a (by simp),
          keep sign (by simp)] using parityValue
      simp only [clear,run,writeBit,Function.update_self,
        Function.update_of_ne clearNe.2.1,
        Function.update_of_ne clearNe.2.2]
      rw [rel]
      cases u.basis a <;> cases u.basis b <;> cases u.basis sign <;> rfl
    · rw [clearKeeps topCopy (bAway _ (by simp)) ms,
        clearKeeps topTarget (bAway _ (by simp)) ms,keep topCopy (by simp),
        keep topTarget (by simp),top]
    · intro q hq
      rw [clearKeeps q (bAway _ (by simp only [List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false] at hq ⊢;tauto)) ms,
        keep q (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,
          or_false] at hq ⊢;tauto)]
      exact clean q (List.mem_cons_of_mem first hq)
  have equal(ms:List Bool):run (clear++renameProgram (Equiv.swap retired b) body++
      clear.reverse) ms u=run body ms u:=by
    have r:=ready ms
    have after:=coherent_prefix_frame x y carry topSource topTarget topCopy unused first
      hy hc bodyND (run clear ms u) ms r.2.1 r.2.2
    apply raw_loan_sandwich clear body retired b proper apart hostIn u ms
      (r.2.2 retired (by simp [member])) r.1
    exact (after.2 retired (by
      intro used
      have pos:=List.count_pos_iff.mpr used
      have h:=List.nodup_iff_count.mp bodyND retired
      have mem:=List.count_pos_iff.mpr member
      simp only [List.count_cons,List.count_append,List.count_nil] at h pos
      omega)).trans (r.2.2 retired (by simp [member]))
  have zero:=properProgram_measurementCount clear proper
  have middleCount:measurementCount (clear++renameProgram (Equiv.swap retired b) body++
      clear.reverse)=measurementCount body:=by
    simp only [measurementCount_append,measurementCount_reverse,
      (renameProgram_counts _ _).2,zero,Nat.zero_add,Nat.add_zero]
  have eq:=TopCarry.run_mid_congr (majority a b sign first)
    (clear++renameProgram (Equiv.swap retired b) body++clear.reverse) body
    (eraseCarry a b sign first++[.CX a b,.CX sign b]) m s rfl middleCount equal
  simpa only [List.append_assoc] using eq

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeRawAddCall =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeRawAdd

/-! Concrete raw-add call. Seed cleanliness supplies both the parity
relation and the copied sign bit; no new half-call assumption is used. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit

private theorem nonempty_split (xs : List Wire) (h : xs≠[]) :
    xs=xs.getD 0 0::xs.drop 1 := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons a xs => rfl

private theorem zero_surround (A P Q R : Program) (s : State) (m : List Bool)
    (a0 : measurementCount A=0) (r0 : measurementCount R=0)
    (eq : ∀ms,run P ms (run A [] s)=run Q ms (run A [] s)) :
    run (A++P++R) m s=run (A++Q++R) m s := by
  have execute(B:Program):run (A++B++R) m s=
      run R [] (run B m (run A [] s)):=by
    rw [run_append,run_take,run_append,a0,List.take_zero,List.drop_zero]
    exact FifthCarry.no_records R r0 _ _ []
  rw [execute P,execute Q,eq m]

private theorem q6_take255 (L : BalancedCircuit.Layout) (hw : L.Widths) :
    (Q6Structural.q6Carry L).take 255=L.carry.take 254++[L.lower] := by
  simp [Q6Structural.q6Carry,List.take_append,List.take_take,List.length_take,hw.2.2]

theorem raw_add_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (parityValue : s.basis L.parity=(s.basis L.r0 ^^ s.basis (L.ylow.getD 0 0)))
    (top : s.basis L.one=s.basis L.rmsb) (lower : s.basis L.lower=false)
    (clean : ∀q∈L.carry,s.basis q=false) :
    run (Q6LifetimeResearch.rawAdd retired L) m s=run (Q6Structural.rawAdd L) m s := by
  let carries:=(Q6Structural.q6Carry L).take 255
  let a:=L.ylow.getD 0 0
  let b:=L.r0
  let c:=carries.getD 0 0
  let x:=L.ylow.drop 1
  let y:=L.rtail
  let cs:=carries.drop 1
  let unused:=L.carry.getD 255 0
  let S:=signComplement L.sign L.y
  let clear:Program:=[.CX L.parity b,.CX a b,.CX L.sign b]
  let body:=CoherentTail.addPrefix x y cs L.ymsb L.rmsb L.one c
  have cshape:carries=L.carry.take 254++[L.lower]:=q6_take255 L hw
  have clen:carries.length=255:=by rw [cshape];simp [List.length_take,hw.2.2]
  have yne:L.ylow≠[]:=by intro e;have h:=hw.2.1;rw [e] at h;cases h
  have cne:carries≠[]:=by intro e;rw [e] at clen;cases clen
  have ysplit:L.ylow=a::x:=nonempty_split L.ylow yne
  have csplit:carries=c::cs:=nonempty_split carries cne
  have unusedIn:unused∈L.carry:=by
    have h:255<L.carry.length:=by rw [hw.2.2];omega
    dsimp only [unused]
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem _
  have rawND:(L.ylow++[L.ymsb]++L.low++[L.rmsb,L.one]++carries++
      [unused,L.sign,L.parity]).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    rw [CarryBorrow.carry_split L hw] at h
    have take:List.count q (L.carry.take 254)≤List.count q (L.carry.take 255):=by
      simpa only [List.take_take,show min 254 255=254 from rfl] using
        (List.take_sublist 254 (L.carry.take 255)).count_le q
    rw [cshape]
    dsimp only [unused]
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      BalancedCleanup.Layout.y,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have headND:([a,b,L.sign,c,L.parity]++x++[L.ymsb]++y++[L.rmsb,L.one]++
      cs++[unused]).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp rawND q
    rw [ysplit,csplit] at h
    dsimp only [b,y]
    simp only [BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have memberTail:retired∈cs:=by
    change retired∈carries.drop 1
    rw [cshape,List.drop_append]
    have len:(L.carry.take 254).length=254:=by simp [List.length_take,hw.2.2]
    simp only [len,show 1-254=0 from rfl,List.drop_zero,List.mem_append,List.mem_singleton]
    exact Or.inl member
  have cx:x.length=254:=by simp [x,hw.2.1]
  have cy:y.length=254:=hw.1
  have cc:cs.length=254:=by simp [cs,clen]
  have othersND:(([L.sign,L.parity,L.lower,L.one]++L.r++L.carry)++L.y).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have notY(q:Wire)(hq:q∈[L.sign,L.parity,L.lower,L.one]++L.r++L.carry):q∉L.y:=
    fun used=>List.disjoint_left.mp (List.nodup_append'.mp othersND).2.2 hq used
  have cleanupND:L.toLayout.wires.Nodup:=(List.nodup_append'.mp hn).2.1
  have yND:L.y.Nodup:=
    (List.nodup_append'.mp (List.nodup_append'.mp (L.toLayout.dataND cleanupND)).2.1).1
  have signAway:L.sign∉L.y:=notY L.sign (by simp)
  let v:=run S [] s
  have view(q:Wire):v.basis q=
      if q∈L.y then s.basis q ^^ s.basis L.sign else s.basis q:=
    GuardCompression.complement_bit L.sign L.y yND signAway s [] q
  have keep(q:Wire)(hq:q∈[L.sign,L.parity,L.lower,L.one]++L.r++L.carry):
      v.basis q=s.basis q:=by rw [view,if_neg (notY q hq)]
  have aIn:a∈L.y:=by
    change a∈L.ylow++[L.ymsb]
    rw [ysplit]
    simp
  have pv:v.basis L.parity=(v.basis b ^^ v.basis a ^^ v.basis L.sign):=by
    rw [keep L.parity (by simp),keep b (by simp [b,BalancedCleanup.Layout.r,
      BalancedCleanup.Layout.low]),keep L.sign (by simp),view a,if_pos aIn,parityValue]
    cases s.basis L.r0 <;> cases s.basis a <;> cases s.basis L.sign <;> rfl
  have topV:v.basis L.one=v.basis L.rmsb:=by
    rw [keep L.one (by simp),keep L.rmsb (by simp [BalancedCleanup.Layout.r]),top]
  have carryView(q:Wire)(hq:q∈carries++[unused]):v.basis q=false:=by
    have choice:q∈L.carry∨q=L.lower:=by
      rw [cshape] at hq
      simp only [List.mem_append,List.mem_singleton] at hq
      rcases hq with (front|low)|last
      · exact Or.inl (List.mem_of_mem_take front)
      · exact Or.inr low
      · exact Or.inl (last ▸ unusedIn)
    rcases choice with used|eq
    · exact (keep q (by simp [used])).trans (clean q used)
    · subst q
      exact (keep L.lower (by simp)).trans lower
  have cleanV:∀q∈c::(cs++[unused]),v.basis q=false:=by
    intro q hq
    apply carryView q
    rw [csplit]
    simpa only [List.cons_append] using hq
  have middleEq(ms:List Bool):
      run (majority a b L.sign c++clear++renameProgram (Equiv.swap retired b) body++
        clear.reverse++eraseCarry a b L.sign c++[.CX a b,.CX L.sign b]) ms v=
      run (CoherentTail.addPrefix L.ylow L.low carries L.ymsb L.rmsb L.one L.sign) ms v:=by
    have eq:=raw_add_head_loan_eq x y cs a b L.sign c L.parity L.ymsb L.rmsb
      L.one unused retired (cy.trans cx.symm) (cc.trans cx.symm) headND memberTail
      v ms pv topV cleanV
    have shape:CoherentTail.addPrefix L.ylow L.low carries L.ymsb L.rmsb L.one L.sign=
        majority a b L.sign c++body++eraseCarry a b L.sign c++[.CX a b,.CX L.sign b]:=by
      rw [ysplit,csplit]
      rfl
    rw [shape]
    exact eq
  have s0:measurementCount S=0:=(signComplement_counts L.sign L.y).2
  have actual:=zero_surround S
    (majority a b L.sign c++clear++renameProgram (Equiv.swap retired b) body++
      clear.reverse++eraseCarry a b L.sign c++[.CX a b,.CX L.sign b])
    (CoherentTail.addPrefix L.ylow L.low carries L.ymsb L.rmsb L.one L.sign) S s m s0 s0 middleEq
  simpa only [Q6LifetimeResearch.rawAdd,Q6LifetimeResearch.move,Q6Structural.rawAdd,
    FifthCarry.rawAdd,Q6Structural.carryLayout,BalancedCleanup.Layout.low,
    List.getD_cons_zero,List.drop_succ_cons,List.drop_zero,List.append_assoc] using actual

theorem seed_raw_add_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m : List Bool)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (GuardCompression.seed L++Q6LifetimeResearch.rawAdd retired L) m s=
      run (GuardCompression.seed L++Q6Structural.rawAdd L) m s := by
  let u:=run (GuardCompression.seed L) [] s
  have ready:=FifthCarry.seed_ready L hn s [] clean
  have seedND:=BalancedCircuit.seedND L hw hn
  have scalarND:=BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at seedND scalarND
  have parityOne:L.parity≠L.one:=by
    have h:=BalancedCircuit.scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at h
    tauto
  have away(q:Wire)(hq:q∈[L.r0,L.ylow.getD 0 0,L.lower]):
      q≠L.parity∧q≠L.one:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> constructor <;> tauto
  have copy:=ready.1
  have pv:u.basis L.parity=(u.basis L.r0 ^^ u.basis (L.ylow.getD 0 0)):=by
    simp only [u,GuardCompression.seed,run,writeBit,Function.update_self,
      Function.update_of_ne parityOne,
      Function.update_of_ne (away L.r0 (by simp)).1,
      Function.update_of_ne (away L.r0 (by simp)).2,
      Function.update_of_ne (away (L.ylow.getD 0 0) (by simp)).1,
      Function.update_of_ne (away (L.ylow.getD 0 0) (by simp)).2,
      clean L.parity (by simp [BalancedCircuit.work]),Bool.false_xor]
    cases s.basis L.r0 <;> cases s.basis (L.ylow.getD 0 0) <;> rfl
  have low:u.basis L.lower=false:=by
    simp [u,GuardCompression.seed,run,writeBit,(away L.lower (by simp)).1,
      (away L.lower (by simp)).2,clean L.lower (by simp [BalancedCircuit.work])]
  rw [run_append,run_append]
  change run (Q6LifetimeResearch.rawAdd retired L) m u=run (Q6Structural.rawAdd L) m u
  exact raw_add_eq retired L hw hn member u m pv copy low ready.2

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeFold =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeProgram
-- consolidated import: import ECDSAAdd.Submission.Entrant.ParityField1591

/-! The mapped fold reads the lower selector without changing it. The
checked parity-host transport therefore permits the high-bit carry loan. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit

theorem mapped_sub_frame (bits : List MappedBit) (ys carry : List Wire) (cin : Wire)
    (nd : (cin::(ys++carry)).Nodup)
    (source : ∀q∈mappedWires bits,q∉cin::(ys++carry))
    (hl : bits.length=ys.length) (hc : carry.length+1=ys.length)
    (s : State) (m : List Bool) (clean : ∀q∈carry,s.basis q=false) :
    (run (mappedSub bits ys carry cin) m s).phase=s.phase ∧
    ∀q,q∉ys→(run (mappedSub bits ys carry cin) m s).basis q=s.basis q := by
  have ysND:ys.Nodup:=(List.nodup_append'.mp (List.nodup_cons.mp nd).2).1
  have carryAway(q:Wire)(hq:q∈carry):q∉ys:=by
    intro used
    exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp nd).2).2.2 used hq
  let u:=run (notRegister ys) [] s
  have first:u=⟨s.phase,fun q=>if q∈ys then !s.basis q else s.basis q⟩:=
    notRegister_correct ys ysND s []
  have keep(q:Wire)(hq:q∉ys):u.basis q=s.basis q:=by rw [first];simp only [hq,if_false]
  have cleanU:∀q∈carry,u.basis q=false:=
    fun q hq=>(keep q (carryAway q hq)).trans (clean q hq)
  have add:=mappedAdd_correct bits ys carry cin nd source hl hc u m cleanU
  let t:=run (mappedAdd bits ys carry cin) m u
  have zero:measurementCount (notRegister ys)=0:=(notRegister_counts ys).2
  have execute:run (mappedSub bits ys carry cin) m s=run (notRegister ys) [] t:=by
    simp only [mappedSub,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ m s zero,run_append,run_take]
    exact FifthCarry.no_records (notRegister ys) zero _ _ []
  have phaseU:=congrArg State.phase first
  rw [execute,notRegister_correct ys ysND]
  refine ⟨add.1.trans phaseU,?_⟩
  intro q hq
  simp only [hq,if_false]
  exact (add.2.1 q hq).trans (keep q hq)

private def foldBody (add : Bool) (L : BalancedCircuit.Layout) : Program :=
  if add then mappedAdd (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
  else mappedSub (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one

private theorem fold_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq:q∈[L.rmsb,L.lower,L.parity]++L.carry) : q∉L.low := by
  have nd:(([L.rmsb,L.lower,L.parity]++L.carry)++L.low).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro r
    have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) r
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  exact fun used=>List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 hq used

private theorem fold_frame (add : Bool) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (clean : ∀q∈L.carry,s.basis q=false) :
    (run (foldBody add L) m s).phase=s.phase ∧
    ∀q,q∉L.low→(run (foldBody add L) m s).basis q=s.basis q := by
  have nd:(L.one::(L.low++L.carry.take 254)).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    have take:=(List.take_sublist 254 L.carry).count_le q
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have source:∀q∈mappedWires (ShortBiasedFold.lowBits L),q∉L.one::(L.low++L.carry.take 254):=by
    intro q hq used
    have eq:=OneReuse.lowBits_source L q hq
    subst q
    have all:=BalancedCircuit.scalarND L hn
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at all
    simp only [List.mem_cons,List.mem_append] at used
    rcases used with eq|low|carry
    · tauto
    · exact fold_away L hn L.lower (by simp) low
    · exact BalancedCircuit.flagAway L hn L.lower (by simp)
        (by simp [List.mem_of_mem_take carry])
  have length:(ShortBiasedFold.lowBits L).length=L.low.length:=by
    rw [ShortBiasedFold.lowBits_length,(BalancedCleanup.widths L.toLayout hw).1]
  have carryLength:(L.carry.take 254).length+1=L.low.length:=by
    simp [List.length_take,hw.2.2,(BalancedCleanup.widths L.toLayout hw).1]
  have cleanTake:∀q∈L.carry.take 254,s.basis q=false:=
    fun q hq=>clean q (List.mem_of_mem_take hq)
  cases add with
  | false => exact mapped_sub_frame _ _ _ _ nd source length carryLength s m cleanTake
  | true =>
    have result:=mappedAdd_correct _ _ _ _ nd source length carryLength s m cleanTake
    exact ⟨result.1,result.2.1⟩

private theorem fold_host_free (add : Bool) (L : BalancedCircuit.Layout)
    (hn : L.wires.Nodup) : L.rmsb∉wires (foldBody add L) := by
  have all:([L.rmsb,L.lower,L.one]++L.low++L.carry).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have away: L.rmsb∉L.lower::L.one::(L.low++L.carry):=by
    have h:=(List.nodup_cons.mp all).1
    simpa only [List.cons_append,List.nil_append] using h
  intro used
  have bound:wires (foldBody add L)⊆
      (mappedWires (ShortBiasedFold.lowBits L)++L.low++L.carry.take 254++[L.one]).toFinset:=by
    cases add
    · exact mappedSub_wires_subset _ _ _ _
    · exact mappedAdd_wires_subset _ _ _ _
  have h:=List.mem_toFinset.mp (bound used)
  simp only [List.mem_append,List.mem_singleton] at h
  rcases h with ((src|low)|carry)|one
  · exact away (by simp [OneReuse.lowBits_source L L.rmsb src])
  · exact away (by simp [low])
  · exact away (by simp [List.mem_of_mem_take carry])
  · exact away (by simp [one])

theorem fold_eq_old (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (s : State) (m : List Bool) (high : s.basis L.rmsb=s.basis L.lower)
    (clean : ∀q∈L.carry,s.basis q=false) :
    run (Q6LifetimeResearch.fold retired L) m s=run (OneReuse.foldWindow L) m s := by
  let head:Program:=[.CCX L.parity L.lower L.one]
  let P:=foldBody true L
  let u:=run head [] s
  have scalar:=BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  have hostOne:L.rmsb≠L.one:=by tauto
  have lowerOne:L.lower≠L.one:=by tauto
  have keep(q:Wire)(hq:q≠L.one):u.basis q=s.basis q:=by simp [u,head,run,writeBit,hq]
  have cleanU:∀q∈L.carry,u.basis q=false:=by
    intro q hq
    have ne:q≠L.one:=fun e=>BalancedCircuit.flagAway L hn L.one (by simp) (by simp [←e,hq])
    exact (keep q ne).trans (clean q hq)
  have retiredHigh:retired≠L.rmsb:=by
    intro e
    have nd:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) retired
    have pos:=List.count_pos_iff.mpr (List.mem_of_mem_take member)
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at nd
    subst retired
    simp only [beq_self_eq_true,if_true] at nd
    omega
  have same:u.basis L.rmsb=TraceParity5.parity ([L.lower].map u.basis):=by
    simp only [List.map_cons,List.map_nil,TraceParity5.parity,Bool.xor_false]
    rw [keep L.rmsb hostOne,keep L.lower lowerOne]
    exact high
  have loan(ms:List Bool):run (ParityField1591.program [L.lower] retired L.rmsb P) ms u=
      run P ms u:=by
    have frame:=fold_frame true L hw hn u ms cleanU
    apply ParityField1591.run_eq [L.lower] retired L.rmsb P u ms retiredHigh
      (by simp only [List.mem_cons,List.not_mem_nil,or_false];tauto) (fold_host_free true L hn)
      same (cleanU retired (List.mem_of_mem_take member))
      ((frame.2 retired (fold_away L hn retired (by simp [List.mem_of_mem_take member]))).trans
        (cleanU retired (List.mem_of_mem_take member)))
    intro q hq
    have eq:q=L.lower:=List.mem_singleton.mp hq
    subst q
    exact frame.2 L.lower (fold_away L hn L.lower (by simp))
  have count:measurementCount (ParityField1591.program [L.lower] retired L.rmsb P)=
      measurementCount P:=(ParityField1591.counts _ _ _ _).2.1
  have eq:=TopCarry.run_mid_congr head
    (ParityField1591.program [L.lower] retired L.rmsb P) P
    [.CX L.parity L.rmsb,.CX L.parity L.lower,.CX L.rmsb L.lower,
      .measureX L.one [] [.Z L.parity,.CZ L.parity L.rmsb]] m s rfl count loan
  simpa only [Q6LifetimeResearch.fold,Q6LifetimeResearch.move,OneReuse.foldWindow,
    ParityField1591.program,ParityHostTransport5.program,ParityHost5.setup,
    List.map_cons,List.map_nil,foldBody,head,P,List.append_assoc] using eq

private theorem two_setup_commute (a b host : Wire) (outside : host∉[a,b])
    (s : State) (m : List Bool) :
    run (ParityHost5.setup [a,b] host) m s=run (ParityHost5.setup [b,a] host) m s := by
  have reverseOutside:host∉[b,a]:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at outside ⊢
    tauto
  rw [ParityHost5.setup_run [a,b] host s m outside,
    ParityHost5.setup_run [b,a] host s m reverseOutside]
  have parityEq:TraceParity5.parity ([a,b].map s.basis)=
      TraceParity5.parity ([b,a].map s.basis):=by
    simp only [List.map_cons,List.map_nil,TraceParity5.parity,Bool.xor_false]
    exact Bool.xor_comm _ _
  rw [parityEq]

theorem unfold_eq_old (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈L.carry.take 254)
    (s : State) (m : List Bool) (lower : s.basis L.lower=false)
    (clean : ∀q∈L.carry,s.basis q=false) :
    run (Q6LifetimeResearch.unfoldStep retired L) m s=run (OneReuse.unfoldWindow L) m s := by
  let head:Program:=[.CX L.parity L.lower,.CX L.rmsb L.lower,.CCX L.parity L.lower L.one]
  let P:=foldBody false L
  let A:=ParityHost5.setup [L.lower,L.parity] L.rmsb
  let B:=ParityHost5.setup [L.parity,L.lower] L.rmsb
  let u:=run head [] s
  have scalar:=BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  have outside:L.rmsb∉[L.lower,L.parity]:=by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    tauto
  have cleanU:∀q∈L.carry,u.basis q=false:=by
    intro q hq
    have ql:q≠L.lower:=fun e=>BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [←e,hq])
    have qo:q≠L.one:=fun e=>BalancedCircuit.flagAway L hn L.one (by simp) (by simp [←e,hq])
    simp [u,head,run,writeBit,ql,qo,clean q hq]
  have retiredHigh:retired≠L.rmsb:=by
    intro e
    have nd:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) retired
    have pos:=List.count_pos_iff.mpr (List.mem_of_mem_take member)
    simp only [BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil] at nd
    subst retired
    simp only [beq_self_eq_true,if_true] at nd
    omega
  have same:u.basis L.rmsb=TraceParity5.parity ([L.lower,L.parity].map u.basis):=by
    cases hp:s.basis L.parity <;> cases hr:s.basis L.rmsb <;>
      simp_all [u,head,run,writeBit,TraceParity5.parity,ne_comm]
  have loan(ms:List Bool):run (ParityField1591.program [L.lower,L.parity] retired L.rmsb P) ms u=
      run P ms u:=by
    have frame:=fold_frame false L hw hn u ms cleanU
    apply ParityField1591.run_eq [L.lower,L.parity] retired L.rmsb P u ms retiredHigh
      outside (fold_host_free false L hn) same (cleanU retired (List.mem_of_mem_take member))
      ((frame.2 retired (fold_away L hn retired (by simp [List.mem_of_mem_take member]))).trans
        (cleanU retired (List.mem_of_mem_take member)))
    intro q hq
    exact frame.2 q (fold_away L hn q (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
      rcases hq with rfl|rfl <;> simp))
  have actualLoan(ms:List Bool):
      run (A++renameProgram (Equiv.swap retired L.rmsb) P++B) ms u=run P ms u:=by
    apply Eq.trans (b:=run (ParityField1591.program [L.lower,L.parity] retired L.rmsb P) ms u)
    · change run (A++renameProgram (Equiv.swap retired L.rmsb) P++B) ms u=
        run (A++renameProgram (Equiv.swap retired L.rmsb) P++A) ms u
      conv_lhs=>rw [run_append,run_take]
      conv_rhs=>rw [run_append,run_take]
      exact two_setup_commute L.parity L.lower L.rmsb
        (by simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at outside ⊢;tauto) _ _
    · exact loan ms
  have count:measurementCount (A++renameProgram (Equiv.swap retired L.rmsb) P++B)=
      measurementCount P:=by
    simp only [A,B,measurementCount_append,(renameProgram_counts _ _).2,
      (ParityHost5.setup_counts _ _).2.1,Nat.zero_add,Nat.add_zero]
  have eq:=TopCarry.run_mid_congr head
    (A++renameProgram (Equiv.swap retired L.rmsb) P++B) P
    [.CX L.parity L.rmsb,.CX L.rmsb L.lower,.measureX L.one [] [.CZ L.parity L.rmsb]]
    m s rfl count actualLoan
  simpa only [Q6LifetimeResearch.unfoldStep,Q6LifetimeResearch.move,OneReuse.unfoldWindow,
    A,B,ParityHost5.setup,List.map_cons,List.map_nil,foldBody,head,P,List.append_assoc,
    List.cons_append,List.nil_append] using eq

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeForwardPrefix =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeRawAddCall
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeFold

/-! The actual forward prefix reaches the checked old prefix State.
All seed and fold handoffs follow from the unchanged input work frame. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit Arithmetic.BalancedField

def forwardPrefix (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  GuardCompression.seed L++Q6LifetimeResearch.rawAdd retired L++OneReuse.newPrepare L++
    rotateRight (BalancedCircuit.rawTarget L)++Q6LifetimeResearch.fold retired L++
    BalancedCleanup.prepareSign L.toLayout++BiasedCircuit.flipBias L

theorem raw_add_measurements (retired : Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    measurementCount (Q6LifetimeResearch.rawAdd retired L)=measurementCount (FifthCarry.rawAdd L) := by
  have len:(Q6Structural.q6Carry L).length=256:=(Q6StructuralCell.carry_widths L hw).2.2
  have w:=BalancedCleanup.widths L.toLayout hw
  have upper:=CoherentTail.addPrefix_counts (L.ylow.drop 1) (L.low.drop 1)
    (((Q6Structural.q6Carry L).take 255).drop 1) L.ymsb L.rmsb L.one
    (((Q6Structural.q6Carry L).take 255).getD 0 0)
    (by simp [hw.2.1,w.1])
    (by simp [List.length_take,len,hw.2.1])
  rw [(FifthCarry.raw_counts L hw).2.1]
  simp only [Q6LifetimeResearch.rawAdd,Q6LifetimeResearch.move,measurementCount_append,
    measurementCount_reverse,(renameProgram_counts _ _).2,
    (signComplement_counts L.sign L.y).2,upper.2]
  simp only [majority,eraseCarry,measurementCount,List.length_drop,hw.2.1]

theorem fold_measurements (retired : Wire) (L : BalancedCircuit.Layout) :
    measurementCount (Q6LifetimeResearch.fold retired L)=measurementCount (OneReuse.foldWindow L) := by
  simp only [Q6LifetimeResearch.fold,Q6LifetimeResearch.move,OneReuse.foldWindow,
    measurementCount_append,(renameProgram_counts _ _).2]
  rfl

private theorem seeded_raw_fifth_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (s : State) (m : List Bool) (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (GuardCompression.seed L++Q6LifetimeResearch.rawAdd retired L) m s=
      run (GuardCompression.seed L++FifthCarry.rawAdd L) m s := by
  rw [seed_raw_add_eq retired L hw hn member s m clean]
  let u:=run (GuardCompression.seed L) [] s
  have ready:=FifthCarry.seed_ready L hn s [] clean
  have scalar:=BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  have lowerParity:L.lower≠L.parity:=by tauto
  have lowerOne:L.lower≠L.one:=by tauto
  have low:u.basis L.lower=false:=by
    simp [u,GuardCompression.seed,run,writeBit,lowerParity,lowerOne,
      clean L.lower (by simp [BalancedCircuit.work])]
  have index:254<L.carry.length:=by rw [hw.2.2];omega
  have oldMember:L.carry.getD 254 0∈L.carry:=by
    rw [List.getD_eq_getElem _ _ index]
    exact List.getElem_mem _
  rw [TopCarry.run_zero_head _ _ m s rfl,TopCarry.run_zero_head _ _ m s rfl,
    ←Q6Structural.rawAdd_eq L hw hn]
  exact Q6RawBorrow.rawAdd_borrow L hw hn _ oldMember u m ready.1 ready.2 low

theorem forward_prefix_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=X) (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (forwardPrefix retired L) m s=run (FifthCarry2.forwardPrefix L) m s := by
  let newRaw:=GuardCompression.seed L++Q6LifetimeResearch.rawAdd retired L
  let oldRaw:=GuardCompression.seed L++FifthCarry.rawAdd L
  let A:=OneReuse.newPrepare L++rotateRight (BalancedCircuit.rawTarget L)
  let C:=BalancedCleanup.prepareSign L.toLayout++BiasedCircuit.flipBias L
  let v:=run oldRaw m s
  let u:=run A [] v
  let seedState:=run (GuardCompression.seed L) [] s
  have seedReady:=FifthCarry.seed_ready L hn s [] clean
  have firstEq:run newRaw m s=run oldRaw m s:=
    seeded_raw_fifth_eq retired L hw hn member s m clean
  have guardEq:v=run (OneReuse.rawPrefix L) m s:=by
    change run (GuardCompression.seed L++FifthCarry.rawAdd L) m s=
      run (GuardCompression.seed L++GuardCompression.rawAdd L) m s
    rw [TopCarry.run_zero_head _ _ m s rfl,TopCarry.run_zero_head _ _ m s rfl]
    exact FifthCarry.rawAdd_eq L hw hn seedState m seedReady.1 seedReady.2
  have ready:v.basis L.lower=false∧v.basis L.minus=false∧v.basis L.r0=v.basis L.parity:=by
    rw [guardEq]
    exact OneReuse.rawPrefix_ready L hw hn B X Y hx hy s m hs hR hY clean
  have prepared:=OneReusePrefix.prepare_rotate_ready L hw hn v [] [] ready.1 ready.2.1 ready.2.2
  have executeA:u=run (rotateRight (BalancedCircuit.rawTarget L)) []
      (run (OneReusePrefix.prepare L) [] v):=by
    rw [show u=run A [] v from rfl,run_append]
    simp only [List.take_nil,List.drop_nil]
    rfl
  have high:u.basis L.rmsb=u.basis L.lower:=by rw [executeA];exact prepared.2.2.1
  have rawFrame:=GuardCompression.rawAdd_correct L hw hn seedState m
    ((regValue_zero _ _).mpr seedReady.2)
  have rawExecute:v=run (GuardCompression.rawAdd L) m seedState:=by
    rw [guardEq]
    exact TopCarry.run_zero_head _ _ m s rfl
  have carryV:∀q∈L.carry,v.basis q=false:=by
    intro q hq
    rw [rawExecute]
    exact (rawFrame.2.1 q (Q6RawBorrow.rawTarget_away L hn q (by simp [hq]))).trans
      (seedReady.2 q hq)
  have carryU:∀q∈L.carry,u.basis q=false:=by
    intro q hq
    have targetAway:=Q6RawBorrow.rawTarget_away L hn q (by simp [hq])
    have low:q≠L.lower:=fun e=>BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [←e,hq])
    have first:q≠L.r0:=fun e=>targetAway (by simp [BalancedCircuit.rawTarget,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,e])
    have keep:(run (OneReusePrefix.prepare L) [] v).basis q=v.basis q:=by
      simp [OneReusePrefix.prepare,run,writeBit,low,first]
    rw [executeA]
    exact ((rotate_frame (BalancedCircuit.rawTarget L) (run (OneReusePrefix.prepare L) [] v) []).2.1
      q targetAway).trans (keep.trans (carryV q hq))
  have memberTake:retired∈L.carry.take 254:=List.mem_of_mem_drop member
  have middle(ms:List Bool):run (Q6LifetimeResearch.fold retired L) ms u=
      run (OneReuse.foldWindow L) ms u:=fold_eq_old retired L hw hn memberTake u ms high carryU
  have a0:measurementCount A=0:=by
    simp only [A,measurementCount_append,(rotate_counts (BalancedCircuit.rawTarget L)).2.1]
    rfl
  have rawCount:measurementCount newRaw=measurementCount oldRaw:=by
    simp only [newRaw,oldRaw,measurementCount_append,raw_add_measurements retired L hw]
  have foldEq:=TopCarry.run_mid_congr A (Q6LifetimeResearch.fold retired L) (OneReuse.foldWindow L)
    C (m.drop (measurementCount oldRaw)) v a0 (fold_measurements retired L) middle
  have newShape:forwardPrefix retired L=newRaw++(A++Q6LifetimeResearch.fold retired L++C):=by
    simp only [forwardPrefix,newRaw,A,C,List.append_assoc]
  have oldShape:FifthCarry2.forwardPrefix L=oldRaw++(A++OneReuse.foldWindow L++C):=by
    simp only [FifthCarry2.forwardPrefix,oldRaw,A,C,OneReuse.remainder,List.append_assoc]
  rw [newShape,oldShape]
  conv_lhs=>rw [run_append,run_take]
  conv_rhs=>rw [run_append,run_take]
  rw [rawCount,firstEq]
  exact foldEq

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeNormalize =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeLoans

/-! Literal-adder carry loans. The prepared high bit is derived from the
existing centered-value bound. All equalities retain the complete State. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic Arithmetic.BalancedField Arithmetic.BalancedCleanup

private theorem rmsb_not_low (L : Layout) (hn : L.wires.Nodup) : L.rmsb∉L.low := by
  have d:=List.nodup_append'.mp (List.nodup_append'.mp (L.dataND hn)).1
  exact fun h=>List.disjoint_left.mp d.2.2 h (by simp)

private theorem carry_not_low (L : Layout) (hn : L.wires.Nodup)
    (q : Wire) (hq : q∈L.carry) : q∉L.low := by
  have d:=List.nodup_append'.mp (L.dataND hn)
  intro h
  have qr:q∈L.r:=List.mem_append_left _ h
  exact List.disjoint_left.mp d.2.2 qr (List.mem_append_right L.y hq)

private theorem low_frame_eq (lo : List Wire) (s t u : State)
    (phaseT : t.phase=s.phase) (phaseU : u.phase=s.phase)
    (value : regValue lo t.basis=regValue lo u.basis)
    (outsideT : ∀q,q∉lo→t.basis q=s.basis q)
    (outsideU : ∀q,q∉lo→u.basis q=s.basis q) : t=u := by
  apply State.extensionality
  · exact phaseT.trans phaseU.symm
  · funext q
    by_cases hq:q∈lo
    · exact (regValue_eq_iff lo _ _).mp value q hq
    · exact (outsideT q hq).trans (outsideU q hq).symm

theorem prepared_rmsb_zero (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false) :
    (run (prepareSign L) m s).basis L.rmsb=false := by
  have v:=prepareSign_value L hw hn R hr s m hR hz
  have hi:=regValue_highBit L.low L.rmsb (run (prepareSign L) m s).basis
  rw [(widths L hw).1] at hi
  change (run (prepareSign L) m s).basis L.rmsb=true ↔
    2^255≤regValue L.r (run (prepareSign L) m s).basis at hi
  rw [v.1] at hi
  have b:=magnitude_bounds R hr
  have p:=constants
  have cast:=Int.toNat_of_nonneg b.1
  cases e:(run (prepareSign L) m s).basis L.rmsb
  · rfl
  · simp [e] at hi
    omega

theorem normalize_eq_records (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (R : Int) (hr : Centered R) (s : State) (m n : List Bool)
    (hv : regValue L.low s.basis=(magnitude R).toNat)
    (hl : s.basis L.lower=negative R) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (normalize L) m s=run (normalize L) n s := by
  have a:=normalize_value L hw hn R hr s m hv hl ho hc
  have b:=normalize_value L hw hn R hr s n hv hl ho hc
  exact low_frame_eq L.low s _ _ a.1 b.1 (a.2.1.trans b.2.1.symm) a.2.2 b.2.2

theorem normalize_loan_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (retired : Wire) (member : retired∈L.carry) (R : Int) (hr : Centered R)
    (s : State) (m n : List Bool)
    (hv : regValue L.low s.basis=(magnitude R).toNat)
    (hl : s.basis L.lower=negative R) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) (high : s.basis L.rmsb=false) :
    run (renameProgram (Equiv.swap retired L.rmsb) (normalize L)) m s=
      run (normalize L) n s := by
  have a:=normalize_value L hw hn R hr s m hv hl ho hc
  have rebound:=FieldFrameOB5.rebind_swap_run retired L.rmsb (normalize L) s m
    (hc retired member) high
    ((a.2.2 retired (carry_not_low L hn retired member)).trans (hc retired member))
    ((a.2.2 L.rmsb (rmsb_not_low L hn)).trans high)
  exact rebound.trans (normalize_eq_records L hw hn R hr s m n hv hl ho hc)

theorem prepared_normalize_loan_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (retired : Wire) (member : retired∈L.carry) (R : Int) (hr : Centered R)
    (s : State) (m n : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hz : s.basis L.lower=false)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (prepareSign L++renameProgram (Equiv.swap retired L.rmsb) (normalize L)) m s=
      run (prepareSign L++normalize L) n s := by
  let u:=run (prepareSign L) [] s
  have v:=prepareSign_value L hw hn R hr s [] hR hz
  have high:u.basis L.rmsb=false:=prepared_rmsb_zero L hw hn R hr s [] hR hz
  have oneAway:L.one∉L.r:=fun h=>L.flagAway hn L.one (by simp) (by simp [h])
  have oneLower:L.one≠L.lower:=by
    have h:=List.nodup_iff_count.mp (L.flagsND hn) L.one
    intro e
    simp [List.count_cons,e] at h
    omega
  have carryAway(q : Wire)(hq:q∈L.carry):q∉L.r∧q≠L.lower:=by
    have d:=List.nodup_append'.mp (L.dataND hn)
    exact ⟨fun h=>List.disjoint_left.mp d.2.2 h (by simp [hq]),
      fun e=>L.flagAway hn L.lower (by simp) (by simp [←e,hq])⟩
  have one:u.basis L.one=false:=(v.2.2 _ oneAway oneLower).trans ho
  have clean:∀q∈L.carry,u.basis q=false:=
    fun q hq=>(v.2.2 q (carryAway q hq).1 (carryAway q hq).2).trans (hc q hq)
  have low:regValue L.low u.basis=(magnitude R).toNat:=by
    have value:regValue L.r u.basis=(magnitude R).toNat:=v.1
    rw [Layout.r,regValue_append] at value
    simpa [regValue,high] using value
  have zero:=properProgram_measurementCount (prepareSign L) (prepareSign_proper L hn)
  simp only [run_append,zero,List.take_zero,List.drop_zero]
  exact normalize_loan_eq L hw hn retired member R hr u m n low v.2.1 one clean high

theorem unnormalize_eq_records (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (s : State) (m n : List Bool) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) :
    run (unnormalize L) m s=run (unnormalize L) n s := by
  have a:=unnormalize_correct L hw hn s m ho hc
  have b:=unnormalize_correct L hw hn s n ho hc
  exact low_frame_eq L.low s _ _ a.1 b.1 (a.2.1.trans b.2.1.symm) a.2.2 b.2.2

theorem unnormalize_loan_eq (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup)
    (retired : Wire) (member : retired∈L.carry) (s : State) (m n : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (high : s.basis L.rmsb=false) :
    run (renameProgram (Equiv.swap retired L.rmsb) (unnormalize L)) m s=
      run (unnormalize L) n s := by
  have a:=unnormalize_correct L hw hn s m ho hc
  have rebound:=FieldFrameOB5.rebind_swap_run retired L.rmsb (unnormalize L) s m
    (hc retired member) high
    ((a.2.2 retired (carry_not_low L hn retired member)).trans (hc retired member))
    ((a.2.2 L.rmsb (rmsb_not_low L hn)).trans high)
  exact rebound.trans (unnormalize_eq_records L hw hn s m n ho hc)

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeCompareReady =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeNormalize
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeProgram

/-! Actual comparator handoffs. Forward uses the flag that the old
cleanup erases. Inverse derives its zero flag from the old clean work. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit Arithmetic.BalancedField

theorem forward_compare_ready (L : BalancedCircuit.Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (bound : regValue L.r s.basis<2^255)
    (cleared : (run (CarryBorrow.cleanup L) m s).basis L.parity=false) :
    let v:=run (BalancedCleanup.prepareCompare L.toLayout) [] s
    v.basis L.one=false ∧ (∀q∈L.carry,v.basis q=false) ∧
      v.basis L.r0= !(v.basis L.sign ^^ v.basis L.lower) ∧
      v.basis L.parity=decide (regValue L.y v.basis<regValue L.r v.basis) := by
  let v:=run (BalancedCleanup.prepareCompare L.toLayout) [] s
  have ready:=CarryBorrow.prepareCompare_clean L hw hn s [] ho hc
  have relation:=Q6LowerExposure.prepareCompare_low_relation L.toLayout hw
    (List.nodup_append'.mp hn).2.1 (regValue L.r s.basis) bound s [] rfl
  have shape:CarryBorrow.cleanup L=BalancedCleanup.prepareCompare L.toLayout++
      (CarryBorrow.program L++FifthCarry2.cleanupRest L):=by
    simp only [CarryBorrow.cleanup,FifthCarry2.cleanupRest]
  have out:run (CarryBorrow.cleanup L) m s=
      run (FifthCarry2.cleanupRest L) (m.drop (measurementCount (CarryBorrow.program L)))
        (run (CarryBorrow.program L) m v):=by
    rw [shape,TopCarry.run_zero_head _ _ m s (Q6CleanupBorrow.prepare_M L.toLayout),
      run_append,run_take]
  have final:(run (CarryBorrow.program L) m v).basis L.parity=false:=by
    rw [out,run_preserves_outside _ _ _ _ (FifthCarry2.cleanupRest_free L hw hn)] at cleared
    exact cleared
  have oldEq:=CarryBorrow.program_eq L hw hn v m ready.1 ready.2
  have w:=BalancedCleanup.widths L.toLayout hw
  have compare:=compareLt_correct none L.y L.r L.carry L.one L.parity
    (L.toLayout.compareND (List.nodup_append'.mp hn).2.1) (by simp)
    (w.2.2.1.trans w.2.1.symm) (hw.2.2.trans w.2.1.symm) v m ready.1 ready.2
  rw [oldEq,compare.2.2] at final
  simp only [controlValue,Bool.true_and] at final
  have parity:v.basis L.parity=decide (regValue L.y v.basis<regValue L.r v.basis):=by
    cases hp:v.basis L.parity <;>
      cases hd:decide (regValue L.y v.basis<regValue L.r v.basis) <;> simp_all
  exact ⟨ready.1,ready.2,relation,parity⟩

def recoverBefore (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  BalancedCleanup.prepareSign L.toLayout++Q6LifetimeResearch.normalize retired L++
    BalancedCleanup.prepareCompare L.toLayout

theorem recover_before_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈L.carry)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false) :
    run (recoverBefore retired L) m s=run (CarryBorrow.recoverBefore L) [] s := by
  let newP:=BalancedCleanup.prepareSign L.toLayout++Q6LifetimeResearch.normalize retired L
  let oldP:=BalancedCleanup.prepareSign L.toLayout++BalancedCleanup.normalize L.toLayout
  have eq:run newP m s=run oldP [] s:=prepared_normalize_loan_eq L.toLayout hw
    (List.nodup_append'.mp hn).2.1 retired member R hr s m [] hR hl ho hc
  change run (newP++BalancedCleanup.prepareCompare L.toLayout) m s=
    run (oldP++BalancedCleanup.prepareCompare L.toLayout) [] s
  conv_lhs=>rw [run_append,run_take]
  conv_rhs=>rw [run_append,run_take]
  rw [eq]
  simpa only [List.drop_nil] using (FifthCarry.no_records
    (BalancedCleanup.prepareCompare L.toLayout) (Q6CleanupBorrow.prepare_M L.toLayout)
    (run oldP [] s) (m.drop (measurementCount newP)) [])

private theorem normalize_parity_free (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.parity∉wires (BalancedCleanup.normalize L.toLayout) := by
  have scalar:=BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  have one:L.parity≠L.one:=by tauto
  have low:L.parity≠L.lower:=by tauto
  intro used
  have h:=literalConstAdd_wires L.low (L.carry.take 254) L.lower L.one
    BalancedCleanup.negativeLiteral used
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  rcases h with eq|eq|data|carry
  · exact one eq
  · exact low eq
  · exact BalancedCircuit.flagAway L hn L.parity (by simp)
      (by simp [BalancedCleanup.Layout.r,data])
  · exact BalancedCircuit.flagAway L hn L.parity (by simp)
      (by simp [List.mem_of_mem_take carry])

theorem inverse_compare_ready (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈L.carry)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R) (hl : s.basis L.lower=false)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (hp : s.basis L.parity=false) :
    let v:=run (recoverBefore retired L) m s
    v.basis L.one=false ∧ (∀q∈L.carry,v.basis q=false) ∧
      v.basis L.r0= !(v.basis L.sign ^^ v.basis L.lower) ∧ v.basis L.parity=false := by
  rw [recover_before_eq retired L hw hn member R hr s m hR hl ho hc]
  let P:=BalancedCleanup.prepareSign L.toLayout++BalancedCleanup.normalize L.toLayout
  let u:=run P [] s
  let v:=run (CarryBorrow.recoverBefore L) [] s
  have ready:=CarryBorrow.recoverBefore_clean L hw hn s [] ho hc
  have bound:regValue L.r u.basis<2^255:=
    Q6CompareReady.normalized_bound L.toLayout hw (List.nodup_append'.mp hn).2.1
      R hr s [] hR hl ho hc
  have actual:v=run (BalancedCleanup.prepareCompare L.toLayout) [] u:=by
    change run (P++BalancedCleanup.prepareCompare L.toLayout) [] s=_
    rw [run_append]
    simp only [List.take_nil,List.drop_nil]
    rfl
  have relation:v.basis L.r0= !(v.basis L.sign ^^ v.basis L.lower):=by
    rw [actual]
    exact Q6LowerExposure.prepareCompare_low_relation L.toLayout hw
      (List.nodup_append'.mp hn).2.1 (regValue L.r u.basis) bound u [] rfl
  have views:=BalancedCleanup.clifford_parity_away L.toLayout hw (List.nodup_append'.mp hn).2.1
  have free:L.parity∉wires (CarryBorrow.recoverBefore L):=by
    simp only [CarryBorrow.recoverBefore,wires_append,Finset.mem_union,not_or]
    exact ⟨⟨views.1,normalize_parity_free L hn⟩,views.2⟩
  have parity:v.basis L.parity=false:=
    (run_preserves_outside (CarryBorrow.recoverBefore L) [] s L.parity free).trans hp
  exact ⟨ready.1,ready.2,relation,parity⟩

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.ComparatorOutputLeaves =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Half

/-! UNCHECKED Lean 4.28 proof code. Pinned public source d56b1252.
These local leaves remove the comparator's last carry, including every
measurement correction operand. They assert full State equality for
independent tapes. No point-contract hypothesis is changed. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.ComparatorOutputResearch
open Arithmetic Challenge

def oldErase (a b c k t : Wire) : Program :=
  [.X t, .CX t k, .CX k t] ++ eraseCarry a b c k
def newErase (a b c t : Wire) : Program :=
  [.X t, .measureX t [] [.CZ a b, .CZ a c, .CZ b c]]

def oldCompute (a b c k t : Wire) : Program :=
  majority a b c k ++ [.X t, .CX k t] ++ eraseCarry a b c k
def newCompute (a b c t : Wire) : Program :=
  majority a b c t ++ [.X t]

theorem erase_state_eq (a b c k t : Wire) (hn : [a,b,c,k,t].Nodup)
    (s : State) (m n : List Bool) (hk : s.basis k = false)
    (ht : s.basis t = !carryBit (s.basis a) (s.basis b) (s.basis c)) :
    run (newErase a b c t) m s = run (oldErase a b c k t) n s := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, not_or, not_false_eq_true, and_true] at hn
  apply State.extensionality
  · cases ha : s.basis a <;> cases hb : s.basis b <;>
      cases hc : s.basis c <;>
      cases hm : m.headD false <;> cases hr : n.headD false <;>
      simp_all [newErase, oldErase, eraseCarry, run, measureAndCorrect,
        correct, writeBit, carryBit, ne_comm]
  · funext q
    by_cases qk : q = k <;> by_cases qt : q = t <;>
      cases ha : s.basis a <;> cases hb : s.basis b <;>
      cases hc : s.basis c <;>
      simp_all [newErase, oldErase, eraseCarry, run, measureAndCorrect,
        writeBit, carryBit, ne_comm]

theorem compute_state_eq (a b c k t : Wire) (hn : [a,b,c,k,t].Nodup)
    (s : State) (m n : List Bool) (hk : s.basis k = false) :
    run (newCompute a b c t) m s = run (oldCompute a b c k t) n s := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, not_or, not_false_eq_true, and_true] at hn
  apply State.extensionality
  · cases ha : s.basis a <;> cases hb : s.basis b <;>
      cases hc : s.basis c <;> cases ht : s.basis t <;>
      cases hr : n.headD false <;>
      simp_all [newCompute, oldCompute, majority, eraseCarry,
        run, measureAndCorrect, correct, writeBit, ne_comm]
  · funext q
    by_cases qa : q = a <;> by_cases qb : q = b <;>
      by_cases qc : q = c <;> by_cases qk : q = k <;>
      by_cases qt : q = t <;>
      cases ha : s.basis a <;> cases hb : s.basis b <;>
      cases hc : s.basis c <;> cases ht : s.basis t <;>
      simp_all [newCompute, oldCompute, majority, eraseCarry,
        run, measureAndCorrect, writeBit, ne_comm]

end ECDSAAdd.Entrant.ComparatorOutputResearch
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeCompareChain =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeProgram
-- consolidated import: import ECDSAAdd.Submission.Entrant.ComparatorOutputLeaves

/-! Comparator recursion with a direct output leaf. The forward leaf uses
the old cleared-output postcondition. The inverse leaf accepts any flag. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic

private theorem compare_append_run (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

private theorem compare_triple_run (P Q R : Program) (m : List Bool) (s : State) :
    run (P++Q++R) m s=run R (m.drop (measurementCount P+measurementCount Q))
      (run Q (m.drop (measurementCount P)) (run P m s)) := by
  rw [compare_append_run,compare_append_run,measurementCount_append]

private theorem compare_leaf_eq (forward : Bool) (a b cin last target : Wire)
    (nd : (target::cin::([a]++[b]++[last])).Nodup)
    (s : State) (m n : List Bool) (clean : s.basis last=false)
    (post : forward=true →
      (run (Arithmetic.compareChain none [a] [b] [last] cin target) n s).basis target=false) :
    run (Q6LifetimeResearch.compareLeaf forward a b cin target) m s=
      run (Arithmetic.compareChain none [a] [b] [last] cin target) n s := by
  have nd5:[a,b,cin,last,target].Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  cases forward with
  | false =>
    have eq:=ComparatorOutputResearch.compute_state_eq a b cin last target nd5 s m n clean
    simpa only [Q6LifetimeResearch.compareLeaf,if_false,
      ComparatorOutputResearch.newCompute,ComparatorOutputResearch.oldCompute,
      Arithmetic.compareChain,flipBelow,List.append_assoc] using eq
  | true =>
    have old:=compareChain_correct none [a] [b] [last] cin target nd (by simp)
      rfl rfl s n (by simpa using clean)
    have zero:=post rfl
    rw [old.2.2] at zero
    simp only [controlValue,Bool.true_and] at zero
    have top:s.basis target= !decide
        (2^([b]:List Wire).length≤regValue [a] s.basis+regValue [b] s.basis+
          (s.basis cin).toNat):=by
      cases ht:s.basis target <;>
        cases hd:decide (2^([b]:List Wire).length≤regValue [a] s.basis+
          regValue [b] s.basis+(s.basis cin).toNat) <;> simp_all
      omega
    have relation:s.basis target= !carryBit (s.basis a) (s.basis b) (s.basis cin):=by
      cases ha:s.basis a <;> cases hb:s.basis b <;> cases hi:s.basis cin <;>
        simpa [TopCarry.regValue_single,ha,hb,hi,carryBit] using top
    have leaf:=ComparatorOutputResearch.erase_state_eq a b cin last target nd5 s m n clean relation
    have topEq:=TopCarry.compareChainTop_eq [a] [b] [last] cin target nd rfl rfl
      (by simp) s n (by simpa using clean) top
    have actual:run (Q6LifetimeResearch.compareLeaf true a b cin target) m s=
        run (TopCarry.compareChainTop [a] [b] [last] cin target) n s:=by
      simpa only [Q6LifetimeResearch.compareLeaf,if_true,TopCarry.compareChainTop,
        ComparatorOutputResearch.newErase,ComparatorOutputResearch.oldErase,
        eraseCarry,List.append_assoc] using leaf
    exact actual.trans topEq

theorem compare_chain_eq_old (forward : Bool) (x y carry : List Wire) (cin target : Wire)
    (nd : (target::cin::(x++y++carry)).Nodup)
    (hx : x.length=y.length) (hc : carry.length=y.length) (nonempty : y≠[])
    (s : State) (m n : List Bool) (clean : ∀q∈carry,s.basis q=false)
    (post : forward=true →
      (run (Arithmetic.compareChain none x y carry cin target) n s).basis target=false) :
    run (Q6LifetimeResearch.compareChain forward x y carry cin target) m s=
      run (Arithmetic.compareChain none x y carry cin target) n s := by
  induction y generalizing x carry cin s m n with
  | nil => exact absurd rfl nonempty
  | cons b bs ih =>
    cases x with
    | nil => simp at hx
    | cons a xs =>
    cases carry with
    | nil => simp at hc
    | cons c cs =>
    have hx':xs.length=bs.length:=by simpa using hx
    have hc':cs.length=bs.length:=by simpa using hc
    cases bs with
    | nil =>
      have xe:xs=[]:=List.eq_nil_of_length_eq_zero hx'
      have ce:cs=[]:=List.eq_nil_of_length_eq_zero hc'
      subst xs cs
      exact compare_leaf_eq forward a b cin c target nd s m n (clean c (by simp)) post
    | cons b' bs =>
      cases xs with
      | nil => simp at hx'
      | cons a' xs =>
      have counts:=List.nodup_iff_count.mp nd
      have tailND:(target::c::((a'::xs)++(b'::bs)++cs)).Nodup:=by
        apply List.nodup_iff_count.mpr
        intro q
        have h:=counts q
        simp only [List.count_cons,List.count_append] at h ⊢
        omega
      have four:[a,b,cin,c].Nodup:=by
        apply List.nodup_iff_count.mpr
        intro q
        have h:=counts q
        simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
        omega
      have neq:=four
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
        not_or,not_false_eq_true,and_true] at neq
      have ac:a≠c:=by tauto
      have bc:b≠c:=by tauto
      have ic:cin≠c:=by tauto
      have targetAway:target∉cin::((a::a'::xs)++(b::b'::bs)++c::cs):=
        (List.nodup_cons.mp nd).1
      have ta:a≠target:=fun e=>targetAway (by simp [e])
      have tb:b≠target:=fun e=>targetAway (by simp [e])
      have ti:cin≠target:=fun e=>targetAway (by simp [e])
      have tc:target≠c:=fun e=>targetAway (by simp [e])
      have cAway:c∉cs:=by
        intro h
        have h1:=counts c
        have h2:=List.count_pos_iff.mpr h
        simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h1
        omega
      let u:State:=⟨s.phase,writeBit s.basis c
        (carryBit (s.basis a) (s.basis b) (s.basis cin))⟩
      have head(ms:List Bool):run (majority a b cin c) ms s=u:=by
        rw [majority_correct a b cin c four]
        simp only [clean c (by simp),Bool.false_xor]
        rfl
      have keep(q:Wire)(hq:q≠c):u.basis q=s.basis q:=by
        simp [u,writeBit,hq]
      have tailClean:∀q∈cs,u.basis q=false:=by
        intro q hq
        exact (keep q (fun e=>cAway (e ▸ hq))).trans (clean q (by simp [hq]))
      let t:=run (Arithmetic.compareChain none (a'::xs) (b'::bs) cs c target) n u
      have old:=compareChain_correct none (a'::xs) (b'::bs) cs c target tailND
        (by simp) hx' hc' u n tailClean
      have erase(ms:List Bool):run (eraseCarry a b cin c) ms t=
          ⟨t.phase,writeBit t.basis c false⟩:=by
        apply eraseCarry_correct a b cin c ac bc ic t
        · rw [old.2.1 a ta,old.2.1 b tb,old.2.1 cin ti,old.2.1 c (Ne.symm tc),
            keep a ac,keep b bc,keep cin ic]
          simp [u,writeBit]
      have oldRun:run (Arithmetic.compareChain none (a::a'::xs) (b::b'::bs)
          (c::cs) cin target) n s=⟨t.phase,writeBit t.basis c false⟩:=by
        rw [Arithmetic.compareChain,compare_triple_run]
        simp only [show measurementCount (majority a b cin c)=0 from rfl,
          Nat.zero_add,List.drop_zero,head]
        exact erase _
      have tailPost:forward=true→t.basis target=false:=by
        intro h
        have zero:=post h
        rw [oldRun] at zero
        simpa only [writeBit,Function.update_of_ne tc] using zero
      have tailEq:=ih (a'::xs) cs c tailND hx' hc' (by simp) u m n tailClean tailPost
      rw [Q6LifetimeResearch.compareChain,compare_triple_run]
      simp only [show measurementCount (majority a b cin c)=0 from rfl,
        Nat.zero_add,List.drop_zero,head]
      rw [tailEq,oldRun]
      exact erase _

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeComparator =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeCompareChain
-- consolidated import: import ECDSAAdd.Framework.GateInverse

/-! The comparator loan uses a carry after the head carry. All tape lists
and the full incoming State are retained. The hypotheses are internal
arithmetic handoffs, not new point caller conditions. -/
set_option autoImplicit false
namespace ECDSAAdd.Entrant.Q6LifetimeResearch
open Arithmetic RecordedQuantum
attribute [local irreducible] run wires Arithmetic.compareChain compareChain

private theorem append_run (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

private theorem triple_run (P Q R : Program) (m : List Bool) (s : State) :
    run (P++Q++R) m s=run R (m.drop (measurementCount P+measurementCount Q))
      (run Q (m.drop (measurementCount P)) (run P m s)) := by
  rw [append_run,append_run,measurementCount_append]

private theorem zero_tapes (P : Program) (zero : measurementCount P=0)
    (s : State) (m n : List Bool) : run P m s=run P n s := by
  have a : run P m s=run P [] s := by
    simpa only [zero,List.take_zero] using (run_take P m s).symm
  have b : run P [] s=run P n s := by
    simpa only [zero,List.take_zero] using run_take P n s
  exact a.trans b

private theorem x_run (q : Wire) (m : List Bool) (s : State) :
    run [.X q] m s=run [.X q] [] s := by simp only [run]

private theorem x_basis (q w : Wire) (ne : w≠q) (s : State) :
    (run [.X q] [] s).basis w=s.basis w := by
  simp [run,writeBit,Function.update_of_ne ne]

private theorem x_sandwich (q : Wire) (P : Program) (m : List Bool) (s : State) :
    run ([.X q]++P++[.X q]) m s=
      run [.X q] [] (run P m (run [.X q] [] s)) := by
  rw [triple_run]
  simp only [show measurementCount [.X q]=0 from rfl,Nat.zero_add,List.drop_zero,x_run]

private theorem pure_wrap (pre P Q : Program) (zero : measurementCount pre=0)
    (s : State) (m n : List Bool)
    (middle : run P m (run pre [] s)=run Q n (run pre [] s)) :
    run (pre++P++pre) m s=run (pre++Q++pre) n s := by
  rw [triple_run,triple_run]
  simp only [zero,Nat.zero_add,List.drop_zero]
  rw [zero_tapes pre zero s m [],zero_tapes pre zero s n [],middle]
  exact zero_tapes pre zero _ _ _

private theorem chain_ignores_last (forward : Bool) (x y cs : List Wire)
    (cin target last : Wire) (hx : x.length=y.length) (hc : cs.length+1=y.length)
    (nonempty : y≠[]) :
    compareChain forward x y (cs++[last]) cin target=compareChain forward x y cs cin target := by
  induction y generalizing x cs cin with
  | nil => exact (nonempty rfl).elim
  | cons b ys ih =>
    cases x with
    | nil => simp at hx
    | cons a xs =>
      have hx' : xs.length=ys.length := Nat.succ.inj hx
      cases ys with
      | nil =>
        have xe : xs=[] := List.eq_nil_of_length_eq_zero hx'
        subst xs
        simp only [compareChain]
      | cons b' ys =>
        cases xs with
        | nil => simp at hx'
        | cons a' xs =>
          cases cs with
          | nil => simp at hc
          | cons c cs =>
            have hc' : cs.length+1=(b'::ys).length := Nat.succ.inj hc
            have child := ih (a'::xs) cs c hx' hc' (by simp)
            simp only [compareChain,List.cons_append,child]

private theorem borrowed_tail_eq (forward : Bool) (retired host cin target last : Wire)
    (x y cs : List Wire) (nd : (host::target::cin::(x++y++(cs++[last]))).Nodup)
    (hx : x.length=y.length) (hc : (cs++[last]).length=y.length) (nonempty : y≠[])
    (member : retired∈cs) (s : State) (m n : List Bool) (hostOne : s.basis host=true)
    (clean : ∀q∈cs++[last],s.basis q=false)
    (post : forward=true →
      (run (Arithmetic.compareChain none x y (cs++[last]) cin target) n s).basis target=false) :
    run ([.X host]++move retired host (compareChain forward x y cs cin target)++[.X host]) m s=
      run (Arithmetic.compareChain none x y (cs++[last]) cin target) n s := by
  let Q := Arithmetic.compareChain none x y (cs++[last]) cin target
  let P := compareChain forward x y cs cin target
  let v := run [.X host] [] s
  have hostAway := (List.nodup_cons.mp nd).1
  have tailND := (List.nodup_cons.mp nd).2
  have targetAway := (List.nodup_cons.mp tailND).1
  have ht : host≠target := fun e => hostAway (by simp [e])
  have rt : retired≠target := fun e => targetAway (by
    have mem : target∈cs := e ▸ member
    simp only [List.mem_cons,List.mem_append]
    tauto)
  have memberFull : retired∈cs++[last] := List.mem_append_left _ member
  have carryAway (q : Wire) (hq : q∈cs++[last]) : q≠host := by
    intro e
    apply hostAway
    simp only [List.mem_cons,List.mem_append] at hq ⊢
    rw [←e]
    tauto
  have vHost : v.basis host=false := by simp [v,run,writeBit,hostOne]
  have vClean (q : Wire) (hq : q∈cs++[last]) : v.basis q=false :=
    (x_basis host q (carryAway q hq) s).trans (clean q hq)
  have free : host∉wires Q := by
    rw [show Q=Arithmetic.compareChain none x y (cs++[last]) cin target from rfl,
      compareChain_wires none x y (cs++[last]) cin target hx hc]
    simpa only [Option.toList_none,List.nil_append,List.mem_toFinset] using hostAway
  have commute : run Q n v=run [.X host] [] (run Q n s) :=
    CarryBorrow.x_commute_free host Q free s n
  have vPost (h : forward=true) : (run Q n v).basis target=false :=
    ((congrArg (fun t : State => t.basis target) commute).trans
      (x_basis host target (Ne.symm ht) (run Q n s))).trans (post h)
  have facts := compareChain_correct none x y (cs++[last]) cin target tailND (by simp)
    hx hc v n vClean
  have same : run P m v=run Q n v := by
    rw [show P=compareChain forward x y cs cin target from rfl,
      ←chain_ignores_last forward x y cs cin target last hx
        (by simpa only [List.length_append,List.length_singleton] using hc) nonempty]
    exact Q6LifetimeProof.compare_chain_eq_old forward x y (cs++[last]) cin target
      tailND hx hc nonempty v m n vClean vPost
  have retiredOut : (run P m v).basis retired=false := by
    rw [same]
    exact (facts.2.1 retired rt).trans (vClean retired memberFull)
  have hostOut : (run P m v).basis host=false := by
    rw [same]
    exact (facts.2.1 host ht).trans vHost
  have rebound := FieldFrameOB5.rebind_swap_run retired host P v m
    (vClean retired memberFull) vHost retiredOut hostOut
  rw [x_sandwich]
  change run [.X host] [] (run (renameProgram (Equiv.swap retired host) P) m v)=run Q n s
  rw [rebound,same,commute]
  exact properGate_involution (.X host) (by trivial) (run Q n s) [] []

private theorem head_window_eq (forward : Bool) (retired a b c host target last : Wire)
    (x y cs : List Wire)
    (nd : (target::host::((a::x)++(b::y)++(c::(cs++[last])))).Nodup)
    (hx : x.length=y.length) (hc : (cs++[last]).length=y.length) (nonempty : y≠[])
    (member : retired∈cs) (s : State) (m n : List Bool) (hostOne : s.basis host=true)
    (clean : ∀q∈c::(cs++[last]),s.basis q=false)
    (post : forward=true →
      (run (Arithmetic.compareChain none (a::x) (b::y) (c::(cs++[last])) host target) n s).basis target=false) :
    run (majority a b host c++
      ([.X host]++move retired host (compareChain forward x y cs c target)++[.X host])++
      eraseCarry a b host c) m s=
      run (Arithmetic.compareChain none (a::x) (b::y) (c::(cs++[last])) host target) n s := by
  have counts := List.nodup_iff_count.mp nd
  have four : [a,b,host,c].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := counts q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have tailND : (host::target::c::(x++y++(cs++[last]))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := counts q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have carryND : (c::(cs++[last])).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := counts q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have cAway := (List.nodup_cons.mp carryND).1
  have fourNe := four
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at fourNe
  have ac : a≠c := by tauto
  have bc : b≠c := by tauto
  have hcNe : host≠c := by tauto
  have targetAway := (List.nodup_cons.mp nd).1
  have aTarget : a≠target := fun e => targetAway (by simp [e])
  have bt : b≠target := fun e => targetAway (by simp [e])
  have ht : host≠target := fun e => targetAway (by simp [e])
  have ct : c≠target := fun e => targetAway (by simp [e])
  let u : State := ⟨s.phase,writeBit s.basis c
    (carryBit (s.basis a) (s.basis b) (s.basis host))⟩
  have head (records : List Bool) : run (majority a b host c) records s=u := by
    rw [majority_correct a b host c four]
    simp only [clean c (by simp),Bool.false_xor]
    rfl
  have keep (q : Wire) (ne : q≠c) : u.basis q=s.basis q := by
    simp [u,writeBit,Function.update_of_ne ne]
  have tailClean (q : Wire) (hq : q∈cs++[last]) : u.basis q=false :=
    (keep q (fun e => cAway (e ▸ hq))).trans (clean q (List.mem_cons_of_mem _ hq))
  let t := run (Arithmetic.compareChain none x y (cs++[last]) c target) n u
  have old := compareChain_correct none x y (cs++[last]) c target
    (List.nodup_cons.mp tailND).2 (by simp) hx hc u n tailClean
  have erase (records : List Bool) : run (eraseCarry a b host c) records t=
      ⟨t.phase,writeBit t.basis c false⟩ := by
    apply eraseCarry_correct a b host c ac bc hcNe t
    rw [old.2.1 a aTarget,old.2.1 b bt,old.2.1 host ht,old.2.1 c ct,
      keep a ac,keep b bc,keep host hcNe]
    simp [u,writeBit]
  have oldRun : run (Arithmetic.compareChain none (a::x) (b::y) (c::(cs++[last])) host target) n s=
      ⟨t.phase,writeBit t.basis c false⟩ := by
    rw [Arithmetic.compareChain,triple_run]
    simp only [show measurementCount (majority a b host c)=0 from rfl,
      Nat.zero_add,List.drop_zero,head]
    exact erase _
  have tailPost (h : forward=true) : t.basis target=false := by
    have zero := post h
    rw [oldRun] at zero
    simpa only [writeBit,Function.update_of_ne (Ne.symm ct)] using zero
  have window := borrowed_tail_eq forward retired host c target last x y cs tailND hx hc nonempty
    member u m n ((keep host hcNe).trans hostOne) tailClean tailPost
  rw [triple_run]
  simp only [show measurementCount (majority a b host c)=0 from rfl,
    Nat.zero_add,List.drop_zero,head]
  rw [window,oldRun]
  exact erase _

private theorem comparator_window_eq (forward : Bool) (retired a b c host target last : Wire)
    (x y cs : List Wire)
    (nd : (target::host::((a::x)++(b::y)++(c::(cs++[last])))).Nodup)
    (hx : x.length=y.length) (hc : (cs++[last]).length=y.length) (nonempty : y≠[])
    (member : retired∈cs) (s : State) (m n : List Bool) (hostZero : s.basis host=false)
    (clean : ∀q∈c::(cs++[last]),s.basis q=false)
    (flag : forward=true →
      s.basis target=decide (regValue (a::x) s.basis<regValue (b::y) s.basis)) :
    run (notRegister (host::b::y)++majority a b host c++[.X host]++
      move retired host (compareChain forward x y cs c target)++[.X host]++
      eraseCarry a b host c++notRegister (host::b::y)) m s=
      run (compareLt none (a::x) (b::y) (c::(cs++[last])) host target) n s := by
  let pre := notRegister (host::b::y)
  let Q := Arithmetic.compareChain none (a::x) (b::y) (c::(cs++[last])) host target
  let P := majority a b host c++
    ([.X host]++move retired host (compareChain forward x y cs c target)++[.X host])++
    eraseCarry a b host c
  let v := run pre [] s
  have counts := List.nodup_iff_count.mp nd
  have preCarryND : ((host::b::y)++(c::(cs++[last]))).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := counts q
    simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have preND := (List.nodup_append'.mp preCarryND).1
  have apart := (List.nodup_append'.mp preCarryND).2.2
  have invert := notRegister_correct (host::b::y) preND s []
  have hostOne : v.basis host=true := by
    change (run (notRegister (host::b::y)) [] s).basis host=true
    rw [invert]
    change (if host∈host::b::y then !s.basis host else s.basis host)=true
    rw [if_pos (by simp),hostZero]
    rfl
  have vClean (q : Wire) (hq : q∈c::(cs++[last])) : v.basis q=false := by
    have away : q∉host::b::y := fun h => List.disjoint_left.mp apart h hq
    change (run (notRegister (host::b::y)) [] s).basis q=false
    rw [invert]
    change (if q∈host::b::y then !s.basis q else s.basis q)=false
    rw [if_neg away]
    exact clean q hq
  have preZero : measurementCount pre=0 := (notRegister_counts _).2
  have targetAway := (List.nodup_cons.mp nd).1
  have free : target∉wires pre := by
    rw [show pre=notRegister (host::b::y) from rfl,notRegister_wires]
    intro used
    have mem := List.mem_toFinset.mp used
    apply targetAway
    simp only [List.mem_cons,List.mem_append] at mem ⊢
    tauto
  have oldRun : run (compareLt none (a::x) (b::y) (c::(cs++[last])) host target) n s=
      run pre [] (run Q n v) := by
    rw [compareLt,triple_run]
    change run pre (n.drop (measurementCount pre+measurementCount Q))
      (run Q (n.drop (measurementCount pre)) (run pre n s))=run pre [] (run Q n v)
    rw [preZero,List.drop_zero,zero_tapes pre preZero s n []]
    exact zero_tapes pre preZero _ _ []
  have facts := compareLt_correct none (a::x) (b::y) (c::(cs++[last])) host target
    nd (by simp) (by simp only [List.length_cons,hx])
    (by simp only [List.length_cons,hc]) s n hostZero clean
  have post (h : forward=true) : (run Q n v).basis target=false := by
    have zero : (run (compareLt none (a::x) (b::y) (c::(cs++[last])) host target) n s).basis
        target=false := by
      rw [facts.2.2,flag h]
      simp only [controlValue,Bool.true_and,Bool.xor_self]
    rw [oldRun] at zero
    exact (run_preserves_outside pre [] (run Q n v) target free).symm.trans zero
  have middle : run P m v=run Q n v :=
    head_window_eq forward retired a b c host target last x y cs nd hx hc nonempty member
      v m n hostOne vClean post
  have result := pure_wrap pre P Q preZero s m n middle
  simpa only [pre,P,Q,compareLt,List.append_assoc] using result

private theorem q6_comparator_nodup (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    (L.parity::L.one::(L.y++L.r++Q6Structural.q6Carry L)).Nodup := by
  have sub : List.Sublist (L.carry.take 254++L.carry.drop 255) L.carry := by
    have h := (List.Sublist.refl (L.carry.take 254)).append
      (List.drop_sublist_drop_left L.carry (show 254≤255 from by omega))
    simpa only [List.take_append_drop] using h
  apply List.nodup_iff_count.mpr
  intro q
  have whole := List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
  have bound := sub.count_le q
  simp only [Q6Structural.q6Carry,List.count_cons,List.count_append,List.count_nil] at whole bound ⊢
  omega

private theorem q6_clean (L : BalancedCircuit.Layout) (s : State)
    (hc : ∀q∈L.carry,s.basis q=false) (lower0 : s.basis L.lower=false) :
    ∀q∈Q6Structural.q6Carry L,s.basis q=false := by
  intro q h
  simp only [Q6Structural.q6Carry,List.mem_append,List.mem_singleton] at h
  rcases h with (h|rfl)|h
  · exact hc q (List.mem_of_mem_take h)
  · exact lower0
  · exact hc q (List.mem_of_mem_drop h)

private theorem head_drop (xs : List Wire) (ne : xs≠[]) :
    xs=xs.getD 0 0::xs.drop 1 := by
  cases xs with
  | nil => exact (ne rfl).elim
  | cons a xs => rfl

private theorem q6_spine_front (L : BalancedCircuit.Layout) (hw : L.Widths) :
    (Q6Structural.q6Carry L).take 255=L.carry.take 254++[L.lower] := by
  have front : (L.carry.take 254).length=254 := by
    simp only [List.length_take,hw.2.2]
    omega
  have prefixLen : (L.carry.take 254++[L.lower]).length=255 := by
    simp only [List.length_append,List.length_singleton,front]
  unfold Q6Structural.q6Carry
  rw [List.take_append_of_le_length (by omega),List.take_of_length_le (by omega)]

private theorem q6_spine_member (retired : Wire) (L : BalancedCircuit.Layout) (hw : L.Widths)
    (member : retired∈(L.carry.take 254).drop 1) :
    retired∈((Q6Structural.q6Carry L).take 255).drop 1 := by
  have front : (L.carry.take 254).length=254 := by
    simp only [List.length_take,hw.2.2]
    omega
  rw [q6_spine_front L hw,List.drop_append,front]
  change retired∈(L.carry.take 254).drop 1++[L.lower]
  exact List.mem_append_left _ member

private theorem q6_geometry (L : BalancedCircuit.Layout) (hw : L.Widths) :
    (Q6Structural.q6Carry L).length=256 ∧
    ((Q6Structural.q6Carry L).take 255).length=255 ∧
    Q6Structural.q6Carry L=(Q6Structural.q6Carry L).take 255++
      [(Q6Structural.q6Carry L).getD 255 0] := by
  have widths := Q6StructuralCell.carry_widths L hw
  have full : (Q6Structural.q6Carry L).length=256 := widths.2.2
  have spine : ((Q6Structural.q6Carry L).take 255).length=255 := by
    simp only [List.length_take,full]
    omega
  exact ⟨full,spine,CarryBorrow.carry_split (Q6Structural.carryLayout L) widths⟩

/-- Internal comparator boundary. The retired carry is after the live head. -/
theorem compare_eq_plain (retired : Wire) (forward : Bool) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m n : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (lower0 : s.basis L.lower=false)
    (flag : forward=true → s.basis L.parity=decide (regValue L.y s.basis<regValue L.r s.basis)) :
    run (compare retired forward L) m s=
      run (compareLt none L.y L.r (Q6Structural.q6Carry L) L.one L.parity) n s := by
  let spine := (Q6Structural.q6Carry L).take 255
  let last := (Q6Structural.q6Carry L).getD 255 0
  let a := L.y.getD 0 0
  let b := L.r.getD 0 0
  let c := spine.getD 0 0
  let x := L.y.drop 1
  let y := L.r.drop 1
  let cs := spine.drop 1
  have widths := BalancedCleanup.widths L.toLayout hw
  have yn : L.y.length=256 := widths.2.2.1
  have rn : L.r.length=256 := widths.2.1
  have geom := q6_geometry L hw
  have spineLen : spine.length=255 := geom.2.1
  have yne : L.y≠[] := by intro e; rw [e] at yn; contradiction
  have rne : L.r≠[] := by intro e; rw [e] at rn; contradiction
  have cne : spine≠[] := by intro e; rw [e] at spineLen; contradiction
  have yshape : L.y=a::x := head_drop L.y yne
  have rshape : L.r=b::y := head_drop L.r rne
  have cshape : spine=c::cs := head_drop spine cne
  have fullshape : Q6Structural.q6Carry L=c::(cs++[last]) := by
    calc
      Q6Structural.q6Carry L=spine++[last] := geom.2.2
      _=c::(cs++[last]) := by rw [cshape]; rfl
  have nd : (L.parity::L.one::((a::x)++(b::y)++(c::(cs++[last])))).Nodup := by
    rw [←yshape,←rshape,←fullshape]
    exact q6_comparator_nodup L hn
  have hx : x.length=y.length := by
    simp only [x,y,List.length_drop,yn,rn]
  have hcs : (cs++[last]).length=y.length := by
    simp only [cs,y,List.length_append,List.length_singleton,List.length_drop,spineLen,rn]
  have tailNonempty : y≠[] := by
    intro e
    have len : y.length=255 := by simp only [y,List.length_drop,rn]
    rw [e] at len
    contradiction
  have tailMember : retired∈cs := q6_spine_member retired L hw member
  have clean : ∀q∈c::(cs++[last]),s.basis q=false := by
    rw [←fullshape]
    exact q6_clean L s hc lower0
  have flag' (h : forward=true) : s.basis L.parity=
      decide (regValue (a::x) s.basis<regValue (b::y) s.basis) := by
    rw [←yshape,←rshape]
    exact flag h
  have result := comparator_window_eq forward retired a b c L.one L.parity last x y cs
    nd hx hcs tailNonempty tailMember s m n ho clean flag'
  have sourceShape : compare retired forward L=
      notRegister (L.one::b::y)++majority a b L.one c++[.X L.one]++
      move retired L.one (compareChain forward x y cs c L.parity)++[.X L.one]++
      eraseCarry a b L.one c++notRegister (L.one::b::y) := by
    unfold compare
    change notRegister (L.one::L.r)++majority a b L.one c++[.X L.one]++
      move retired L.one (compareChain forward x y cs c L.parity)++[.X L.one]++
      eraseCarry a b L.one c++notRegister (L.one::L.r)=_
    rw [rshape]
  rw [sourceShape]
  have targetShape : compareLt none L.y L.r (Q6Structural.q6Carry L) L.one L.parity=
      compareLt none (a::x) (b::y) (c::(cs++[last])) L.one L.parity := by
    rw [yshape,rshape,fullshape]
  rw [targetShape]
  exact result

/-- Match the existing comparator frame, with independent record lists. -/
theorem compare_eq_reference (retired : Wire) (forward : Bool) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m n : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (lower0 : s.basis L.lower=false)
    (flag : forward=true → s.basis L.parity=decide (regValue L.y s.basis<regValue L.r s.basis)) :
    run (compare retired forward L) m s=
      run (if forward then Q6Structural.compareForward L else Q6Structural.compareInverse L) n s := by
  have plain := compare_eq_plain retired forward L hw hn member s m n ho hc lower0 flag
  let spine := (Q6Structural.q6Carry L).take 255
  let last := (Q6Structural.q6Carry L).getD 255 0
  have geom := q6_geometry L hw
  have split : Q6Structural.q6Carry L=spine++[last] := geom.2.2
  have spineLen : spine.length=255 := geom.2.1
  have ne : spine≠[] := by intro e; rw [e] at spineLen; contradiction
  have widths := BalancedCleanup.widths L.toLayout hw
  have nd : (L.parity::L.one::(L.y++L.r++(spine++[last]))).Nodup := by
    rw [←split]
    exact q6_comparator_nodup L hn
  have hx : L.y.length=L.r.length := widths.2.2.1.trans widths.2.1.symm
  have hs : spine.length+1=L.r.length := by rw [spineLen,widths.2.1]
  have clean : ∀q∈spine++[last],s.basis q=false := by
    rw [←split]
    exact q6_clean L s hc lower0
  have reference : run (if forward then Q6Structural.compareForward L
      else Q6Structural.compareInverse L) n s=
      run (compareLt none L.y L.r (Q6Structural.q6Carry L) L.one L.parity) n s := by
    cases forward
    · have eq := CarryBorrow.compare_eq L.y L.r spine L.one L.parity last ne nd hx hs s n ho clean
      simpa only [Q6Structural.compareInverse,Q6Structural.carryLayout,CarryBorrow.program,
        Bool.false_eq_true,if_false,←split] using eq
    · have eq := TopCarryBorrow.compare_eq L.y L.r spine L.one L.parity last ne nd hx hs
        (by rw [widths.2.1]; omega) s n ho clean (flag rfl)
      simpa only [Q6Structural.compareForward,Q6Structural.carryLayout,TopCarryBorrow.program,
        if_true,←split] using eq
  exact plain.trans reference.symm

end ECDSAAdd.Entrant.Q6LifetimeResearch
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeCompareWindow =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeComparator

/-! Exposed comparator windows use the existing low relation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit Arithmetic.BalancedField
attribute [local irreducible] run

theorem compare_window_eq (retired : Wire) (forward : Bool) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m n : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (relation : s.basis L.r0= !(s.basis L.sign ^^ s.basis L.lower))
    (flag : forward=true →
      s.basis L.parity=decide (regValue L.y s.basis<regValue L.r s.basis)) :
    run (Q6StructuralCell.exposure L++Q6LifetimeResearch.compare retired forward L++
      (Q6StructuralCell.exposure L).reverse) m s=
      run (if forward then TopCarryBorrow.program L else CarryBorrow.program L) n s := by
  let E:=Q6StructuralCell.exposure L
  let u:=run E [] s
  let P:=if forward then Q6Structural.compareForward L else Q6Structural.compareInverse L
  have scalar:=BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  have sl:L.sign≠L.lower:=by tauto
  have ol:L.one≠L.lower:=by tauto
  have pl:L.parity≠L.lower:=by tauto
  have lowerR:L.lower∉L.r:=fun used=>BalancedCircuit.flagAway L hn L.lower
    (by simp) (by simp [used])
  have lowerY:L.lower∉L.y:=fun used=>BalancedCircuit.flagAway L hn L.lower
    (by simp) (by simp [used])
  have rl:L.r0≠L.lower:=fun eq=>lowerR (by
    simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,←eq])
  have expose:=Q6LowerExposure.expose_correct L.sign L.lower L.r0 sl rl s [] relation
  have one:u.basis L.one=false:=(expose.2.2 _ ol).trans ho
  have carry:∀q∈L.carry,u.basis q=false:=by
    intro q hq
    have ql:q≠L.lower:=fun eq=>BalancedCircuit.flagAway L hn L.lower
      (by simp) (by simp [←eq,hq])
    exact (expose.2.2 q ql).trans (hc q hq)
  have values:regValue L.y u.basis=regValue L.y s.basis ∧
      regValue L.r u.basis=regValue L.r s.basis:=by
    constructor
    · apply regValue_congr
      intro q hq
      exact expose.2.2 q (fun eq=>lowerY (eq ▸ hq))
    · apply regValue_congr
      intro q hq
      exact expose.2.2 q (fun eq=>lowerR (eq ▸ hq))
  have flagU:forward=true →
      u.basis L.parity=decide (regValue L.y u.basis<regValue L.r u.basis):=by
    intro h
    rw [values.1,values.2]
    exact (expose.2.2 _ pl).trans (flag h)
  have body:run (Q6LifetimeResearch.compare retired forward L) m u=run P n u:=
    Q6LifetimeResearch.compare_eq_reference retired forward L hw hn member u m n
      one carry expose.2.1 flagU
  have e0:measurementCount E=0:=(Q6LowerExposure.expose_counts _ _ _).2
  have er0:measurementCount E.reverse=0:=by rw [measurementCount_reverse,e0]
  have execute (B : Program) (records : List Bool):
      run (E++B++E.reverse) records s=run E.reverse [] (run B records u):=by
    rw [List.append_assoc,run_append,e0,List.take_zero,List.drop_zero,run_append,run_take]
    exact FifthCarry.no_records E.reverse er0 _ _ []
  have replaced:run (E++Q6LifetimeResearch.compare retired forward L++E.reverse) m s=
      run (E++P++E.reverse) n s:=by
    rw [execute,execute,body]
  have index:254<L.carry.length:=by rw [hw.2.2];omega
  have oldMember:L.carry.getD 254 0∈L.carry:=by
    rw [List.getD_eq_getElem _ _ index]
    exact List.getElem_mem _
  have old:run (E++P++E.reverse) n s=
      run (if forward then TopCarryBorrow.program L else CarryBorrow.program L) n s:=by
    cases forward
    · simpa only [P,Bool.false_eq_true,if_false,E,Q6StructuralCell.exposure,
        ←Q6Structural.compareInverse_eq L hw hn,Q6ComparatorBorrow.borrowed] using
        Q6ComparatorBorrow.actual_inverse_compare_borrow L hw hn
          (L.carry.getD 254 0) oldMember s n ho hc relation
    · simpa only [P,if_true,E,Q6StructuralCell.exposure,
        ←Q6Structural.compareForward_eq L hw hn,Q6ComparatorBorrow.borrowed] using
        Q6ComparatorBorrow.actual_forward_compare_borrow L hw hn
          (L.carry.getD 254 0) oldMember s n ho hc relation (flag rfl)
  exact replaced.trans old

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeForward =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeForwardPrefix
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeCompareReady
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeCompareWindow

/-! The literal forward program retains the old complete State contract. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit Arithmetic.BalancedField
attribute [local irreducible] run

def forwardBefore (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  BalancedCleanup.prepareCompare L.toLayout++Q6StructuralCell.exposure L++
    Q6LifetimeResearch.compare retired true L++(Q6StructuralCell.exposure L).reverse++
    (BalancedCleanup.prepareCompare L.toLayout).reverse

def forwardCleanup (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  forwardBefore retired L++Q6LifetimeResearch.unnormalize retired false L++
    (BalancedCleanup.prepareSign L.toLayout).reverse

private def oldBefore (L : BalancedCircuit.Layout) : Program :=
  BalancedCleanup.prepareCompare L.toLayout++CarryBorrow.program L++
    (BalancedCleanup.prepareCompare L.toLayout).reverse

private def clearedState (L : BalancedCircuit.Layout) (s : State) : State :=
  ⟨s.phase,writeBit s.basis L.parity false⟩

private theorem scalar_parity_away (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.one≠L.parity ∧ L.rmsb≠L.parity := by
  have nd:=BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  constructor <;> tauto

private theorem pure_surround (A B : Program) (s : State) (records : List Bool)
    (zero : measurementCount A=0) :
    run (A++B++A.reverse) records s=
      run A.reverse [] (run B records (run A [] s)) := by
  rw [List.append_assoc,run_append,zero,List.take_zero,List.drop_zero,run_append,run_take]
  exact FifthCarry.no_records A.reverse (by rw [measurementCount_reverse,zero]) _ _ []

private theorem old_before_eq (L : BalancedCircuit.Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (s : State) (records : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (flag : let v:=run (BalancedCleanup.prepareCompare L.toLayout) [] s
      v.basis L.parity=decide (regValue L.y v.basis<regValue L.r v.basis)) :
    run (oldBefore L) records s=clearedState L s := by
  let P:=BalancedCleanup.prepareCompare L.toLayout
  let v:=run P [] s
  let t:=run (CarryBorrow.program L) records v
  have ready:=CarryBorrow.prepareCompare_clean L hw hn s [] ho hc
  have cnd: L.toLayout.wires.Nodup:=(List.nodup_append'.mp hn).2.1
  have w:=BalancedCleanup.widths L.toLayout hw
  have cmp:=compareLt_correct none L.y L.r L.carry L.one L.parity
    (L.toLayout.compareND cnd) (by simp) (w.2.2.1.trans w.2.1.symm)
    (hw.2.2.trans w.2.1.symm) v records ready.1 ready.2
  have old:=CarryBorrow.program_eq L hw hn v records ready.1 ready.2
  have frame:BalancedCleanup.Except L.parity t v:=by
    change BalancedCleanup.Except L.parity (run (CarryBorrow.program L) records v) v
    rw [old]
    exact ⟨cmp.1,cmp.2.1⟩
  have flagValue:v.basis L.parity=decide (regValue L.y v.basis<regValue L.r v.basis):=flag
  have target:t.basis L.parity=false:=by
    change (run (CarryBorrow.program L) records v).basis L.parity=false
    rw [old,cmp.2.2]
    simp only [controlValue,Bool.true_and,flagValue,Bool.xor_self]
  have free:L.parity∉wires P:=
    (BalancedCleanup.clifford_parity_away L.toLayout hw cnd).2
  have inverse:=BalancedCleanup.inverse_except P
    (BalancedCleanup.prepareCompare_proper L.toLayout cnd) L.parity free s t [] [] frame
  have targetAfter:(run P.reverse [] t).basis L.parity=false:=
    (run_preserves_outside P.reverse [] t L.parity (by rw [wires_reverse];exact free)).trans target
  rw [show oldBefore L=P++CarryBorrow.program L++P.reverse from rfl,
    pure_surround P _ s records (Q6CleanupBorrow.prepare_M L.toLayout)]
  apply State.extensionality
  · exact inverse.1
  · funext q
    by_cases eq:q=L.parity
    · subst q
      simpa only [clearedState,writeBit,Function.update_self] using targetAfter
    · simpa only [clearedState,writeBit,Function.update_of_ne eq] using inverse.2 q eq

theorem forward_before_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m n : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (bound : regValue L.r s.basis<2^255)
    (cleared : (run (CarryBorrow.cleanup L) n s).basis L.parity=false) :
    run (forwardBefore retired L) m s=clearedState L s := by
  let P:=BalancedCleanup.prepareCompare L.toLayout
  let v:=run P [] s
  let W:=Q6StructuralCell.exposure L++Q6LifetimeResearch.compare retired true L++
    (Q6StructuralCell.exposure L).reverse
  have ready:=forward_compare_ready L hw hn s n ho hc bound cleared
  have window:run W m v=run (CarryBorrow.program L) [] v:=by
    have a:=compare_window_eq retired true L hw hn member v m [] ready.1
      ready.2.1 ready.2.2.1 (fun _=>ready.2.2.2)
    have b:run (TopCarryBorrow.program L) [] v=run (CarryBorrow.program L) [] v:=
      (TopCarryBorrow.program_eq L hw hn v [] ready.1 ready.2.1 ready.2.2.2).trans
        (CarryBorrow.program_eq L hw hn v [] ready.1 ready.2.1).symm
    exact a.trans b
  have shape:forwardBefore retired L=P++W++P.reverse:=by
    simp only [forwardBefore,P,W,List.append_assoc]
  have replaced:run (forwardBefore retired L) m s=run (oldBefore L) [] s:=by
    rw [shape,show oldBefore L=P++CarryBorrow.program L++P.reverse from rfl,
      pure_surround P W s m (Q6CleanupBorrow.prepare_M L.toLayout),
      pure_surround P _ s [] (Q6CleanupBorrow.prepare_M L.toLayout),window]
  exact replaced.trans (old_before_eq L hw hn s [] ho hc ready.2.2.2)

theorem forward_cleanup_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1) (s : State) (m n : List Bool)
    (ho : s.basis L.one=false) (hc : ∀q∈L.carry,s.basis q=false)
    (bound : regValue L.r s.basis<2^255)
    (cleared : (run (CarryBorrow.cleanup L) n s).basis L.parity=false) :
    run (forwardCleanup retired L) m s=run (CarryBorrow.cleanup L) n s := by
  let u:=clearedState L s
  let Q:=(BalancedCleanup.prepareSign L.toLayout).reverse
  let U:=BalancedCleanup.unnormalize L.toLayout
  have ready:=forward_compare_ready L hw hn s n ho hc bound cleared
  have oldState:run (oldBefore L) n s=u:=old_before_eq L hw hn s n ho hc ready.2.2.2
  have newState:run (forwardBefore retired L) m s=u:=
    forward_before_eq retired L hw hn member s m n ho hc bound cleared
  have away:=scalar_parity_away L hn
  have one:u.basis L.one=false:=by
    simpa only [u,clearedState,writeBit,Function.update_of_ne away.1] using ho
  have carry:∀q∈L.carry,u.basis q=false:=by
    intro q hq
    have ne:q≠L.parity:=fun eq=>BalancedCircuit.flagAway L hn L.parity
      (by simp) (by simp [←eq,hq])
    simpa only [u,clearedState,writeBit,Function.update_of_ne ne] using hc q hq
  have highInput:s.basis L.rmsb=false:=by
    have high:=regValue_highBit L.low L.rmsb s.basis
    rw [(BalancedCleanup.widths L.toLayout hw).1] at high
    change s.basis L.rmsb=true ↔ 2^255≤regValue L.r s.basis at high
    cases bit:s.basis L.rmsb
    · rfl
    · have bad:=high.mp bit
      omega
  have high:u.basis L.rmsb=false:=by
    simpa only [u,clearedState,writeBit,Function.update_of_ne away.2] using highInput
  have memberCarry:retired∈L.carry:=
    List.mem_of_mem_take (List.mem_of_mem_drop member)
  have sameU:run (Q6LifetimeResearch.unnormalize retired false L)
      (m.drop (measurementCount (forwardBefore retired L))) u=
      run U (n.drop (measurementCount (oldBefore L))) u:=by
    exact unnormalize_loan_eq L.toLayout hw (List.nodup_append'.mp hn).2.1 retired
      memberCarry u _ _ one carry high
  have zero:measurementCount Q=0:=by
    rw [measurementCount_reverse]
    exact properProgram_measurementCount _
      (BalancedCleanup.prepareSign_proper L.toLayout (List.nodup_append'.mp hn).2.1)
  have execute (A B : Program) (records : List Bool):
      run (A++B++Q) records s=
      run Q [] (run B (records.drop (measurementCount A)) (run A records s)):=by
    rw [List.append_assoc,run_append,run_take,run_append,run_take]
    exact FifthCarry.no_records Q zero _ _ []
  have oldShape:CarryBorrow.cleanup L=oldBefore L++U++Q:=by
    simp only [CarryBorrow.cleanup,oldBefore,U,Q,List.append_assoc]
  rw [forwardCleanup,oldShape,execute,execute,newState,oldState,sameU]

private theorem forward_records (L : BalancedCircuit.Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=X) (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (FifthCarry.forward L) m s=run (FifthCarry.forward L) n s := by
  have a:=FifthCarry.forward_correct L hw hn B X Y hx hy s m hs hR hY clean
  have b:=FifthCarry.forward_correct L hw hn B X Y hx hy s n hs hR hY clean
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases used:q∈L.r
    · exact (regValue_eq_iff L.r _ _).mp (a.2.1.trans b.2.1.symm) q used
    · exact (a.2.2.2 q used).trans (b.2.2.2 q used).symm

theorem forward_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=X) (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (Q6LifetimeResearch.forward retired false L) m s=run (FifthCarry.forward L) n s := by
  let v:=run (FifthCarry2.forwardPrefix L) m s
  let records:=m.drop (measurementCount (FifthCarry2.forwardPrefix L))
  have old:=FifthCarry.forward_correct L hw hn B X Y hx hy s m hs hR hY clean
  have oldShape:FifthCarry.forward L=FifthCarry2.forwardPrefix L++CarryBorrow.cleanup L:=by
    simp only [FifthCarry.forward,FifthCarry2.forwardPrefix,List.append_assoc]
  have oldRun:run (FifthCarry.forward L) m s=run (CarryBorrow.cleanup L) records v:=by
    rw [oldShape,run_append,run_take]
  have ready:=FifthCarry.forward_prefix_clean L hw hn B X Y hx hy s (false::m) hs hR hY clean
  rw [←FifthCarry2.forwardPrefix_shifted L hw hn s m clean] at ready
  have bound:=Q6CompareReady.forwardPrefix_bound L hw hn B X Y hx hy s m hs hR hY clean
  have cleared:(run (CarryBorrow.cleanup L) records v).basis L.parity=false:=by
    rw [←oldRun]
    exact old.2.2.1 L.parity (by simp [BalancedCircuit.work])
  have core:run (forwardPrefix retired L++forwardCleanup retired L) m s=
      run (FifthCarry.forward L) m s:=by
    rw [run_append,run_take,forward_prefix_eq retired L hw hn member B X Y hx hy s m hs hR hY clean,
      oldRun]
    exact forward_cleanup_eq retired L hw hn member v _ records ready.1 ready.2 bound cleared
  have shape:Q6LifetimeResearch.forward retired false L=
      (forwardPrefix retired L++forwardCleanup retired L)++[.measureX L.one [] []]:=by
    simp only [Q6LifetimeResearch.forward,forwardPrefix,forwardCleanup,forwardBefore,List.append_assoc]
  have same:run (Q6LifetimeResearch.forward retired false L) m s=run (FifthCarry.forward L) m s:=by
    rw [shape,run_append,run_take,core]
    have zero: (run (FifthCarry.forward L) m s).basis L.one=false:=
      old.2.2.1 L.one (by simp [BalancedCircuit.work])
    apply State.extensionality
    · simp [run,measureAndCorrect,correct,zero]
    · funext q
      by_cases eq:q=L.one
      · subst q
        simp [run,measureAndCorrect,correct,writeBit,zero]
      · simp [run,measureAndCorrect,correct,writeBit,Function.update_of_ne eq]
  exact same.trans (forward_records L hw hn B X Y hx hy s m n hs hR hY clean)

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.DependentTop =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Rolling1588Half

/-!
Exact replacement for the affine top of the public c4 inverse raw subtraction.

UNCHECKED: no Lean executable was available when this file was written.
The finite gate experiment is in dependent_top_check.py.  The local full-State
lemmas below have complete proof bodies and quantify over every record tape.

The final two source bits of rawSub are the SAME physical source wire.  The
public TopCarry proof establishes that the final two result bits agree.  At
the top recursion boundary this says

    oldTop = carryBit a b cin XOR b XOR cin.

Measure oldTop with this exact phase polynomial, update b, and copy b to top.
This removes the former top carry, which had been borrowed from parity.
Retaining the parity copy of the lowest raw target bit then permits that low
target to host one ordinary upper carry.  No protected premise is changed:
the top relation is the same internal relation as TopCarry.rawSubT_eq uses.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.C4Lifetime
open Arithmetic RecordedQuantum Challenge

def eraseDependentTop (a b cin top : Wire) : Program :=
  [.measureX top [] [.CZ a b,.CZ a cin,.CZ b cin,.Z b,.Z cin]]

def dependentTop (a b cin top : Wire) : Program :=
  eraseDependentTop a b cin top ++ [.CX a b,.CX cin b,.CX b top]

theorem eraseDependentTop_correct (a b cin top : Wire)
    (nd : [a,b,cin,top].Nodup) (s : State) (m : List Bool)
    (ht : s.basis top =
      (carryBit (s.basis a) (s.basis b) (s.basis cin) ^^ s.basis b ^^ s.basis cin)) :
    run (eraseDependentTop a b cin top) m s =
      ⟨s.phase,writeBit s.basis top false⟩ := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,hat⟩,⟨hbc,hbt⟩,hct⟩ := nd
  have hta := Ne.symm hat
  have htb := Ne.symm hbt
  have htc := Ne.symm hct
  apply State.extensionality
  · cases hm : m.headD false <;>
      cases ha : s.basis a <;> cases hb : s.basis b <;> cases hc : s.basis cin <;>
      simp_all [eraseDependentTop,run,measureAndCorrect,correct,writeBit,
        Function.update,carryBit]
  · simp only [eraseDependentTop,run,measureAndCorrect,correct_basis]

theorem dependentTop_correct (a b cin top : Wire)
    (nd : [a,b,cin,top].Nodup) (s : State) (m : List Bool)
    (ht : s.basis top =
      (carryBit (s.basis a) (s.basis b) (s.basis cin) ^^ s.basis b ^^ s.basis cin)) :
    run (dependentTop a b cin top) m s =
      ⟨s.phase,writeBit
        (writeBit s.basis b (s.basis a ^^ s.basis b ^^ s.basis cin))
        top (s.basis a ^^ s.basis b ^^ s.basis cin)⟩ := by
  have erased := eraseDependentTop_correct a b cin top nd s m ht
  rw [dependentTop,run_append,run_take,erased]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hab,hac,hat⟩,⟨hbc,hbt⟩,hct⟩ := nd
  have hba := Ne.symm hab
  have hca := Ne.symm hac
  have hta := Ne.symm hat
  have hcb := Ne.symm hbc
  have htb := Ne.symm hbt
  have htc := Ne.symm hct
  apply State.extensionality
  · rfl
  · funext q
    by_cases qb : q=b <;> by_cases qt : q=top <;>
      cases ha : s.basis a <;> cases hb : s.basis b <;> cases hc : s.basis cin <;>
      simp_all [run,writeBit,Function.update]

theorem dependentTop_counts (a b cin top : Wire) :
    toffoliCount (dependentTop a b cin top)=0 ∧
    measurementCount (dependentTop a b cin top)=1 ∧
    gateSlots (dependentTop a b cin top)=9 := by
  exact ⟨rfl,rfl,rfl⟩

theorem dependentTop_support (a b cin top : Wire) :
    wires (dependentTop a b cin top) ⊆ [a,b,cin,top].toFinset := by
  intro q hq
  simp [dependentTop,eraseDependentTop,wires,Instr.wires,correctionWires] at hq
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

/-- All lower source bits are distinct from the final repeated source bit;
the final two target bits are explicit.  This is a finite recursive program. -/
def dependentAddPrefix : List Wire → List Wire → List Wire → Wire → Wire → Wire → Wire → Program
  | [],[],[],a,b,top,cin => dependentTop a b cin top
  | x::xs,y::ys,k::ks,a,b,top,cin =>
      majority x y cin k ++ dependentAddPrefix xs ys ks a b top k ++
        eraseCarry x y cin k ++ [.CX x y,.CX cin y]
  | _,_,_,_,_,_,_ => []

theorem dependentAddPrefix_counts (xs ys cs : List Wire) (a b top cin : Wire)
    (hy : ys.length=xs.length) (hc : cs.length=xs.length) :
    toffoliCount (dependentAddPrefix xs ys cs a b top cin)=xs.length ∧
    measurementCount (dependentAddPrefix xs ys cs a b top cin)=xs.length+1 := by
  induction xs generalizing ys cs cin with
  | nil =>
      have ey : ys=[] := List.eq_nil_of_length_eq_zero hy
      have ec : cs=[] := List.eq_nil_of_length_eq_zero hc
      subst ys; subst cs
      exact ⟨(dependentTop_counts a b cin top).1,(dependentTop_counts a b cin top).2.1⟩
  | cons x xs ih =>
      cases ys with
      | nil => simp at hy
      | cons y ys =>
          cases cs with
          | nil => simp at hc
          | cons k cs =>
              have h := ih ys cs k (by simpa using hy) (by simpa using hc)
              simp only [dependentAddPrefix,toffoliCount_append,measurementCount_append]
              norm_num [majority,eraseCarry,toffoliCount,measurementCount,List.length_cons] at h ⊢
              constructor <;> omega

/-- At the call boundary the first complemented target equals `!parity`.
After its first majority, clear it, lend it to an upper carry by an injective
wire permutation, restore it, then erase the first carry normally. -/
def lowTargetLoan : List Wire → List Wire → List Wire → Wire → Wire → Wire → Wire → Wire → Wire → Program
  | x::xs,y::ys,k::ks,a,b,top,cin,parity,missing =>
      majority x y cin k ++ [.X y,.CX parity y] ++
        renameProgram (Equiv.swap missing y) (dependentAddPrefix xs ys ks a b top k) ++
        [.CX parity y,.X y] ++ eraseCarry x y cin k ++ [.CX x y,.CX cin y]
  | _,_,_,_,_,_,_,_,_ => []

/-- Exact candidate replacement for
`[CX r0 parity] ++ Q6Structural.rawSub L ++ [CX rmsb one]`.
Only the scalar `missing` is parameterized; for the proposed new omission use
`base720`.  The first low target is NOT in the upper subprogram. -/
def inverseRawTail (L : BalancedCircuit.Layout) (missing : Wire) : Program :=
  signComplement L.sign L.y ++
  notRegister (BalancedCircuit.rawTarget L) ++
  lowTargetLoan L.ylow L.low ((Q6Structural.carryLayout L).carry.take 255)
    L.ymsb L.rmsb L.one L.sign L.parity missing ++
  notRegister (BalancedCircuit.rawTarget L) ++
  signComplement L.sign L.y ++
  [.CX L.r0 L.parity,.CX (L.ylow.getD 0 0) L.parity,.CX L.rmsb L.one]

end ECDSAAdd.Entrant.C4Lifetime

end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimePrefix =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.DependentTop

/-! Internal inverse-tail replacement. The old plain-adder postcondition
derives the measured top-bit relation. Every record list is allowed. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic RecordedQuantum
open C4Lifetime (dependentTop dependentAddPrefix)

private theorem append_run (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

private theorem triple_run (P Q R : Program) (m : List Bool) (s : State) :
    run (P++Q++R) m s=run R (m.drop (measurementCount P+measurementCount Q))
      (run Q (m.drop (measurementCount P)) (run P m s)) := by
  rw [append_run,append_run,measurementCount_append]

theorem dependent_leaf_eq_add (a t cin z last : Wire) (nd : [a,t,cin,z,last].Nodup)
    (s : State) (m n : List Bool) (clean : s.basis last=false)
    (post : (run (addInPlace [a,a] [t,z] [last] cin) n s).basis z=
      (run (addInPlace [a,a] [t,z] [last] cin) n s).basis t) :
    run (dependentTop a t cin z) m s=run (addInPlace [a,a] [t,z] [last] cin) n s := by
  have nd4 : [a,t,cin,z].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp nd q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  have tz : t≠z := by
    have h:=List.nodup_iff_count.mp nd t
    intro eq
    subst z
    simp only [List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have old:=CoherentTail.old_general a t cin z last nd s n clean
  rw [old] at post
  have side : (s.basis z ^^ s.basis a ^^ carryBit (s.basis a) (s.basis t) (s.basis cin))=
      sumBit (s.basis a) (s.basis t) (s.basis cin) := by
    simpa [writeBit,Function.update,tz,Ne.symm tz] using post
  have relation : s.basis z=
      (carryBit (s.basis a) (s.basis t) (s.basis cin) ^^ s.basis t ^^ s.basis cin) := by
    cases ha:s.basis a <;> cases ht:s.basis t <;> cases hc:s.basis cin <;>
      cases hz:s.basis z <;> simp_all [sumBit,carryBit]
  have new:=C4Lifetime.dependentTop_correct a t cin z nd4 s m relation
  have same :
      (⟨s.phase,writeBit (writeBit s.basis t (s.basis a ^^ s.basis t ^^ s.basis cin))
        z (s.basis a ^^ s.basis t ^^ s.basis cin)⟩ : State)=
      ⟨s.phase,writeBit (writeBit s.basis t (sumBit (s.basis a) (s.basis t) (s.basis cin)))
        z (s.basis z ^^ s.basis a ^^ carryBit (s.basis a) (s.basis t) (s.basis cin))⟩ := by
    simp only [side,sumBit]
  exact new.trans (same.trans old.symm)

private theorem finish_support (a b cin k : Wire) :
    wires (eraseCarry a b cin k++[.CX a b,.CX cin b])⊆[a,b,cin,k].toFinset := by
  intro q h
  simp [eraseCarry,wires,Instr.wires,correctionWires] at h
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem dependent_prefix_same_records (x y carry : List Wire) (a t z last cin : Wire)
    (hy : y.length=x.length) (hc : carry.length=x.length)
    (hn : (x++[a]++y++[t,z]++carry++[last,cin]).Nodup)
    (s : State) (m : List Bool)
    (post : (run (addInPlace (x++[a,a]) (y++[t,z]) (carry++[last]) cin) m s).basis z=
      (run (addInPlace (x++[a,a]) (y++[t,z]) (carry++[last]) cin) m s).basis t)
    (clean : ∀q∈carry++[last],s.basis q=false) :
    run (dependentAddPrefix x y carry a t z cin) m s=
      run (addInPlace (x++[a,a]) (y++[t,z]) (carry++[last]) cin) m s := by
  induction x generalizing y carry cin s m with
  | nil =>
    have ye:y=[] := List.eq_nil_of_length_eq_zero hy
    have ce:carry=[] := List.eq_nil_of_length_eq_zero hc
    subst y;subst carry
    have nd : [a,t,cin,z,last].Nodup := by
      apply List.nodup_iff_count.mpr;intro q
      have h:=List.nodup_iff_count.mp hn q
      simp only [List.nil_append,List.count_append,List.count_cons,List.count_nil] at h ⊢
      omega
    simpa only [List.nil_append,dependentAddPrefix] using
      dependent_leaf_eq_add a t cin z last nd s m m (clean last (by simp)) post
  | cons b xs ih =>
    cases y with
    | nil => simp at hy
    | cons d ys =>
      cases carry with
      | nil => simp at hc
      | cons k ks =>
        have hy' : ys.length=xs.length := by simpa using hy
        have hc' : ks.length=xs.length := by simpa using hc
        have nd : [b,d,cin,k].Nodup := by
          apply List.nodup_iff_count.mpr;intro q
          have h:=List.nodup_iff_count.mp hn q
          simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
          omega
        have nd' : (xs++[a]++ys++[t,z]++ks++[last,k]).Nodup := by
          apply List.nodup_iff_count.mpr;intro q
          have h:=List.nodup_iff_count.mp hn q
          simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
          omega
        have away (q : Wire) (hq : q∈[t,z]++ks++[last]) : q≠k := by
          have ndq:=List.nodup_iff_count.mp hn q
          have pos:=List.count_pos_iff.mpr hq
          intro eq;subst q
          simp only [List.count_append,List.count_cons,List.count_nil] at ndq pos
          simp only [beq_self_eq_true,if_true] at ndq
          omega
        let mid:=run (majority b d cin k) m s
        have mid_eq:=majority_correct b d cin k nd s m
        have clean' : ∀q∈ks++[last],mid.basis q=false := by
          intro q hq
          rw [show mid=run (majority b d cin k) m s from rfl,mid_eq]
          have ne:=away q (by simp only [List.mem_append] at hq ⊢;tauto)
          simpa [writeBit,Function.update,ne] using
            clean q (by simp only [List.mem_append,List.mem_cons] at hq ⊢;tauto)
        have oldM : measurementCount
            (addInPlace (xs++[a,a]) (ys++[t,z]) (ks++[last]) k)=xs.length+1 := by
          have h:=(addInPlace_counts (xs++[a,a]) (ys++[t,z]) (ks++[last]) k
            (by simp [hy']) (by simp [hy',hc'])).2
          simpa [hy'] using h
        have newM : measurementCount (dependentAddPrefix xs ys ks a t z k)=xs.length+1 :=
          (C4Lifetime.dependentAddPrefix_counts xs ys ks a t z k hy' hc').2
        have shape : addInPlace ((b::xs)++[a,a]) ((d::ys)++[t,z]) ((k::ks)++[last]) cin=
            majority b d cin k++addInPlace (xs++[a,a]) (ys++[t,z]) (ks++[last]) k++
              eraseCarry b d cin k++[.CX b d,.CX cin d] := by
          cases xs <;> cases ys <;> rfl
        have majM : measurementCount (majority b d cin k)=0 := rfl
        have free (q : Wire) (hq : q∈[t,z]) :
            q∉wires (eraseCarry b d cin k++[.CX b d,.CX cin d]) := by
          have pp : ([b,d,cin,k]++[t,z]).Nodup := by
            apply List.nodup_iff_count.mpr;intro v
            have h:=List.nodup_iff_count.mp hn v
            simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
            omega
          intro bad
          exact List.disjoint_left.mp (List.nodup_append'.mp pp).2.2
            (List.mem_toFinset.mp (finish_support b d cin k bad)) hq
        have post' :
            (run (addInPlace (xs++[a,a]) (ys++[t,z]) (ks++[last]) k) m mid).basis z=
            (run (addInPlace (xs++[a,a]) (ys++[t,z]) (ks++[last]) k) m mid).basis t := by
          rw [shape] at post
          have regroup :
              ((majority b d cin k++addInPlace (xs++[a,a]) (ys++[t,z]) (ks++[last]) k)++
                eraseCarry b d cin k++[Instr.CX b d,Instr.CX cin d])=
              majority b d cin k++addInPlace (xs++[a,a]) (ys++[t,z]) (ks++[last]) k++
                (eraseCarry b d cin k++[Instr.CX b d,Instr.CX cin d]) := by
            simp only [List.append_assoc]
          rw [regroup,triple_run] at post
          simp only [majM,Nat.zero_add,List.drop_zero] at post
          rw [run_preserves_outside _ _ _ z (free z (by simp)),
            run_preserves_outside _ _ _ t (free t (by simp))] at post
          exact post
        have ih':=ih ys ks k hy' hc' nd' mid m post' clean'
        rw [shape]
        simp only [dependentAddPrefix,append_run,measurementCount_append,
          majM,Nat.zero_add,List.drop_zero,oldM,newM]
        rw [ih']

theorem dependent_prefix_records (x y carry : List Wire) (a t z last cin : Wire)
    (hy : y.length=x.length) (hc : carry.length=x.length)
    (hn : (x++[a]++y++[t,z]++carry++[last,cin]).Nodup)
    (s : State) (m n : List Bool)
    (post : (run (addInPlace (x++[a,a]) (y++[t,z]) (carry++[last]) cin) n s).basis z=
      (run (addInPlace (x++[a,a]) (y++[t,z]) (carry++[last]) cin) n s).basis t)
    (clean : ∀q∈carry++[last],s.basis q=false) :
    run (dependentAddPrefix x y carry a t z cin) m s=
      run (addInPlace (x++[a,a]) (y++[t,z]) (carry++[last]) cin) n s := by
  have nd : (cin::((y++[t,z])++(carry++[last]))).Nodup := by
    apply List.nodup_iff_count.mpr;intro q
    have h:=List.nodup_iff_count.mp hn q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have hd : List.Disjoint (x++[a,a]) (cin::((y++[t,z])++(carry++[last]))) := by
    have h : List.Disjoint (x++[a]) (y++[t,z]++carry++[last,cin]) := by
      have nd' : ((x++[a])++(y++[t,z]++carry++[last,cin])).Nodup := by
        simpa only [List.append_assoc] using hn
      exact (List.nodup_append'.mp nd').2.2
    apply List.disjoint_left.mpr
    intro q hq bad
    apply List.disjoint_left.mp h
    · simpa only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] using hq
    · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at bad ⊢
      tauto
  have independent:=CoherentTail.readonly_record_independent
    (x++[a,a]) (y++[t,z]) (carry++[last]) cin nd hd
    (by simp [hy]) (by simp [hy,hc]) s m n clean
  have post' :
      (run (addInPlace (x++[a,a]) (y++[t,z]) (carry++[last]) cin) m s).basis z=
      (run (addInPlace (x++[a,a]) (y++[t,z]) (carry++[last]) cin) m s).basis t := by
    rw [independent]
    exact post
  exact (dependent_prefix_same_records x y carry a t z last cin hy hc hn s m post' clean).trans independent

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeRawSubHead =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeProgram
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeLoans
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimePrefix

/-! The old complete adder supplies the top-pair relation. The low target
is cleared for the upper carry loan and is restored before head cleanup. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic

theorem addTop_eq_prefix (x y carry : List Wire) (a t z cin : Wire)
    (hy : y.length=x.length) (hc : carry.length=x.length) :
    Q6LifetimeResearch.addTop (x++[a,a]) (y++[t,z]) carry cin =
      C4Lifetime.dependentAddPrefix x y carry a t z cin := by
  induction x generalizing y carry cin with
  | nil =>
    have ye:y=[] := List.eq_nil_of_length_eq_zero hy
    have ce:carry=[] := List.eq_nil_of_length_eq_zero hc
    subst y;subst carry
    rfl
  | cons b xs ih =>
    cases y with
    | nil => simp at hy
    | cons d ys =>
      cases carry with
      | nil => simp at hc
      | cons k ks =>
        have same:=ih ys ks k (by simpa using hy) (by simpa using hc)
        obtain ⟨p,ps,sourceShape⟩:=List.exists_cons_of_ne_nil
          (show xs++[a,a]≠[] by simp)
        have psNe:ps≠[] := by
          intro e
          have h:=congrArg List.length sourceShape
          rw [e] at h
          simp only [List.length_append,List.length_cons,List.length_nil] at h
          omega
        obtain ⟨p',ps',psShape⟩:=List.exists_cons_of_ne_nil psNe
        rw [psShape] at sourceShape
        obtain ⟨q,qs,targetShape⟩:=List.exists_cons_of_ne_nil
          (show ys++[t,z]≠[] by simp)
        simpa only [List.cons_append,sourceShape,targetShape,Q6LifetimeResearch.addTop,
          C4Lifetime.dependentAddPrefix] using
          congrArg (fun P=>majority b d cin k++P++eraseCarry b d cin k++
            [Instr.CX b d,Instr.CX cin d]) same

private theorem prefix_ports (x y carry : List Wire) (a t z last cin : Wire)
    (nd : (x++[a]++y++[t,z]++carry++[last,cin]).Nodup) :
    (cin::((y++[t,z])++(carry++[last]))).Nodup ∧
      List.Disjoint (x++[a,a]) (cin::((y++[t,z])++(carry++[last]))) := by
  constructor
  · apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp nd q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  · have split:((x++[a])++(y++[t,z]++carry++[last,cin])).Nodup := by
      simpa only [List.append_assoc] using nd
    have dis:=(List.nodup_append'.mp split).2.2
    apply List.disjoint_left.mpr
    intro q hq bad
    apply List.disjoint_left.mp dis
    · simpa only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] using hq
    · simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at bad ⊢
      tauto

private theorem prefix_support (x y carry : List Wire) (a t z cin : Wire)
    (hy : y.length=x.length) (hc : carry.length=x.length) :
    wires (C4Lifetime.dependentAddPrefix x y carry a t z cin)⊆
      (x++[a]++y++[t,z]++carry++[cin]).toFinset := by
  induction x generalizing y carry cin with
  | nil =>
    have ye:y=[] := List.eq_nil_of_length_eq_zero hy
    have ce:carry=[] := List.eq_nil_of_length_eq_zero hc
    subst y;subst carry
    intro q used
    have h:=C4Lifetime.dependentTop_support a t cin z used
    simp only [C4Lifetime.dependentAddPrefix] at used
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false,List.nil_append] at h ⊢
    tauto
  | cons b xs ih =>
    cases y with
    | nil => simp at hy
    | cons d ys =>
      cases carry with
      | nil => simp at hc
      | cons k ks =>
        have sub:=ih ys ks k (by simpa using hy) (by simpa using hc)
        have maj:wires (majority b d cin k)={b,d,cin,k} := by
          ext q;simp [majority,wires,Instr.wires];tauto
        intro q used
        simp only [C4Lifetime.dependentAddPrefix,wires_append,Finset.mem_union,
          or_assoc] at used
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false]
        rcases used with h|h|h|h
        · rw [maj] at h
          simp only [Finset.mem_insert,Finset.mem_singleton] at h
          tauto
        · have h':=sub h
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,
            List.not_mem_nil,or_false] at h'
          tauto
        · rw [eraseCarry_wires] at h
          simp only [Finset.mem_insert,Finset.mem_singleton] at h
          tauto
        · simp [wires,Instr.wires] at h
          tauto

private theorem head_append_run (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

private theorem head_triple_run (P Q R : Program) (m : List Bool) (s : State) :
    run (P++Q++R) m s=run R (m.drop (measurementCount P+measurementCount Q))
      (run Q (m.drop (measurementCount P)) (run P m s)) := by
  rw [head_append_run,head_append_run,measurementCount_append]

theorem raw_sub_head_loan_eq (x y carry : List Wire)
    (a b cin first parity topSource topTarget topCopy unused retired : Wire)
    (hy : y.length=x.length) (hc : carry.length=x.length)
    (nd : ([a,b,cin,first,parity]++x++[topSource]++y++[topTarget,topCopy]++
      carry++[unused]).Nodup) (member : retired∈carry)
    (s : State) (m n : List Bool)
    (low : s.basis b= !s.basis parity)
    (clean : ∀q∈first::(carry++[unused]),s.basis q=false)
    (post :
      (run (addInPlace ((a::x)++[topSource,topSource])
        ((b::y)++[topTarget,topCopy]) ((first::carry)++[unused]) cin) n s).basis topCopy=
      (run (addInPlace ((a::x)++[topSource,topSource])
        ((b::y)++[topTarget,topCopy]) ((first::carry)++[unused]) cin) n s).basis topTarget) :
    let clear:Program:=[.X b,.CX parity b]
    let upper:=Q6LifetimeResearch.addTop (x++[topSource,topSource])
      (y++[topTarget,topCopy]) carry first
    run (majority a b cin first++clear++renameProgram (Equiv.swap retired b) upper++
        clear.reverse++eraseCarry a b cin first++[.CX a b,.CX cin b]) m s=
      run (addInPlace ((a::x)++[topSource,topSource])
        ((b::y)++[topTarget,topCopy]) ((first::carry)++[unused]) cin) n s := by
  dsimp only
  rw [addTop_eq_prefix x y carry topSource topTarget topCopy first hy hc]
  let clear:Program:=[.X b,.CX parity b]
  let upper:=C4Lifetime.dependentAddPrefix x y carry topSource topTarget topCopy first
  let oldUpper:=addInPlace (x++[topSource,topSource]) (y++[topTarget,topCopy])
    (carry++[unused]) first
  let finish:=eraseCarry a b cin first++[Instr.CX a b,Instr.CX cin b]
  have counts:=List.nodup_iff_count.mp nd
  have four:[a,b,cin,first].Nodup := by
    apply List.nodup_iff_count.mpr;intro q
    have h:=counts q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have split:([a,b,cin,parity]++(x++[topSource]++y++[topTarget,topCopy]++
      carry++[unused,first])).Nodup := by
    apply List.nodup_iff_count.mpr;intro q
    have h:=counts q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have upperND:(x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]).Nodup :=
    (List.nodup_append'.mp split).2.1
  have dis:List.Disjoint [a,b,cin,parity]
      (x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]) :=
    (List.nodup_append'.mp split).2.2
  have ports:=prefix_ports x y carry topSource topTarget topCopy unused first upperND
  have fullND:((a::x)++[topSource]++(b::y)++[topTarget,topCopy]++
      (first::carry)++[unused,cin]).Nodup := by
    apply List.nodup_iff_count.mpr;intro q
    have h:=counts q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have fullPorts:=prefix_ports (a::x) (b::y) (first::carry)
    topSource topTarget topCopy unused cin fullND
  have parityNe:parity≠b := by
    have small:([a,b,cin,parity]:List Wire).Nodup := (List.nodup_append'.mp split).1
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true] at small
    tauto
  have proper:ProperProgram clear := by
    intro i hi
    simp only [clear,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl
    · trivial
    · exact parityNe
  have support:wires upper⊆
      (x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]).toFinset := by
    intro q used
    have h:=prefix_support x y carry topSource topTarget topCopy first hy hc used
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have oldSupport:wires oldUpper⊆
      (x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]).toFinset := by
    rw [show oldUpper=addInPlace (x++[topSource,topSource]) (y++[topTarget,topCopy])
      (carry++[unused]) first from rfl,addInPlace_wires _ _ _ _ (by simp [hy]) (by simp [hy,hc])]
    intro q used
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at used ⊢
    tauto
  have apartFor(P:Program)(sub:wires P⊆
      (x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]).toFinset):
      Disjoint (wires clear) (wires P) := by
    apply Finset.disjoint_left.mpr
    intro q left right
    have ls:q∈[a,b,cin,parity] := by
      simp [clear,wires,Instr.wires] at left
      simp only [List.mem_cons,List.not_mem_nil,or_false]
      tauto
    exact List.disjoint_left.mp dis ls (List.mem_toFinset.mp (sub right))
  have hostIn:b∈wires clear := by simp [clear,wires,Instr.wires]
  have clearKeeps(v:State)(q:Wire)(hq:q≠b)(ms:List Bool):
      (run clear ms v).basis q=v.basis q := by
    simp [clear,run,writeBit,hq]
  have bAway(q:Wire)(hq:q∈x++[topSource]++y++[topTarget,topCopy]++carry++[unused,first]):q≠b :=
    fun eq=>List.disjoint_left.mp dis (by simp) (eq ▸ hq)
  let u:=run (majority a b cin first) [] s
  have firstEq:u=⟨s.phase,writeBit s.basis first
      (carryBit (s.basis a) (s.basis b) (s.basis cin))⟩ := by
    rw [show u=run (majority a b cin first) [] s from rfl,
      majority_correct a b cin first four]
    simp only [clean first (by simp),Bool.false_xor]
  have beforeFirst(q:Wire)(hq:q∈[a,b,cin,parity]++x++[topSource]++y++
      [topTarget,topCopy]++carry++[unused]):q≠first := by
    intro eq
    have h:=counts first
    have pos:=List.count_pos_iff.mpr (eq ▸ hq)
    simp only [List.count_append,List.count_cons,List.count_nil,beq_self_eq_true,if_true] at h pos
    omega
  have keep(q:Wire)(hq:q∈[a,b,cin,parity]++x++[topSource]++y++
      [topTarget,topCopy]++carry++[unused]):u.basis q=s.basis q := by
    rw [firstEq]
    simp only [writeBit,Function.update_of_ne (beforeFirst q hq)]
  have cleanU:∀q∈carry++[unused],u.basis q=false := by
    intro q hq
    exact (keep q (by simp only [List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false] at hq ⊢;tauto)).trans (clean q (List.mem_cons_of_mem first hq))
  have oldShape:addInPlace ((a::x)++[topSource,topSource])
      ((b::y)++[topTarget,topCopy]) ((first::carry)++[unused]) cin=
      majority a b cin first++oldUpper++finish := by
    cases x <;> cases y <;>
      simp only [oldUpper,finish,List.cons_append,List.nil_append,addInPlace,List.append_assoc]
  have finishFree(q:Wire)(hq:q∈[topTarget,topCopy]):q∉wires finish := by
    have sub:wires finish⊆[a,b,cin,first].toFinset := by
      intro v used
      simp [finish,eraseCarry,wires,Instr.wires,correctionWires] at used
      simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
      tauto
    intro used
    have small:([a,b,cin,first]++[topTarget,topCopy]).Nodup := by
      apply List.nodup_iff_count.mpr;intro v
      have h:=counts v
      simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
      omega
    exact List.disjoint_left.mp (List.nodup_append'.mp small).2.2
      (List.mem_toFinset.mp (sub used)) hq
  have postU:(run oldUpper n u).basis topCopy=(run oldUpper n u).basis topTarget := by
    have h:=post
    rw [oldShape,head_triple_run] at h
    simp only [show measurementCount (majority a b cin first)=0 from rfl,
      Nat.zero_add,List.drop_zero] at h
    rw [FifthCarry.no_records (majority a b cin first) rfl s n []] at h
    rw [run_preserves_outside _ _ _ topCopy (finishFree _ (by simp)),
      run_preserves_outside _ _ _ topTarget (finishFree _ (by simp))] at h
    exact h
  have ready(ms:List Bool):(run clear ms u).basis b=false ∧
      (∀q∈carry++[unused],(run clear ms u).basis q=false) := by
    constructor
    · have rel:u.basis b= !u.basis parity := by
        simpa only [keep b (by simp),keep parity (by simp)] using low
      simp only [clear,run,writeBit,Function.update_self,Function.update_of_ne parityNe]
      rw [rel]
      cases u.basis parity <;> rfl
    · intro q hq
      rw [clearKeeps u q (bAway q (by simp only [List.mem_append,List.mem_cons,
        List.not_mem_nil,or_false] at hq ⊢;tauto)) ms]
      exact cleanU q hq
  have postReady(ms:List Bool):
      (run oldUpper n (run clear ms u)).basis topCopy=
        (run oldUpper n (run clear ms u)).basis topTarget := by
    rw [←run_disjoint_commute clear oldUpper (apartFor oldUpper oldSupport) ms n u,
      clearKeeps _ topCopy (bAway _ (by simp)) ms,
      clearKeeps _ topTarget (bAway _ (by simp)) ms]
    exact postU
  have equal(ms:List Bool):
      run (clear++renameProgram (Equiv.swap retired b) upper++clear.reverse) ms u=
        run oldUpper ms u := by
    have r:=ready ms
    have eqReady:=dependent_prefix_records x y carry topSource topTarget topCopy unused first
      hy hc upperND (run clear ms u) ms n (postReady ms) r.2
    have frame:=GuardCompression.addInPlace_readonly_correct
      (x++[topSource,topSource]) (y++[topTarget,topCopy]) (carry++[unused]) first
      ports.1 ports.2 (by simp [hy]) (by simp [hy,hc]) (run clear ms u) n r.2
    have retiredFree:retired∉y++[topTarget,topCopy] := by
      intro used
      have h:=List.nodup_iff_count.mp upperND retired
      have pos:=List.count_pos_iff.mpr used
      have mem:=List.count_pos_iff.mpr member
      simp only [List.count_append,List.count_cons,List.count_nil] at h pos
      omega
    have loan:=raw_loan_sandwich clear upper retired b proper (apartFor upper support)
      hostIn u ms (r.2 retired (by simp [member])) r.1
      (by rw [show run upper ms (run clear ms u)=run oldUpper n (run clear ms u) from eqReady]
          exact (frame.2.1 retired retiredFree).trans (r.2 retired (by simp [member])))
    have prefixEq:=dependent_prefix_records x y carry topSource topTarget topCopy unused first
      hy hc upperND u ms n postU cleanU
    have independent:=CoherentTail.readonly_record_independent
      (x++[topSource,topSource]) (y++[topTarget,topCopy]) (carry++[unused]) first
      ports.1 ports.2 (by simp [hy]) (by simp [hy,hc]) u n ms cleanU
    exact loan.trans (prefixEq.trans independent)
  have zero:=properProgram_measurementCount clear proper
  have middleCount:measurementCount (clear++renameProgram (Equiv.swap retired b) upper++
      clear.reverse)=measurementCount oldUpper := by
    have newM:measurementCount upper=x.length+1 :=
      (C4Lifetime.dependentAddPrefix_counts x y carry topSource topTarget topCopy first hy hc).2
    have oldM:measurementCount oldUpper=x.length+1 := by
      have h:=(addInPlace_counts (x++[topSource,topSource]) (y++[topTarget,topCopy])
        (carry++[unused]) first (by simp [hy]) (by simp [hy,hc])).2
      simpa [hy] using h
    simp only [measurementCount_append,measurementCount_reverse,
      (renameProgram_counts _ _).2,zero,Nat.zero_add,Nat.add_zero,newM,oldM]
  have eq:=TopCarry.run_mid_congr (majority a b cin first)
    (clear++renameProgram (Equiv.swap retired b) upper++clear.reverse) oldUpper finish
    m s rfl middleCount equal
  have independent:=CoherentTail.readonly_record_independent
    ((a::x)++[topSource,topSource]) ((b::y)++[topTarget,topCopy])
    ((first::carry)++[unused]) cin fullPorts.1 fullPorts.2
    (by simp [hy]) (by simp [hy,hc]) s m n (by simpa only [List.cons_append] using clean)
  apply Eq.trans ?_ independent
  rw [oldShape]
  simpa only [clear,upper,finish,List.append_assoc] using eq

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeInverseBoundary =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeProgram
-- consolidated import: import ECDSAAdd.Framework.RecordPadding

/-! The old inverse contract supplies the repeated output top bit.
The optimized copied outputs are not used to establish this relation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit Arithmetic.BalancedField

private theorem scalar_parity_ne (L : BalancedCircuit.Layout) (hn : L.wires.Nodup) :
    L.one≠L.parity ∧ L.rmsb≠L.parity := by
  have scalar:=BalancedCircuit.scalarND L hn
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at scalar
  constructor <;> tauto

theorem inverse_plain_sub_output_copy (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (B : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) (s : State) (m n : List Bool)
    (hs : s.basis L.sign=B) (hR : signedRegValue L.r s.basis=R)
    (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    let v:=run (GuardCompression.inversePrefix L) m s
    (run (GuardCompression.rawSub L) n v).basis L.one=
      (run (GuardCompression.rawSub L) n v).basis L.rmsb := by
  let P:=GuardCompression.inversePrefix L
  let headRecords:=(m++List.replicate (measurementCount P) false).take (measurementCount P)
  have prefixLength:headRecords.length=measurementCount P:=by
    simp only [headRecords,List.length_take,List.length_append,List.length_replicate]
    omega
  have prefixRun:run P headRecords s=run P m s:=by
    change run P ((m++List.replicate (measurementCount P) false).take (measurementCount P)) s=_
    rw [run_take,run_pad_false]
  have take:(headRecords++n).take (measurementCount P)=headRecords:=by
    rw [List.take_append,prefixLength,Nat.sub_self,List.take_zero,List.append_nil,
      ←prefixLength,List.take_length]
  have drop:(headRecords++n).drop (measurementCount P)=n:=by
    rw [List.drop_append,prefixLength,Nat.sub_self,List.drop_zero,
      ←prefixLength,List.drop_length,List.nil_append]
  have shape:GuardCompression.inverse L=P++
      (GuardCompression.rawSub L++(GuardCompression.seed L).reverse):=by
    simp only [P,GuardCompression.inverse,GuardCompression.inversePrefix,List.append_assoc]
  have actual:run (GuardCompression.inverse L) (headRecords++n) s=
      run (GuardCompression.rawSub L++(GuardCompression.seed L).reverse) n (run P m s):=by
    rw [shape,run_append,take,drop,prefixRun]
  have old:=GuardCompression.inverse_correct L hw hn B R Y hr hy s (headRecords++n) hs hR hY clean
  rw [actual] at old
  have apart:=scalar_parity_ne L hn
  have oneParity:L.one≠L.parity:=apart.1
  have highParity:L.rmsb≠L.parity:=apart.2
  have peel(t:State)(records:List Bool):
      (run (GuardCompression.seed L).reverse records t).basis L.one=
        (t.basis L.one ^^ t.basis L.rmsb):=by
    simp [GuardCompression.seed,run,writeBit,oneParity,highParity]
  have zero:=old.2.2.1 L.one (by simp [BalancedCircuit.work])
  rw [run_append,run_take,peel] at zero
  change (run (GuardCompression.rawSub L) n (run P m s)).basis L.one=
    (run (GuardCompression.rawSub L) n (run P m s)).basis L.rmsb
  cases ho:(run (GuardCompression.rawSub L) n (run P m s)).basis L.one <;>
    cases hh:(run (GuardCompression.rawSub L) n (run P m s)).basis L.rmsb <;> simp_all

theorem inverse_plain_add_output_copy (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (B : Bool) (R Y : Int)
    (hr : Centered R) (hy : Centered Y) (s : State) (m n : List Bool)
    (hs : s.basis L.sign=B) (hR : signedRegValue L.r s.basis=R)
    (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    let v:=run (GuardCompression.inversePrefix L) m s
    let u:=run (signComplement L.sign L.y) [] v
    let z:=run (notRegister (BalancedCircuit.rawTarget L)) [] u
    (run (addInPlace (GuardCompression.source L) (BalancedCircuit.rawTarget L) L.carry L.sign) n z).basis L.one=
      (run (addInPlace (GuardCompression.source L) (BalancedCircuit.rawTarget L) L.carry L.sign) n z).basis L.rmsb := by
  let v:=run (GuardCompression.inversePrefix L) m s
  let u:=run (signComplement L.sign L.y) [] v
  let z:=run (notRegister (BalancedCircuit.rawTarget L)) [] u
  let add:=addInPlace (GuardCompression.source L) (BalancedCircuit.rawTarget L) L.carry L.sign
  let tail:=notRegister (BalancedCircuit.rawTarget L)++signComplement L.sign L.y
  have copy:=inverse_plain_sub_output_copy L hw hn B R Y hr hy s m n hs hR hY clean
  have signZero:measurementCount (signComplement L.sign L.y)=0:=
    (signComplement_counts L.sign L.y).2
  have notZero:measurementCount (notRegister (BalancedCircuit.rawTarget L))=0:=
    (notRegister_counts (BalancedCircuit.rawTarget L)).2
  have actual:run (GuardCompression.rawSub L) n v=
      run tail (n.drop (measurementCount add)) (run add n z):=by
    simp only [GuardCompression.rawSub,subInPlace,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ n v signZero,
      TopCarry.run_zero_head _ _ n u notZero,run_append,run_take]
  have facts:=GuardCompression.rawFacts L hn
  have targetND: (BalancedCircuit.rawTarget L).Nodup:=BalancedCircuit.rawTargetND L hn
  have signAway:L.sign∉L.y:=fun used=>List.disjoint_left.mp facts.2.1 used (by simp)
  have targetAway(q:Wire)(hq:q∈BalancedCircuit.rawTarget L):q∉L.y:=
    fun used=>List.disjoint_left.mp facts.2.1 used (by simp [hq])
  have tailBit(q:Wire)(hq:q∈BalancedCircuit.rawTarget L)(t:State)(records:List Bool):
      (run tail records t).basis q= !t.basis q:=by
    rw [show tail=notRegister (BalancedCircuit.rawTarget L)++signComplement L.sign L.y from rfl,
      run_append,notRegister_correct _ targetND]
    have finish:=signComplement_correct L.sign L.y facts.1 signAway
      ⟨t.phase,fun w=>if w∈BalancedCircuit.rawTarget L then !t.basis w else t.basis w⟩
      (records.drop (measurementCount (notRegister (BalancedCircuit.rawTarget L))))
    rw [finish.2.1 q (targetAway q hq)]
    simp only [hq,if_true]
  change (run (GuardCompression.rawSub L) n v).basis L.one=
    (run (GuardCompression.rawSub L) n v).basis L.rmsb at copy
  rw [actual,tailBit L.one (by simp [BalancedCircuit.rawTarget]),
    tailBit L.rmsb (by simp [BalancedCircuit.rawTarget,BalancedCleanup.Layout.r])] at copy
  simpa using copy

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeAdderTransport =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeProgram

/-! A clean carry ladder does not change the complete arithmetic result.
The read-only source may repeat a wire at its two highest positions. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic

theorem readonly_add_carry_eq (x y left right : List Wire) (cin : Wire)
    (ndL : (cin::(y++left)).Nodup) (ndR : (cin::(y++right)).Nodup)
    (disL : List.Disjoint x (cin::(y++left)))
    (disR : List.Disjoint x (cin::(y++right)))
    (hx : x.length=y.length) (hL : left.length+1=y.length) (hR : right.length+1=y.length)
    (s : State) (m n : List Bool)
    (cleanL : ∀q∈left,s.basis q=false) (cleanR : ∀q∈right,s.basis q=false) :
    run (addInPlace x y left cin) m s=run (addInPlace x y right cin) n s := by
  have a:=GuardCompression.addInPlace_readonly_correct x y left cin ndL disL hx hL s m cleanL
  have b:=GuardCompression.addInPlace_readonly_correct x y right cin ndR disR hx hR s n cleanR
  apply State.extensionality
  · exact a.1.trans b.1.symm
  · funext q
    by_cases used:q∈y
    · exact (regValue_eq_iff y _ _).mp (a.2.2.trans b.2.2.symm) q used
    · exact (a.2.1 q used).trans (b.2.1 q used).symm

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeRawSubCall =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeRawSubHead
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeInverseBoundary
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeAdderTransport

/-! The concrete inverse tail retains the seeded parity through the
subtraction. Its measured top relation comes from the old plain result. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit Arithmetic.BalancedField

private theorem sub_nonempty_split (xs : List Wire) (h : xs≠[]) :
    xs=xs.getD 0 0::xs.drop 1 := by
  cases xs with
  | nil => exact False.elim (h rfl)
  | cons a xs => rfl

private theorem sub_zero_surround (A P Q R : Program) (s : State) (m n : List Bool)
    (a0 : measurementCount A=0) (r0 : measurementCount R=0)
    (eq : run P m (run A [] s)=run Q n (run A [] s)) :
    run (A++P++R) m s=run (A++Q++R) n s := by
  have execute(B:Program)(records:List Bool):run (A++B++R) records s=
      run R [] (run B records (run A [] s)):=by
    rw [run_append,run_take,run_append,a0,List.take_zero,List.drop_zero]
    exact FifthCarry.no_records R r0 _ _ []
  rw [execute P m,execute Q n,eq]

theorem raw_sub_tail_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (s : State) (m n : List Bool) (parityValue : s.basis L.parity=s.basis L.r0)
    (lower : s.basis L.lower=false) (clean : ∀q∈L.carry,s.basis q=false)
    (post :
      let u:=run (signComplement L.sign L.y) [] s
      let z:=run (notRegister (BalancedCircuit.rawTarget L)) [] u
      (run (addInPlace (GuardCompression.source L) (BalancedCircuit.rawTarget L) L.carry L.sign) n z).basis L.one=
        (run (addInPlace (GuardCompression.source L) (BalancedCircuit.rawTarget L) L.carry L.sign) n z).basis L.rmsb) :
    run (Q6LifetimeResearch.rawSubTail retired L) m s=
      run (GuardCompression.rawSub L++(GuardCompression.seed L).reverse) n s := by
  let carries:=(Q6Structural.q6Carry L).take 255
  let a:=L.ylow.getD 0 0
  let b:=L.r0
  let c:=carries.getD 0 0
  let x:=L.ylow.drop 1
  let y:=L.rtail
  let cs:=carries.drop 1
  let unused:=L.carry.getD 255 0
  let C:=carries++[unused]
  let S:=signComplement L.sign L.y
  let N:=notRegister (BalancedCircuit.rawTarget L)
  let A:=S++N
  let R:=N++S++(GuardCompression.seed L).reverse
  let z:=run N [] (run S [] s)
  let clear:Program:=[.X b,.CX L.parity b]
  let upper:=Q6LifetimeResearch.addTop (x++[L.ymsb,L.ymsb]) (y++[L.rmsb,L.one]) cs c
  let newAdd:=majority a b L.sign c++clear++renameProgram (Equiv.swap retired b) upper++
    clear.reverse++eraseCarry a b L.sign c++[.CX a b,.CX L.sign b]
  let oldAdd:=addInPlace (GuardCompression.source L) (BalancedCircuit.rawTarget L) L.carry L.sign
  have cshape:carries=L.carry.take 254++[L.lower]:=by
    simp [carries,Q6Structural.q6Carry,List.take_append,List.take_take,List.length_take,hw.2.2]
  have clen:carries.length=255:=by rw [cshape];simp [List.length_take,hw.2.2]
  have yne:L.ylow≠[]:=by intro e;have h:=hw.2.1;rw [e] at h;cases h
  have cne:carries≠[]:=by intro e;rw [e] at clen;cases clen
  have ysplit:L.ylow=a::x:=sub_nonempty_split L.ylow yne
  have csplit:carries=c::cs:=sub_nonempty_split carries cne
  have unusedIn:unused∈L.carry:=by
    have h:255<L.carry.length:=by rw [hw.2.2];omega
    dsimp only [unused]
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem _
  have rawND:(L.ylow++[L.ymsb]++L.low++[L.rmsb,L.one]++carries++
      [unused,L.sign,L.parity]).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    rw [CarryBorrow.carry_split L hw] at h
    have take:List.count q (L.carry.take 254)≤List.count q (L.carry.take 255):=by
      simpa only [List.take_take,show min 254 255=254 from rfl] using
        (List.take_sublist 254 (L.carry.take 255)).count_le q
    rw [cshape]
    dsimp only [unused]
    simp only [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      BalancedCleanup.Layout.y,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have headND:([a,b,L.sign,c,L.parity]++x++[L.ymsb]++y++[L.rmsb,L.one]++cs++[unused]).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp rawND q
    rw [ysplit,csplit] at h
    dsimp only [b,y]
    simp only [BalancedCleanup.Layout.low,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have targetND:(L.sign::(BalancedCircuit.rawTarget L++C)).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp rawND q
    simp only [C,BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have dataND:(L.y++(L.sign::(BalancedCircuit.rawTarget L++C))).Nodup:=by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp rawND q
    simp only [C,BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.y,
      List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  have sourceDis:List.Disjoint (GuardCompression.source L) (L.sign::(BalancedCircuit.rawTarget L++C)):=by
    apply List.disjoint_left.mpr
    intro q hq used
    exact List.disjoint_left.mp (List.nodup_append'.mp dataND).2.2
      (GuardCompression.source_sub L q hq) used
  have facts:=GuardCompression.rawFacts L hn
  have origDis:List.Disjoint (GuardCompression.source L) (L.sign::(BalancedCircuit.rawTarget L++L.carry)):=by
    apply List.disjoint_left.mpr
    intro q hq used
    exact List.disjoint_left.mp facts.2.1 (GuardCompression.source_sub L q hq) used
  have signAway:L.sign∉L.y:=fun used=>List.disjoint_left.mp facts.2.1 used (by simp)
  have targetDataND:(BalancedCircuit.rawTarget L).Nodup:=BalancedCircuit.rawTargetND L hn
  have basis(q:Wire):z.basis q=
      if q∈BalancedCircuit.rawTarget L then
        !(if q∈L.y then s.basis q ^^ s.basis L.sign else s.basis q)
      else if q∈L.y then s.basis q ^^ s.basis L.sign else s.basis q:=by
    rw [show z=run N [] (run S [] s) from rfl,notRegister_correct _ targetDataND]
    change (if q∈BalancedCircuit.rawTarget L then !(run S [] s).basis q else
      (run S [] s).basis q)=_
    rw [GuardCompression.complement_bit L.sign L.y facts.1 signAway s [] q]
  have dataAway(q:Wire)(hq:q∈L.lower::L.parity::L.carry):
      q∉L.y∧q∉BalancedCircuit.rawTarget L:=by
    exact ⟨(OwnQ6Core5.work_away L hn q (by
      simp only [List.mem_cons] at hq
      simp only [BalancedCircuit.work,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      tauto)).2,Q6RawBorrow.rawTarget_away L hn q hq⟩
  have keep(q:Wire)(hq:q∈L.lower::L.parity::L.carry):z.basis q=s.basis q:=by
    rw [basis,if_neg (dataAway q hq).2,if_neg (dataAway q hq).1]
  have low:z.basis b= !z.basis L.parity:=by
    have bIn:b∈BalancedCircuit.rawTarget L:=by
      simp [b,BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low]
    have bNotY:b∉L.y:=by
      intro used
      have away:∀q∈L.r,q∉L.y++L.carry:=List.disjoint_left.mp (List.nodup_append'.mp
        (L.toLayout.dataND (List.nodup_append'.mp hn).2.1)).2.2
      exact away b (by simp [b,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
        (List.mem_append_left _ used)
    rw [basis b,if_pos bIn,if_neg bNotY,keep L.parity (by simp),parityValue]
  have cleanOrig:∀q∈L.carry,z.basis q=false:=by
    intro q hq
    exact (keep q (by simp [hq])).trans (clean q hq)
  have cleanC:∀q∈C,z.basis q=false:=by
    intro q hq
    have choice:q∈L.carry∨q=L.lower:=by
      change q∈carries++[unused] at hq
      rw [cshape] at hq
      simp only [List.mem_append,List.mem_singleton] at hq
      rcases hq with (front|lo)|last
      · exact Or.inl (List.mem_of_mem_take front)
      · exact Or.inr lo
      · exact Or.inl (last ▸ unusedIn)
    rcases choice with used|eq
    · exact cleanOrig q used
    · subst q
      exact (keep L.lower (by simp)).trans lower
  have w:=BalancedCircuit.widths L hw
  have sourceLength:(GuardCompression.source L).length=(BalancedCircuit.rawTarget L).length:=by
    rw [GuardCompression.source_len,w.1,w.2.1]
  have cLength:C.length+1=(BalancedCircuit.rawTarget L).length:=by simp [C,clen,w.2.1]
  have originalLength:L.carry.length+1=(BalancedCircuit.rawTarget L).length:=by rw [hw.2.2,w.2.1]
  have transfer:run (addInPlace (GuardCompression.source L) (BalancedCircuit.rawTarget L) C L.sign) n z=
      run oldAdd n z:=readonly_add_carry_eq _ _ C L.carry L.sign targetND facts.2.2
    sourceDis origDis sourceLength cLength originalLength z n n cleanC cleanOrig
  have sourceShape:GuardCompression.source L=(a::x)++[L.ymsb,L.ymsb]:=by
    rw [GuardCompression.source,BalancedCleanup.Layout.y,ysplit,List.append_assoc]
    rfl
  have targetShape:BalancedCircuit.rawTarget L=(b::y)++[L.rmsb,L.one]:=by
    simp only [BalancedCircuit.rawTarget,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      b,y,List.append_assoc]
    rfl
  have carryShape:(c::cs)++[unused]=C:=by rw [←csplit]
  have headPost:
      (run (addInPlace ((a::x)++[L.ymsb,L.ymsb]) ((b::y)++[L.rmsb,L.one])
        ((c::cs)++[unused]) L.sign) n z).basis L.one=
      (run (addInPlace ((a::x)++[L.ymsb,L.ymsb]) ((b::y)++[L.rmsb,L.one])
        ((c::cs)++[unused]) L.sign) n z).basis L.rmsb:=by
    rw [←sourceShape,←targetShape,carryShape,transfer]
    exact post
  have memberTail:retired∈cs:=by
    change retired∈carries.drop 1
    rw [cshape,List.drop_append]
    have len:(L.carry.take 254).length=254:=by simp [List.length_take,hw.2.2]
    simp only [len,show 1-254=0 from rfl,List.drop_zero,List.mem_append,List.mem_singleton]
    exact Or.inl member
  have cleanHead:∀q∈c::(cs++[unused]),z.basis q=false:=by
    intro q hq
    apply cleanC q
    change q∈carries++[unused]
    rw [csplit]
    simpa only [List.cons_append] using hq
  have core:run newAdd m z=run oldAdd n z:=by
    have head:=raw_sub_head_loan_eq x y cs a b L.sign c L.parity L.ymsb L.rmsb L.one
      unused retired (by simp [x,y,hw.1,hw.2.1])
      (by simp [x,cs,clen,hw.2.1]) headND memberTail z m n low cleanHead headPost
    have equal:run newAdd m z=
        run (addInPlace (GuardCompression.source L) (BalancedCircuit.rawTarget L) C L.sign) n z:=by
      rw [sourceShape,targetShape,←carryShape]
      exact head
    exact equal.trans transfer
  have s0:measurementCount S=0:=(signComplement_counts L.sign L.y).2
  have n0:measurementCount N=0:=(notRegister_counts (BalancedCircuit.rawTarget L)).2
  have a0:measurementCount A=0:=by simp only [A,measurementCount_append,s0,n0]
  have r0:measurementCount R=0:=by
    simp only [R,measurementCount_append,measurementCount_reverse,s0,n0]
    rfl
  have input:run A [] s=z:=by
    rw [show A=S++N from rfl,run_append]
    simpa only [List.take_nil,List.drop_nil] using (show run N [] (run S [] s)=z from rfl)
  have eq:=sub_zero_surround A newAdd oldAdd R s m n a0 r0 (by rw [input];exact core)
  have sourceHead:(GuardCompression.source L).getD 0 0=a:=by
    rw [sourceShape]
    rfl
  have targetHead:(BalancedCircuit.rawTarget L).getD 0 0=b:=by
    rw [targetShape]
    rfl
  have sourceTail:(GuardCompression.source L).drop 1=x++[L.ymsb,L.ymsb]:=by
    rw [sourceShape]
    rfl
  have targetTail:(BalancedCircuit.rawTarget L).drop 1=y++[L.rmsb,L.one]:=by
    rw [targetShape]
    rfl
  have newShape:Q6LifetimeResearch.rawSubTail retired L=A++newAdd++R:=by
    simp only [Q6LifetimeResearch.rawSubTail,Q6LifetimeResearch.move,A,newAdd,R,S,N,
      sourceHead,targetHead,sourceTail,targetTail,GuardCompression.seed,clear,upper,
      b,a,c,carries,cs,List.reverse_cons,List.reverse_nil,List.append_assoc,
      List.cons_append,List.nil_append]
  have oldShape:GuardCompression.rawSub L++(GuardCompression.seed L).reverse=A++oldAdd++R:=by
    simp only [GuardCompression.rawSub,subInPlace,A,R,S,N,oldAdd,List.append_assoc]
  rw [newShape,oldShape]
  exact eq

theorem inverse_raw_tail_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup) (member : retired∈(L.carry.take 254).drop 1)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (prefixRecords m n : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    let v:=run (GuardCompression.inversePrefix L) prefixRecords s
    run (Q6LifetimeResearch.rawSubTail retired L) m v=
      run (GuardCompression.rawSub L++(GuardCompression.seed L).reverse) n v := by
  let v:=run (GuardCompression.inversePrefix L) prefixRecords s
  have ready:=GuardCompression.inverse_prefix_parity_unseeded L hw hn B R Y hr hy
    s prefixRecords hs hR hY clean
  have lower:=Q6RawBorrow.inverse_prefix_lower_clean L hw hn B R Y hr hy
    s prefixRecords hs hR hY clean
  have fifthEq:run (FifthCarry.inversePrefix L) prefixRecords s=
      run (GuardCompression.inversePrefix L) prefixRecords s:=
    (FifthCarry.inverse_prefix_eq L hw hn s prefixRecords clean).trans
      (FifthCarry.old_prefix_eq L hw hn B R Y hr hy s prefixRecords hs hR hY clean)
  rw [fifthEq] at lower
  exact raw_sub_tail_eq retired L hw hn member v m n ready.2 lower
    ((regValue_zero _ _).mp ready.1)
    (inverse_plain_add_output_copy L hw hn B R Y hr hy s prefixRecords n hs hR hY clean)

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeInverse =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeCompareReady
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeCompareWindow
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeFold
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeRawSubCall

/-! The literal inverse uses the old recovery state and old raw-tail
postcondition. Record padding joins the independent local record lists. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit Arithmetic.BalancedField
attribute [local irreducible] run

private def recoverProgram (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  recoverBefore retired L++
    (Q6StructuralCell.exposure L++Q6LifetimeResearch.compare retired false L++
      (Q6StructuralCell.exposure L).reverse)++
    (BalancedCleanup.prepareCompare L.toLayout).reverse

private def prefixProgram (retired : Wire) (L : BalancedCircuit.Layout) : Program :=
  recoverProgram retired L++BiasedInverse.unbiasView L++
    Q6LifetimeResearch.unfoldStep retired L++rotateLeft (BalancedCircuit.rawTarget L)++
    [.CX L.parity L.r0]

private theorem inverse_append_run (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

private theorem zero_tail_run (P Q : Program) (s : State) (m : List Bool)
    (zero : measurementCount Q=0) :
    run (P++Q) m s=run Q [] (run P m s) := by
  rw [inverse_append_run]
  exact FifthCarry.no_records Q zero _ _ []

private theorem join_records (P Q : Program) (s : State) (m n : List Bool) :
    ∃records,run (P++Q) records s=run Q n (run P m s) := by
  let headRecords:=(m++List.replicate (measurementCount P) false).take (measurementCount P)
  have headLength:headRecords.length=measurementCount P := by
    simp only [headRecords,List.length_take,List.length_append,List.length_replicate]
    omega
  have headRun:run P headRecords s=run P m s := by
    change run P ((m++List.replicate (measurementCount P) false).take (measurementCount P)) s=_
    rw [run_take,run_pad_false]
  have take:(headRecords++n).take (measurementCount P)=headRecords := by
    rw [List.take_append,headLength,Nat.sub_self,List.take_zero,List.append_nil,
      ←headLength,List.take_length]
  have drop:(headRecords++n).drop (measurementCount P)=n := by
    rw [List.drop_append,headLength,Nat.sub_self,List.drop_zero,
      ←headLength,List.drop_length,List.nil_append]
  refine ⟨headRecords++n,?_⟩
  rw [run_append,take,drop,headRun]

private theorem unbias_zero (L : BalancedCircuit.Layout) :
    measurementCount (BiasedInverse.unbiasView L)=0 := by
  have signZero:measurementCount (BalancedCleanup.prepareSign L.toLayout)=0 := by
    simp only [BalancedCleanup.prepareSign,measurementCount_append,
      (signComplement_counts L.lower L.r).2]
    rfl
  simp only [BiasedInverse.unbiasView,measurementCount_append,measurementCount_reverse,signZero]
  rfl

private theorem recover_eq_old (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1)
    (R : Int) (hr : Centered R) (s : State) (m : List Bool)
    (hR : regValue L.r s.basis=encodeWord 256 R)
    (hl : s.basis L.lower=false) (ho : s.basis L.one=false)
    (hc : ∀q∈L.carry,s.basis q=false) (hp : s.basis L.parity=false) :
    run (recoverProgram retired L) m s=run (BiasedInverse.recoverPrefix L) [] s := by
  have memberCarry:retired∈L.carry := List.mem_of_mem_take (List.mem_of_mem_drop member)
  have beforeEq:=recover_before_eq retired L hw hn memberCarry R hr s m hR hl ho hc
  have ready:=inverse_compare_ready retired L hw hn memberCarry R hr s m hR hl ho hc hp
  obtain ⟨v,vEq⟩ : ∃v : State,run (CarryBorrow.recoverBefore L) [] s=v := ⟨_,rfl⟩
  dsimp only at ready
  rw [beforeEq,vEq] at ready
  let W:=Q6StructuralCell.exposure L++Q6LifetimeResearch.compare retired false L++
    (Q6StructuralCell.exposure L).reverse
  let tail:=(BalancedCleanup.prepareCompare L.toLayout).reverse
  have tailZero:measurementCount tail=0 := by
    rw [show tail=(BalancedCleanup.prepareCompare L.toLayout).reverse from rfl,
      measurementCount_reverse,Q6CleanupBorrow.prepare_M]
  have windowEq:=compare_window_eq retired false L hw hn member v
    (m.drop (measurementCount (recoverBefore retired L))) []
    ready.1 ready.2.1 ready.2.2.1 (by simp)
  have newRun:run (recoverProgram retired L) m s=
      run tail [] (run (CarryBorrow.program L) [] v) := by
    have shape:recoverProgram retired L=recoverBefore retired L++(W++tail) := by
      simp only [recoverProgram,W,tail,List.append_assoc]
    rw [shape,inverse_append_run,beforeEq,vEq,zero_tail_run W tail _ _ tailZero]
    exact congrArg (run tail []) windowEq
  have oldRun:run (CarryBorrow.recoverPrefix L) [] s=
      run tail [] (run (CarryBorrow.program L) [] v) := by
    simp only [CarryBorrow.recoverPrefix,inverse_append_run,List.drop_nil,vEq,tail]
  exact newRun.trans (oldRun.symm.trans (CarryBorrow.recoverPrefix_eq L hw hn s [] ho hc))

private theorem old_view_ready (L : BalancedCircuit.Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    let v:=run (BiasedInverse.recoverPrefix L++BiasedInverse.unbiasView L) [] s
    v.basis L.lower=false ∧ ∀q∈L.carry,v.basis q=false := by
  have cnd:L.toLayout.wires.Nodup := (List.nodup_append'.mp hn).2.1
  have widths:=BalancedCleanup.widths L.toLayout hw
  obtain ⟨u,uEq⟩ : ∃u : State,run (BiasedInverse.recoverPrefix L) [] s=u := ⟨_,rfl⟩
  obtain ⟨v,vEq⟩ : ∃v : State,run (BiasedInverse.unbiasView L) [] u=v := ⟨_,rfl⟩
  have pre:=BiasedInverse.recoverPrefix_correct L hw cnd R Y B hr hy s []
    (word_encoding L.r 256 widths.2.1 s.basis R hR)
    (word_encoding L.y 256 widths.2.2.1 s.basis Y hY) hs
    (clean _ (by simp [BalancedCircuit.work]))
    (clean _ (by simp [BalancedCircuit.work]))
    (fun q hq=>clean q (by simp [BalancedCircuit.work,hq]))
  rw [uEq] at pre
  have view:=BiasedInverse.unbiasView_correct L hw cnd R hr u [] pre.2.1 pre.2.2.1
  rw [vEq] at view
  have carryND:(L.r++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h:=List.nodup_iff_count.mp (BalancedCircuit.allND L hn) q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have away(q:Wire)(hq:q∈L.carry):q∉L.r ∧ q≠L.lower ∧ q≠L.parity := by
    refine ⟨?_,?_,?_⟩
    · exact fun used=>List.disjoint_left.mp (List.nodup_append'.mp carryND).2.2 used hq
    · exact fun eq=>BalancedCircuit.flagAway L hn L.lower (by simp) (by simp [←eq,hq])
    · exact fun eq=>BalancedCircuit.flagAway L hn L.parity (by simp) (by simp [←eq,hq])
  have actual:run (BiasedInverse.recoverPrefix L++BiasedInverse.unbiasView L) [] s=v := by
    rw [inverse_append_run]
    simp only [List.drop_nil,uEq,vEq]
  rw [actual]
  refine ⟨view.2.2.1,?_⟩
  intro q hq
  have out:=(away q hq)
  exact (view.2.2.2 q out.1 out.2.1).trans
    ((pre.2.2.2.2 q out.1 out.2.1 out.2.2).trans
      (clean q (by simp [BalancedCircuit.work,hq])))

private theorem prefix_eq_guard (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    ∃records,run (prefixProgram retired L) m s=
      run (GuardCompression.inversePrefix L) records s := by
  let oldView:=BiasedInverse.recoverPrefix L++BiasedInverse.unbiasView L
  let newView:=recoverProgram retired L++BiasedInverse.unbiasView L
  let Z:Program:=rotateLeft (BalancedCircuit.rawTarget L)++[.CX L.parity L.r0]
  have widths:=BalancedCleanup.widths L.toLayout hw
  have recoverEq:=recover_eq_old retired L hw hn member R hr s m
    (word_encoding L.r 256 widths.2.1 s.basis R hR)
    (clean _ (by simp [BalancedCircuit.work]))
    (clean _ (by simp [BalancedCircuit.work]))
    (fun q hq=>clean q (by simp [BalancedCircuit.work,hq]))
    (clean _ (by simp [BalancedCircuit.work]))
  have viewEq:run newView m s=run oldView [] s := by
    rw [show newView=recoverProgram retired L++BiasedInverse.unbiasView L from rfl,
      zero_tail_run _ _ _ _ (unbias_zero L),recoverEq]
    rw [show oldView=BiasedInverse.recoverPrefix L++BiasedInverse.unbiasView L from rfl,
      zero_tail_run _ _ _ _ (unbias_zero L)]
  obtain ⟨v,vEq⟩ : ∃v : State,run oldView [] s=v := ⟨_,rfl⟩
  have ready:=old_view_ready L hw hn B R Y hr hy s hs hR hY clean
  change (run oldView [] s).basis L.lower=false ∧
    (∀q∈L.carry,(run oldView [] s).basis q=false) at ready
  rw [vEq] at ready
  have zZero:measurementCount Z=0 := by
    simp only [Z,measurementCount_append,(rotate_counts (BalancedCircuit.rawTarget L)).2.2.2]
    rfl
  have tailEq(records:List Bool):
      run (Q6LifetimeResearch.unfoldStep retired L++Z) records v=
        run (OneReuse.restoreRaw L) records v := by
    have oldShape:OneReuse.restoreRaw L=OneReuse.unfoldWindow L++Z := by
      simp only [OneReuse.restoreRaw,Z,List.append_assoc]
    rw [oldShape,zero_tail_run _ Z _ _ zZero,zero_tail_run _ Z _ _ zZero,
      unfold_eq_old retired L hw hn (List.mem_of_mem_drop member) v records ready.1 ready.2]
  let tailRecords:=m.drop (measurementCount newView)
  have newRun:run (prefixProgram retired L) m s=run (OneReuse.restoreRaw L) tailRecords v := by
    have shape:prefixProgram retired L=newView++(Q6LifetimeResearch.unfoldStep retired L++Z) := by
      simp only [prefixProgram,newView,Z,List.append_assoc]
    rw [shape,inverse_append_run,viewEq,vEq]
    exact tailEq tailRecords
  obtain ⟨records,joined⟩:=join_records oldView (OneReuse.restoreRaw L) s [] tailRecords
  rw [vEq] at joined
  have oldShape:oldView++OneReuse.restoreRaw L=FifthCarry.oldInversePrefix L := by
    simp only [oldView,FifthCarry.oldInversePrefix,List.append_assoc]
  rw [oldShape] at joined
  refine ⟨records,newRun.trans (joined.symm.trans ?_)⟩
  exact FifthCarry.old_prefix_eq L hw hn B R Y hr hy s records hs hR hY clean

private theorem old_inverse_records (L : BalancedCircuit.Layout) (hw : L.Widths)
    (hn : L.wires.Nodup) (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=R) (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (GuardCompression.inverse L) m s=run (GuardCompression.inverse L) n s := by
  obtain ⟨u,uEq⟩ : ∃u : State,run (GuardCompression.inverse L) m s=u := ⟨_,rfl⟩
  obtain ⟨v,vEq⟩ : ∃v : State,run (GuardCompression.inverse L) n s=v := ⟨_,rfl⟩
  have first:=GuardCompression.inverse_correct L hw hn B R Y hr hy s m hs hR hY clean
  have second:=GuardCompression.inverse_correct L hw hn B R Y hr hy s n hs hR hY clean
  rw [uEq] at first
  rw [vEq] at second
  have same:u=v := by
    apply State.extensionality
    · exact first.1.trans second.1.symm
    · funext q
      by_cases used:q∈L.r
      · exact (regValue_eq_iff L.r u.basis v.basis).mp
          (first.2.1.trans second.2.1.symm) q used
      · exact (first.2.2.2 q used).trans (second.2.2.2 q used).symm
  exact uEq.trans (same.trans vEq.symm)

theorem inverse_eq (retired : Wire) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired ∈ (L.carry.take 254).drop 1)
    (B : Bool) (R Y : Int) (hr : Centered R) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign = B)
    (hR : signedRegValue L.r s.basis = R)
    (hY : signedRegValue L.y s.basis = Y)
    (clean : ∀ q ∈ BalancedCircuit.work L, s.basis q = false) :
    run (Q6LifetimeResearch.inverse retired L) m s =
      run (GuardCompression.inverse L) n s := by
  obtain ⟨prefixRecords,prefixEq⟩:=prefix_eq_guard retired L hw hn member B R Y hr hy
    s m hs hR hY clean
  let rawRecords:=m.drop (measurementCount (prefixProgram retired L))
  let oldTail:=GuardCompression.rawSub L++(GuardCompression.seed L).reverse
  have newShape:Q6LifetimeResearch.inverse retired L=
      prefixProgram retired L++Q6LifetimeResearch.rawSubTail retired L := by
    simp only [Q6LifetimeResearch.inverse,prefixProgram,recoverProgram,recoverBefore,
      List.append_assoc]
  have newRun:run (Q6LifetimeResearch.inverse retired L) m s=
      run oldTail [] (run (GuardCompression.inversePrefix L) prefixRecords s) := by
    rw [newShape,inverse_append_run,prefixEq]
    exact inverse_raw_tail_eq retired L hw hn member B R Y hr hy s prefixRecords
      rawRecords [] hs hR hY clean
  obtain ⟨records,oldRun⟩:=join_records (GuardCompression.inversePrefix L) oldTail s prefixRecords []
  have oldShape:GuardCompression.inversePrefix L++oldTail=GuardCompression.inverse L := by
    simp only [GuardCompression.inversePrefix,GuardCompression.inverse,oldTail,List.append_assoc]
  rw [oldShape] at oldRun
  exact newRun.trans (oldRun.symm.trans
    (old_inverse_records L hw hn B R Y hr hy s records n hs hR hY clean))

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeHalf =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeForward
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeInverse

/-! Ordinary half frames retain the complete State and arbitrary records. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.Q6LifetimeProof
open Arithmetic BalancedCircuit Secp256k1 BalancedField
attribute [local irreducible] run

private theorem register_frame_eq (r : List Wire) (s t u : State)
    (tp : t.phase=s.phase) (up : u.phase=s.phase)
    (value : regValue r t.basis=regValue r u.basis)
    (tf : ∀q,q∉r→t.basis q=s.basis q) (uf : ∀q,q∉r→u.basis q=s.basis q) : t=u := by
  apply State.extensionality
  · exact tp.trans up.symm
  · funext q
    by_cases used:q∈r
    · exact (regValue_eq_iff r _ _).mp value q used
    · exact (tf q used).trans (uf q used).symm

theorem kernel_eq (retired : Wire) (divide : Bool) (L : BalancedCircuit.Layout)
    (hw : L.Widths) (hn : L.wires.Nodup)
    (member : retired∈(L.carry.take 254).drop 1)
    (B : Bool) (X Y : Int) (hx : Centered X) (hy : Centered Y)
    (s : State) (m n : List Bool) (hs : s.basis L.sign=B)
    (hR : signedRegValue L.r s.basis=X) (hY : signedRegValue L.y s.basis=Y)
    (clean : ∀q∈BalancedCircuit.work L,s.basis q=false) :
    run (if divide then Q6LifetimeResearch.forward retired false L
      else Q6LifetimeResearch.inverse retired L) m s=
      run (OwnQ6Core5.oldKernel divide L) n s := by
  cases divide
  · simp only [OwnQ6Core5.oldKernel,Bool.false_eq_true,if_false]
    rw [inverse_eq retired L hw hn member B X Y hx hy s m n hs hR hY clean]
    have a:=GuardCompression.inverse_correct L hw hn B X Y hx hy s n hs hR hY clean
    have b:=BalancedInverse.program_correct L hw hn B X Y hx hy s n hs hR hY clean
    exact register_frame_eq L.r s _ _ a.1 b.1 (a.2.1.trans b.2.1.symm) a.2.2.2 b.2.2.2
  · simp only [OwnQ6Core5.oldKernel,if_true]
    rw [forward_eq retired L hw hn member B X Y hx hy s m n hs hR hY clean]
    have a:=FifthCarry.forward_correct L hw hn B X Y hx hy s n hs hR hY clean
    have b:=BalancedCircuit.program_correct L hw hn B X Y hx hy s n hs hR hY clean
    exact register_frame_eq L.r s _ _ a.1 b.1 (a.2.1.trans b.2.1.symm) a.2.2.2 b.2.2.2

theorem half_old_eq (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp)
    (s : State) (m n : List Bool)
    (input : PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (centerWord X) (centerWord Y) s.basis) :
    run (Q6LifetimeResearch.half retired divide w sign) m s=
      run (OwnQ6Core5.oldHalf divide (Q6EndpointCell.ports w sign)) n s := by
  let L:=Q6EndpointCell.ports w sign
  let u:=run [.X L.sign] [] s
  have hw:=Q6EndpointCell.ports_widths w sign
  have cl:=Q6EndpointCell.clean_work w sign origin clean
  have away:=BalancedCircuit.flagAway L hn L.sign (by simp)
  have sa:L.sign∉L.r ∧ L.sign∉L.y:=
    ⟨fun h=>away (by simp [h]),fun h=>away (by simp [h])⟩
  have us:=BalancedCleanupOffset.x_run L.sign s []
  have uf(q:Wire)(hq:q≠L.sign):u.basis q=s.basis q:=by
    change (run [.X L.sign] [] s).basis q=s.basis q
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ug:u.basis L.sign= !origin L.sign:=by
    change (run [.X L.sign] [] s).basis L.sign= !origin L.sign
    rw [us]
    simp only [writeBit,Function.update_self,input.2.2 L.sign sa.1 sa.2]
  have uv(r:List Wire)(free:L.sign∉r):regValue r u.basis=regValue r s.basis:=
    regValue_congr _ _ _ (fun q hq=>uf q (fun eq=>free (eq ▸ hq)))
  have ur:signedRegValue L.r u.basis=centerFp X:=by
    rw [signedRegValue,uv L.r sa.1,input.1,(BalancedCleanup.widths L.toLayout hw).2.1,
      centerWord_decode]
  have uy:signedRegValue L.y u.basis=centerFp Y:=by
    rw [signedRegValue,uv L.y sa.2,input.2.1,(BalancedCleanup.widths L.toLayout hw).2.2.1,
      centerWord_decode]
  have uc:∀q∈BalancedCircuit.work L,u.basis q=false:=by
    intro q hq
    have a:=OwnQ6Core5.work_away L hn q hq
    exact (uf q (fun eq=>OwnQ6Core5.sign_work L hn (eq ▸ hq))).trans
      ((input.2.2 q a.1 a.2).trans (cl q hq))
  have body:=kernel_eq retired divide L hw hn member (!origin L.sign)
    (centerFp X) (centerFp Y) (centerFp_bounds X) (centerFp_bounds Y) u m n ug ur uy uc
  have execute(P:Program)(records:List Bool):
      run ([.X L.sign]++P++[.X L.sign]) records s=run [.X L.sign] [] (run P records u):=by
    rw [List.append_assoc,run_append]
    simp only [measurementCount,List.take_zero,List.drop_zero]
    rw [run_append,run_take]
    exact FifthCarry.no_records [.X L.sign] (by rfl) _ _ []
  change run ([.X L.sign]++(if divide then Q6LifetimeResearch.forward retired false L
    else Q6LifetimeResearch.inverse retired L)++[.X L.sign]) m s=
    run ([.X L.sign]++OwnQ6Core5.oldKernel divide L++[.X L.sign]) n s
  rw [execute,execute,body]

theorem half_frame (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (centerWord X) (centerWord Y)) (Q6LifetimeResearch.half retired divide w sign)
      (PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y origin
        (centerWord (if divide then (X+(if origin sign then Y else -Y))/2
          else 2*X+(if origin sign then -Y else Y))) (centerWord Y)) := by
  intro s m input
  rw [half_old_eq retired divide w sign hn member origin clean X Y s m m input]
  have hw:=Q6EndpointCell.ports_widths w sign
  have cl:=Q6EndpointCell.clean_work w sign origin clean
  cases divide
  · exact balancedTranscriptDouble_frame _ hw hn origin cl X Y s m input
  · exact balancedTranscriptHalf_frame _ hw hn origin cl X Y s m input

theorem half_run_eq (retired : Wire) (divide : Bool) (w : Nat→Wire) (sign : Wire)
    (hn : (Q6EndpointCell.ports w sign).wires.Nodup)
    (member : retired∈((Q6EndpointCell.ports w sign).carry.take 254).drop 1)
    (origin : BasisState) (clean : Q6EndpointCell.Clean w origin) (X Y : Fp)
    (s : State) (m n : List Bool)
    (input : PairFrame (Q6EndpointCell.ports w sign).r (Q6EndpointCell.ports w sign).y
      origin (centerWord X) (centerWord Y) s.basis) :
    run (Q6LifetimeResearch.half retired divide w sign) m s=
      run (Q6EndpointCell.half divide w sign) n s := by
  exact PairFrame.program_eq _ _ origin (centerWord X) (centerWord Y) _ _ _ _
    (half_frame retired divide w sign hn member origin clean X Y)
    (Q6EndpointCell.half_frame divide w sign hn origin clean X Y) s m n input

end ECDSAAdd.Entrant.Q6LifetimeProof
end -- original module boundary

section
namespace ECDSAAdd.Entrant.Rolling1588Lifetime
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField
theorem half_ports_nodup760 : (Q6EndpointCell.ports base (base 2409)).wires.Nodup :=
  Q6EndpointCell.ports_nodup_injective base (base 2409) base_injective (by
    intro member
    obtain ⟨i,hi,eq⟩ := List.mem_map.mp member
    have same := base_injective eq
    have bound := Q6EndpointCell.ids_bound i hi
    omega)
end ECDSAAdd.Entrant.Rolling1588Lifetime
end

-- ===== ECDSAAdd.Submission.Entrant.Q6LifetimeSupport =====
section
-- consolidated import: import ECDSAAdd.Submission.Entrant.Q6LifetimeProgram

/-! Structural support and physical gates for the two retired carry choices.
Support includes both correction lists of every measurement. -/
set_option autoImplicit false
namespace ECDSAAdd.Entrant.Q6LifetimeResearch
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum

private theorem majority_support (a b c d : Wire) :
    wires (majority a b c d)={a,b,c,d} := by
  ext q
  simp [majority,wires,Instr.wires]
  tauto

private theorem move_support_erase (r h : Wire) (P : Program) (S : Finset Wire)
    (_rh : r≠h) (hp : wires P⊆S) (hh : h∈S) (off : h∉wires P) :
    wires (move r h P)⊆S.erase r := by
  rw [move,renameProgram_support]
  rintro q used
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp used
  have ah : a≠h := fun e => off (e ▸ ha)
  apply Finset.mem_erase.mpr
  constructor
  · intro e
    have back : Equiv.swap r h h=r := Equiv.swap_apply_right _ _
    exact ah ((Equiv.swap r h).injective (e.trans back.symm))
  · by_cases ar : a=r
    · simpa only [ar,Equiv.swap_apply_left] using hh
    · simpa only [Equiv.swap_apply_of_ne_of_ne ar ah] using hp ha

private theorem move_physical (r h : Wire) (P : Program) (hp : GatePhysical P) :
    GatePhysical (move r h P) :=
  gatePhysical_rename _ (Equiv.swap r h).injective _ hp

private theorem top_chain_support_eq (xs ys cs : List Wire) (cin target : Wire)
    (ne : xs≠[]) (hy : ys.length=xs.length) (hc : cs.length=xs.length) :
    wires (TopCarry.compareChainTop xs ys cs cin target)=
      (target::cin::(xs++ys++cs)).toFinset := by
  induction xs generalizing ys cs cin with
  | nil => exact (ne rfl).elim
  | cons a xs ih =>
    cases ys with
    | nil => simp at hy
    | cons b ys =>
      cases cs with
      | nil => simp at hc
      | cons c cs =>
        by_cases last : xs=[]
        · subst xs
          have ye : ys=[] := List.eq_nil_of_length_eq_zero (by simpa using hy)
          have ce : cs=[] := List.eq_nil_of_length_eq_zero (by simpa using hc)
          subst ys; subst cs
          ext q
          simp [TopCarry.compareChainTop,eraseCarry,wires,Instr.wires,correctionWires]
          tauto
        · have child := ih ys cs c last (by simpa using hy) (by simpa using hc)
          rw [TopCarry.compareChainTop,if_neg last,wires_append,wires_append,
            child,majority_support,eraseCarry_wires]
          ext q
          simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
            List.mem_toFinset,List.mem_cons,List.mem_append]
          tauto

private theorem top_compare_support_eq (xs ys cs : List Wire) (cin target : Wire)
    (ne : cs≠[]) (hy : ys.length=xs.length) (hc : cs.length+1=xs.length)
    (two : 2≤xs.length) :
    wires (TopCarryBorrow.compare xs ys cs cin target)=
      (target::cin::(xs++ys++cs)).toFinset := by
  cases xs with
  | nil => simp at two
  | cons a xs =>
    cases ys with
    | nil => simp at hy
    | cons b ys =>
      cases cs with
      | nil => exact (ne rfl).elim
      | cons c cs =>
        have xn : xs≠[] := by intro e; simp [e] at two
        have hy' : ys.length=xs.length := Nat.succ.inj hy
        have hc' : cs.length+1=xs.length := Nat.succ.inj hc
        have child := top_chain_support_eq xs ys (cs++[cin]) c target xn hy'
          (by simpa only [List.length_append,List.length_singleton] using hc')
        simp only [TopCarryBorrow.compare,TopCarryBorrow.compareHeadTop,
          TopCarryBorrow.headChainTop,wires_append,child,majority_support,
          eraseCarry_wires,notRegister_wires]
        ext q
        simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
          List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false,
          wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
          Finset.notMem_empty,or_false]
        tauto

private theorem compareChain_support (forward : Bool) (xs ys cs : List Wire)
    (cin target : Wire) :
    wires (compareChain forward xs ys cs cin target)⊆
      (target::cin::(xs++ys++cs)).toFinset := by
  induction xs generalizing ys cs cin with
  | nil => cases ys <;> simp [compareChain,wires]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [compareChain,wires]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [compareChain,wires]
        | nil =>
          cases forward <;> intro q used <;>
            simp [compareChain,compareLeaf,wires_append,majority_support,
              eraseCarry_wires,wires,Instr.wires] at used ⊢ <;> tauto
    | cons a' xs =>
      cases ys with
      | nil => simp [compareChain,wires]
      | cons b ys =>
        cases ys with
        | nil => simp [compareChain,wires]
        | cons b' ys =>
          cases cs with
          | nil => simp [compareChain,wires]
          | cons c cs =>
            have child := ih (b'::ys) cs c
            intro q used
            simp only [compareChain,wires_append,Finset.mem_union,
              majority_support,eraseCarry_wires] at used
            simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
            rcases used with (head|tail)|finish
            · simp only [Finset.mem_insert,Finset.mem_singleton] at head
              tauto
            · have h := child tail
              simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
              tauto
            · simp only [Finset.mem_insert,Finset.mem_singleton] at finish
              tauto

private theorem addTop_step (a a' b b' c cin : Wire) (xs ys cs : List Wire)
    (notLast : ¬(xs=[] ∧ ys=[])) :
    addTop (a::a'::xs) (b::b'::ys) (c::cs) cin=
      majority a b cin c++addTop (a'::xs) (b'::ys) cs c++
        eraseCarry a b cin c++[.CX a b,.CX cin b] := by
  cases xs <;> cases ys <;> first | rfl | exact (notLast ⟨rfl,rfl⟩).elim

private theorem addTop_support (xs ys cs : List Wire) (cin : Wire) :
    wires (addTop xs ys cs cin)⊆(cin::(xs++ys++cs)).toFinset := by
  induction xs generalizing ys cs cin with
  | nil => simp [addTop,wires]
  | cons a xs ih =>
    cases xs with
    | nil => cases ys <;> simp [addTop,wires]
    | cons a' xs =>
      cases ys with
      | nil => simp [addTop,wires]
      | cons b ys =>
        cases ys with
        | nil => simp [addTop,wires]
        | cons b' ys =>
          by_cases last : xs=[] ∧ ys=[]
          · rcases last with ⟨rfl,rfl⟩
            intro q used
            simp [addTop,dependentTop,wires,Instr.wires,correctionWires] at used ⊢
            tauto
          · cases cs with
            | nil => cases xs <;> cases ys <;> simp_all [addTop,wires]
            | cons c cs =>
              have child := ih (b'::ys) cs c
              rw [addTop_step a a' b b' c cin xs ys cs last]
              intro q used
              simp only [wires_append,Finset.mem_union,majority_support,eraseCarry_wires] at used
              rcases used with ((head|tail)|finish)|sum
              all_goals
                simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
              · simp only [Finset.mem_insert,Finset.mem_singleton] at head; tauto
              · have h := child tail
                simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
                tauto
              · simp only [Finset.mem_insert,Finset.mem_singleton] at finish; tauto
              · simp [wires,Instr.wires] at sum; tauto

private theorem compareChain_physical (forward : Bool) (xs ys cs : List Wire)
    (cin target : Wire) (nd : (target::cin::(xs++ys++cs)).Nodup) :
    GatePhysical (compareChain forward xs ys cs cin target) := by
  induction xs generalizing ys cs cin with
  | nil => cases ys <;> simp [compareChain,GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => simp [compareChain,GatePhysical]
      | cons b ys =>
        cases ys with
        | cons b' ys => simp [compareChain,GatePhysical]
        | nil =>
          have localND : [a,b,cin,target].Nodup := by
            apply List.nodup_iff_count.mpr
            intro q
            have h := List.nodup_iff_count.mp nd q
            simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
            omega
          cases forward
          · simpa only [compareChain,compareLeaf,Bool.false_eq_true,if_false,
              gatePhysical_append] using And.intro (majority_physical _ _ _ _ localND)
                (show GatePhysical [.X target] by simp [GatePhysical,PhysicalInstr,ProperGate])
          · simpa only [compareChain,compareLeaf,if_true,gatePhysical_append] using
              And.intro (show GatePhysical [.X target] by simp [GatePhysical,PhysicalInstr,ProperGate])
                (eraseCarry_physical _ _ _ _)
    | cons a' xs =>
      cases ys with
      | nil => simp [compareChain,GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [compareChain,GatePhysical]
        | cons b' ys =>
          cases cs with
          | nil => simp [compareChain,GatePhysical]
          | cons c cs =>
            have localND : [a,b,cin,c].Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := List.nodup_iff_count.mp nd q
              simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
              omega
            have tailND : (target::c::((a'::xs)++(b'::ys)++cs)).Nodup := by
              apply List.nodup_iff_count.mpr
              intro q
              have h := List.nodup_iff_count.mp nd q
              simp only [List.count_cons,List.count_append] at h ⊢
              omega
            simpa only [compareChain,gatePhysical_append] using
              And.intro (And.intro (majority_physical _ _ _ _ localND)
                (ih (b'::ys) cs c tailND)) (eraseCarry_physical _ _ _ _)

attribute [local irreducible] wires GatePhysical CoherentTail.addPrefix mappedAdd mappedSub
  literalConstAdd EndKnown.addK compareChain addTop TopCarryBorrow.compare CarryBorrow.compare

private theorem old_half_shape (divide : Bool) (w : Nat→Wire) (sign : Wire) :
    Q6EndpointCell.half divide w sign=[.X sign]++
      (if divide then Q6StructuralCell.forward (Q6EndpointCell.ports w sign)
       else Q6StructuralCell.inverse (Q6EndpointCell.ports w sign))++[.X sign] := rfl

private abbrev L : BalancedCircuit.Layout := Q6EndpointCell.ports base (base 2409)
private abbrev carries : List Wire := (Q6Structural.q6Carry L).take 255
private abbrev footprint : Finset Wire :=
  (L.sign::L.parity::L.one::(L.y++L.r++carries)).toFinset

private theorem take_prefix (xs ys : List Wire) (a : Wire) (n : Nat)
    (hn : xs.length=n) : (xs++[a]++ys).take (n+1)=xs++[a] := by
  have len : (xs++[a]).length=n+1 := by
    simp only [List.length_append,List.length_singleton,hn]
  rw [List.take_append_of_le_length (by omega),List.take_of_length_le (by omega)]

private theorem carries_take : carries=L.carry.take 254++[L.lower] := by
  have len : (L.carry.take 254).length=254 :=
    (BalancedCleanup.widths L.toLayout (Q6EndpointCell.ports_widths base (base 2409))).2.2.2
  exact take_prefix (L.carry.take 254) (L.carry.drop 255) L.lower 254 len

private theorem carry_front_shape :
    L.carry.take 254=wireBlock base 512 253++[base 1540] := by
  have shape : L.carry=wireBlock base 512 253++[base 1540,base 1541,base 1026] := rfl
  have len : (wireBlock base 512 253).length=253 := by
    simp only [wireBlock,List.length_map,List.length_range']
  rw [shape,List.take_append,List.take_of_length_le (by omega),len]
  rfl

private theorem carries_shape : carries=wireBlock base 512 253++[base 1540,base 1797] := by
  rw [carries_take,carry_front_shape,List.append_assoc]
  rfl

private theorem y_shape : L.y=wireBlock base 770 256 :=
  (Q6EndpointCell.ports_y base (base 2409)).trans (balancedSharedPorts_y base (base 2409))
private theorem r_shape : L.r=wireBlock base 2056 256 :=
  (Q6EndpointCell.ports_r base (base 2409)).trans (balancedSharedPorts_r base (base 2409))

private theorem layout_sign : L.sign=base 2409 := rfl

-- Stop unification from evaluating the closed vector constructors. All cuts
-- and membership arguments below use their structural list lemmas.
attribute [local irreducible] List.range'

private theorem footprint_comparator (forward : Bool) :
    wires (if forward then Q6Structural.compareForward L else Q6Structural.compareInverse L)=
      (L.parity::L.one::(L.y++L.r++carries)).toFinset := by
  have widths := Q6EndpointCell.ports_widths base (base 2409)
  have count : carries.length=255 := by
    rw [carries_shape]
    simp only [List.length_append,wireBlock,List.length_map,List.length_range',
      List.length_cons,List.length_nil]
  have yn : L.y.length=256 := (BalancedCleanup.widths L.toLayout widths).2.2.1
  have rn : L.r.length=256 := (BalancedCleanup.widths L.toLayout widths).2.1
  cases forward
  · have fact := CarryBorrow.program_support_eq (Q6Structural.carryLayout L)
      (Q6StructuralCell.carry_widths L widths)
    exact fact
  · have nonempty : carries≠[] := by intro e; simp only [e,List.length_nil] at count; omega
    have fact := top_compare_support_eq L.y L.r carries L.one L.parity nonempty
      (rn.trans yn.symm) (by omega) (by omega)
    exact fact

private theorem footprint_old_half (divide : Bool) :
    footprint⊆wires (Q6EndpointCell.half divide base (base 2409)) := by
  have cmp := footprint_comparator divide
  intro q used
  simp only [footprint,List.mem_toFinset,List.mem_cons] at used
  rcases used with sign|rest
  · subst q
    rw [old_half_shape,wires_append,wires_append]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [wires,Instr.wires,layout_sign]))
  · have part : q∈wires (if divide then Q6Structural.compareForward L
        else Q6Structural.compareInverse L) :=
      cmp.symm ▸ (by simpa only [List.mem_toFinset,List.mem_cons] using rest)
    cases divide
    · change q∈wires (Q6Structural.compareInverse L) at part
      simp only [old_half_shape,Bool.false_eq_true,if_false,Q6StructuralCell.inverse,
        Q6StructuralCell.inversePrefix,Q6StructuralCell.recoverPrefix,wires_append,Finset.mem_union]
      tauto
    · change q∈wires (Q6Structural.compareForward L) at part
      simp only [old_half_shape,if_true,Q6StructuralCell.forward,
        Q6StructuralCell.forwardPrefix,Q6StructuralCell.cleanup,wires_append,Finset.mem_union]
      tauto

private theorem footprint_old_halfE (divide : Bool) :
    footprint⊆wires (Q6EndpointCell.halfE divide base (base 2409)) := by
  cases divide
  · exact footprint_old_half false
  · have cmp := footprint_comparator true
    intro q used
    simp only [footprint,List.mem_toFinset,List.mem_cons] at used
    rcases used with sign|rest
    · subst q
      rw [Q6EndpointCell.halfE_true,wires_append,wires_append]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [wires,Instr.wires,layout_sign]))
    · have part : q∈wires (Q6Structural.compareForward L) :=
        cmp.symm ▸ (by simpa only [List.mem_toFinset,List.mem_cons] using rest)
      simp only [Q6EndpointCell.halfE_true,Q6EndpointStructural.forwardE,
        Q6StructuralCell.forwardPrefix,Q6EndpointStructural.cleanupE,
        wires_append,Finset.mem_union]
      tauto

private abbrev dataSites : Finset Wire :=
  (L.sign::L.parity::L.one::L.lower::(L.y++L.r)).toFinset

private theorem data_footprint : dataSites⊆footprint := by
  have lower : L.lower∈carries := by rw [carries_shape]; simp [L,Q6EndpointCell.ports]
  intro q h
  simp only [dataSites,footprint,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
  rcases h with h|h|h|h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · subst q; tauto
  · tauto

private theorem data_retired_free (retired : Nat) (hr : retired=719∨retired=720∨retired=760) :
    base retired∉dataSites := by
  have nr : base retired∉L.r := by
    rw [r_shape]
    exact OwnPlusHost.not_block retired 2056 256 (by omega)
  have ny : base retired∉L.y := by
    rw [y_shape]
    exact OwnPlusHost.not_block retired 770 256 (by omega)
  intro used
  simp only [dataSites,List.mem_toFinset,List.mem_cons,List.mem_append] at used
  rcases used with e|e|e|e|h|h
  · rcases hr with rfl|rfl|rfl <;> simp [L,Q6EndpointCell.ports,base] at e
  · rcases hr with rfl|rfl|rfl <;> simp [L,Q6EndpointCell.ports,base] at e
  · rcases hr with rfl|rfl|rfl <;> simp [L,Q6EndpointCell.ports,base] at e
  · rcases hr with rfl|rfl|rfl <;> simp [L,Q6EndpointCell.ports,base] at e
  · exact ny h
  · exact nr h

private theorem data_erased (retired : Nat) (hr : retired=719∨retired=720∨retired=760) :
    dataSites⊆footprint.erase (base retired) := by
  intro q h
  exact Finset.mem_erase.mpr ⟨fun e => data_retired_free retired hr (e ▸ h),
    data_footprint h⟩

private theorem mapped_sources (q : Wire)
    (used : q∈mappedWires (ShortBiasedFold.lowBits L)) : q=L.lower∨q=L.one :=
  Or.inl (OneReuse.lowBits_source L q used)

private abbrev addTail : Program :=
  CoherentTail.addPrefix (L.ylow.drop 1) (L.low.drop 1) (carries.drop 1)
    L.ymsb L.rmsb L.one (carries.getD 0 0)
private abbrev topTail : Program :=
  addTop ((GuardCompression.source L).drop 1) ((BalancedCircuit.rawTarget L).drop 1)
    (carries.drop 1) (carries.getD 0 0)
private abbrev cmpTail (forward : Bool) : Program :=
  compareChain forward (L.y.drop 1) (L.r.drop 1) (carries.drop 1)
    (carries.getD 0 0) L.parity
private abbrev foldBody (forward : Bool) : Program :=
  if forward then mappedAdd (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
  else mappedSub (ShortBiasedFold.lowBits L) L.low (L.carry.take 254) L.one
private abbrev normBody (forward endpoint : Bool) : Program :=
  if forward then
    if endpoint then FifthCarry2.unnormalizeE L.toLayout else BalancedCleanup.unnormalize L.toLayout
  else BalancedCleanup.normalize L.toLayout

private theorem add_envelope :
    wires addTail⊆(L.ylow.drop 1++L.low.drop 1++carries.drop 1++
      [L.ymsb,L.rmsb,L.one,carries.getD 0 0]).toFinset := by
  intro q used
  exact List.mem_toFinset.mpr (CoherentTail.addPrefix_support _ _ _ _ _ _ _ q used)

private theorem top_envelope :
    wires topTail⊆(carries.getD 0 0::((GuardCompression.source L).drop 1++
      (BalancedCircuit.rawTarget L).drop 1++carries.drop 1)).toFinset :=
  addTop_support _ _ _ _

private theorem cmp_envelope (forward : Bool) :
    wires (cmpTail forward)⊆(L.parity::carries.getD 0 0::
      (L.y.drop 1++L.r.drop 1++carries.drop 1)).toFinset :=
  compareChain_support _ _ _ _ _ _

private theorem fold_envelope (forward : Bool) :
    wires (foldBody forward)⊆
      (L.lower::L.one::(L.low++L.carry.take 254++[L.one])).toFinset := by
  have bound : wires (foldBody forward)⊆
      (mappedWires (ShortBiasedFold.lowBits L)++L.low++L.carry.take 254++[L.one]).toFinset := by
    cases forward
    · exact mappedSub_wires_subset _ _ _ _
    · exact mappedAdd_wires_subset _ _ _ _
  intro q used
  have h := bound used
  simp only [List.mem_toFinset,List.mem_append] at h
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
  rcases h with ((h|h)|h)|h
  · have source := mapped_sources q h; tauto
  · tauto
  · tauto
  · have eq : q=L.one := List.mem_singleton.mp h
    exact Or.inr (Or.inl eq)

private theorem norm_envelope (forward endpoint : Bool) :
    wires (normBody forward endpoint)⊆
      (L.lower::L.one::L.ymsb::(L.low++L.carry.take 254++L.ylow)).toFinset := by
  have embed : (L.lower::L.one::(L.low++L.carry.take 254)).toFinset⊆
      (L.lower::L.one::L.ymsb::(L.low++L.carry.take 254++L.ylow)).toFinset := by
    intro q h
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have a : wires (literalConstAdd L.low (L.carry.take 254) L.lower L.one
      BalancedCleanup.negativeLiteral)⊆(L.lower::L.one::(L.low++L.carry.take 254)).toFinset := by
    simpa only [List.toFinset_cons,Finset.insert_comm] using
      literalConstAdd_wires L.low (L.carry.take 254) L.lower L.one BalancedCleanup.negativeLiteral
  have b : wires (literalConstAdd L.low (L.carry.take 254) L.lower L.one
      BalancedCleanup.positiveLiteral)⊆(L.lower::L.one::(L.low++L.carry.take 254)).toFinset := by
    simpa only [List.toFinset_cons,Finset.insert_comm] using
      literalConstAdd_wires L.low (L.carry.take 254) L.lower L.one BalancedCleanup.positiveLiteral
  have widths := BalancedCleanup.widths L.toLayout (Q6EndpointCell.ports_widths base (base 2409))
  have lowLen := widths.1
  have carryLen := widths.2.2.2
  have c := EndKnown.addK_wires L.low L.ylow (L.carry.take 254) L.ymsb L.lower L.one
    BalancedCleanup.positiveLiteral (by omega)
  cases forward
  · exact a.trans embed
  · cases endpoint
    · simp only [normBody,if_true,Bool.false_eq_true,if_false,
        BalancedCleanup.unnormalize,wires_append,Finset.union_subset_iff]
      exact ⟨⟨by simp [wires,Instr.wires],b.trans embed⟩,
        by simp [wires,Instr.wires]⟩
    · have known : wires (EndKnown.addK L.low L.ylow (L.carry.take 254) L.ymsb
          L.lower L.one BalancedCleanup.positiveLiteral)⊆
          (L.lower::L.one::L.ymsb::(L.low++L.carry.take 254++L.ylow)).toFinset := by
        intro q used
        rcases Finset.mem_union.mp (c used) with h|h
        · exact embed (b h)
        · simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
          tauto
      simp only [normBody,if_true,FifthCarry2.unnormalizeE,wires_append,
        Finset.union_subset_iff]
      exact ⟨⟨by simp [wires,Instr.wires],known⟩,
        by simp [wires,Instr.wires]⟩

private theorem envelope_fit (q : Wire)
    (h : q∈L.y ∨ q∈L.r ∨ q∈carries ∨ q=L.sign ∨ q=L.parity ∨ q=L.one ∨ q=L.lower) :
    q∈footprint := by
  have lo : L.lower∈carries := by rw [carries_shape]; simp [L,Q6EndpointCell.ports]
  simp only [footprint,List.mem_toFinset,List.mem_cons,List.mem_append]
  rcases h with h|h|h|rfl|rfl|rfl|rfl <;> tauto

private theorem tail_bounds :
    wires addTail⊆footprint ∧ wires topTail⊆footprint ∧
    (∀d,wires (cmpTail d)⊆footprint) ∧
    (∀d,wires (foldBody d)⊆footprint) ∧
    (∀d e,wires (normBody d e)⊆footprint) := by
  have yl (q : Wire) (h : q∈L.ylow) : q∈L.y := by
    simp only [BalancedCleanup.Layout.y,List.mem_append]; exact Or.inl h
  have low (q : Wire) (h : q∈L.low) : q∈L.r := by
    simp only [BalancedCleanup.Layout.r,List.mem_append]; exact Or.inl h
  have carry (q : Wire) (h : q∈L.carry.take 254) : q∈carries := by
    have shape := carry_front_shape
    rw [shape] at h
    rw [carries_shape]
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have head : carries.getD 0 0∈carries := by
    have bound : 0<carries.length := by
      rw [carries_shape]
      simp only [List.length_append,wireBlock,List.length_map,List.length_range',List.length_cons,List.length_nil]
      omega
    rw [List.getD_eq_getElem _ _ bound]
    exact List.getElem_mem _
  have ym : L.ymsb∈L.y := List.mem_append_right _ (List.mem_singleton_self _)
  have rm : L.rmsb∈L.r := List.mem_append_right _ (List.mem_singleton_self _)
  constructor
  · intro q used
    have h := add_envelope used
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    apply envelope_fit
    have ydrop : q∈L.ylow.drop 1 → q∈L.y := fun h => yl q (List.mem_of_mem_drop h)
    have rdrop : q∈L.low.drop 1 → q∈L.r := fun h => low q (List.mem_of_mem_drop h)
    have cdrop : q∈carries.drop 1 → q∈carries := List.mem_of_mem_drop
    rcases h with ((h|h)|h)|h
    · exact Or.inl (ydrop h)
    · exact Or.inr (Or.inl (rdrop h))
    · exact Or.inr (Or.inr (Or.inl (cdrop h)))
    · rcases h with rfl|rfl|rfl|rfl <;> tauto
  constructor
  · intro q used
    have h := top_envelope used
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    apply envelope_fit
    have xd : q∈(GuardCompression.source L).drop 1 → q∈L.y := by
      intro hx
      have full := List.mem_of_mem_drop hx
      simp only [GuardCompression.source,List.mem_append,List.mem_singleton] at full
      rcases full with h|rfl
      · exact h
      · exact ym
    have yd : q∈(BalancedCircuit.rawTarget L).drop 1 → q∈L.r ∨ q=L.one := by
      intro hy
      have full := List.mem_of_mem_drop hy
      simpa only [BalancedCircuit.rawTarget,List.mem_append,List.mem_singleton] using full
    have cd : q∈carries.drop 1 → q∈carries := List.mem_of_mem_drop
    rcases h with rfl|(h|h)|h
    · tauto
    · exact Or.inl (xd h)
    · have v := yd h; tauto
    · tauto
  constructor
  · intro d q used
    have h := cmp_envelope d used
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    have yd : q∈L.y.drop 1 → q∈L.y := List.mem_of_mem_drop
    have rd : q∈L.r.drop 1 → q∈L.r := List.mem_of_mem_drop
    have cd : q∈carries.drop 1 → q∈carries := List.mem_of_mem_drop
    apply envelope_fit
    rcases h with rfl|rfl|(h|h)|h <;> tauto
  constructor
  · intro d q used
    have h := fold_envelope d used
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
    apply envelope_fit
    rcases h with rfl|rfl|(h|h)|rfl
    · tauto
    · tauto
    · have v := low q h; tauto
    · have v := carry q h; tauto
    · tauto
  · intro d e q used
    have h := norm_envelope d e used
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    apply envelope_fit
    rcases h with rfl|rfl|rfl|(h|h)|h
    · tauto
    · tauto
    · tauto
    · have v := low q h; tauto
    · have v := carry q h; tauto
    · have v := yl q h; tauto

private theorem footprint_nodup :
    (L.sign::L.parity::L.one::(L.y++L.r++carries)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp
    (BalancedCircuit.allND L Rolling1588Lifetime.half_ports_nodup760) q
  have take := (List.take_sublist 254 L.carry).count_le q
  simp only [carries_take,List.count_cons,List.count_append,List.count_nil] at h take ⊢
  omega

private theorem removed_not_mem (xs ys : List Wire) (host : Wire) (nd : xs.Nodup)
    (counts : ∀q,xs.count q=ys.count q+(if host==q then 1 else 0)) : host∉ys := by
  intro used
  have count := counts host
  have bound := List.nodup_iff_count.mp nd host
  have positive := List.count_pos_iff.mpr used
  simp only [beq_self_eq_true,if_true] at count
  omega

private theorem local_host_absence :
    L.r0∉wires addTail ∧ L.r0∉wires topTail ∧
    (∀d,L.one∉wires (cmpTail d)) ∧
    (∀d,L.rmsb∉wires (foldBody d)) ∧
    (∀d e,L.rmsb∉wires (normBody d e)) := by
  let withoutLow := L.sign::L.parity::L.one::(L.y++L.rtail++[L.rmsb]++carries)
  let withoutOne := L.sign::L.parity::(L.y++L.r++carries)
  let withoutHigh := L.sign::L.parity::L.one::(L.y++L.low++carries)
  have lowOff : L.r0∉withoutLow := by
    apply removed_not_mem _ _ _ footprint_nodup
    intro q
    simp only [withoutLow,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.count_cons,List.count_append,List.count_nil]
    omega
  have oneOff : L.one∉withoutOne := by
    apply removed_not_mem _ _ _ footprint_nodup
    intro q
    simp only [withoutOne,List.count_cons,List.count_append]
    omega
  have highOff : L.rmsb∉withoutHigh := by
    apply removed_not_mem _ _ _ footprint_nodup
    intro q
    simp only [withoutHigh,BalancedCleanup.Layout.r,List.count_cons,List.count_append,List.count_nil]
    omega
  have lower : L.lower∈carries := by
    rw [carries_take]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have head : carries.getD 0 0∈carries := by
    have bound : 0<carries.length := by
      rw [carries_shape]
      simp only [List.length_append,wireBlock,List.length_map,List.length_range',List.length_cons,List.length_nil]
      omega
    rw [List.getD_eq_getElem _ _ bound]
    exact List.getElem_mem _
  have ym : L.ymsb∈L.y := List.mem_append_right _ (List.mem_singleton_self _)
  have ylow (q : Wire) (h : q∈L.ylow) : q∈L.y := List.mem_append_left _ h
  have ydrop (q : Wire) (h : q∈L.ylow.drop 1) : q∈L.y := ylow q (List.mem_of_mem_drop h)
  have cdrop (q : Wire) (h : q∈carries.drop 1) : q∈carries := List.mem_of_mem_drop h
  have lowDrop : L.low.drop 1=L.rtail := rfl
  have targetDrop : (BalancedCircuit.rawTarget L).drop 1=L.rtail++[L.rmsb]++[L.one] := rfl
  have carry (q : Wire) (h : q∈L.carry.take 254) : q∈carries := by
    rw [carries_take]
    exact List.mem_append_left _ h
  have toLow (q : Wire) (h : q∈L.y ∨ q∈L.rtail ∨ q∈carries ∨ q=L.one ∨ q=L.rmsb) :
      q∈withoutLow := by
    simp only [withoutLow,List.mem_cons,List.mem_append]
    tauto
  have toOne (q : Wire) (h : q∈L.y ∨ q∈L.r ∨ q∈carries ∨ q=L.parity) : q∈withoutOne := by
    simp only [withoutOne,List.mem_cons,List.mem_append]
    tauto
  have toHigh (q : Wire) (h : q∈L.y ∨ q∈L.low ∨ q∈carries ∨ q=L.one) : q∈withoutHigh := by
    simp only [withoutHigh,List.mem_cons,List.mem_append]
    tauto
  have addFit (q : Wire) (used : q∈wires addTail) : q∈withoutLow := by
    have h := add_envelope used
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    apply toLow
    rcases h with ((h|h)|h)|h
    · exact Or.inl (ydrop _ h)
    · rw [lowDrop] at h; tauto
    · have c := cdrop _ h; tauto
    · rcases h with rfl|rfl|rfl|rfl <;> tauto
  have topFit (q : Wire) (used : q∈wires topTail) : q∈withoutLow := by
    have h := top_envelope used
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    apply toLow
    rcases h with rfl|(h|h)|h
    · tauto
    · have full := List.mem_of_mem_drop h
      simp only [GuardCompression.source,List.mem_append,List.mem_singleton] at full
      rcases full with h|rfl <;> tauto
    · rw [targetDrop] at h
      simp only [List.mem_append,List.mem_singleton] at h
      tauto
    · have c := cdrop _ h; tauto
  have cmpFit (d : Bool) (q : Wire) (used : q∈wires (cmpTail d)) : q∈withoutOne := by
    have h := cmp_envelope d used
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    apply toOne
    rcases h with rfl|rfl|(h|h)|h
    · tauto
    · tauto
    · have y := List.mem_of_mem_drop h; tauto
    · have r := List.mem_of_mem_drop h; tauto
    · have c := cdrop _ h; tauto
  have foldFit (d : Bool) (q : Wire) (used : q∈wires (foldBody d)) : q∈withoutHigh := by
    have h := fold_envelope d used
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h
    apply toHigh
    rcases h with rfl|rfl|(h|h)|rfl
    · tauto
    · tauto
    · tauto
    · have c := carry _ h; tauto
    · tauto
  have normFit (d e : Bool) (q : Wire) (used : q∈wires (normBody d e)) : q∈withoutHigh := by
    have h := norm_envelope d e used
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
    apply toHigh
    rcases h with rfl|rfl|rfl|(h|h)|h
    · tauto
    · tauto
    · tauto
    · tauto
    · have c := carry _ h; tauto
    · have y := ylow _ h; tauto
  exact ⟨fun used => lowOff (addFit _ used),fun used => lowOff (topFit _ used),
    fun d used => oneOff (cmpFit d _ used),fun d used => highOff (foldFit d _ used),
    fun d e used => highOff (normFit d e _ used)⟩


private theorem moved_bounds (retired : Nat) (hr : retired=719∨retired=720∨retired=760) :
    wires (move (base retired) L.r0 addTail)⊆footprint.erase (base retired) ∧
    wires (move (base retired) L.r0 topTail)⊆footprint.erase (base retired) ∧
    (∀d,wires (move (base retired) L.one (cmpTail d))⊆footprint.erase (base retired)) ∧
    (∀d,wires (move (base retired) L.rmsb (foldBody d))⊆footprint.erase (base retired)) ∧
    (∀d e,wires (move (base retired) L.rmsb (normBody d e))⊆footprint.erase (base retired)) := by
  have r0 : L.r0∈footprint := envelope_fit _ (Or.inr (Or.inl (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])))
  have one : L.one∈footprint := envelope_fit _ (by simp)
  have rmsb : L.rmsb∈footprint := envelope_fit _ (Or.inr (Or.inl (by simp [BalancedCleanup.Layout.r])))
  have r0Ne : base retired≠L.r0 := by
    rcases hr with rfl|rfl|rfl <;> decide
  have oneNe : base retired≠L.one := by
    rcases hr with rfl|rfl|rfl <;> decide
  have highNe : base retired≠L.rmsb := by
    rcases hr with rfl|rfl|rfl <;> decide
  exact ⟨move_support_erase _ _ _ _ r0Ne tail_bounds.1 r0 local_host_absence.1,
    move_support_erase _ _ _ _ r0Ne tail_bounds.2.1 r0 local_host_absence.2.1,
    fun d => move_support_erase _ _ _ _ oneNe (tail_bounds.2.2.1 d) one
      (local_host_absence.2.2.1 d),
    fun d => move_support_erase _ _ _ _ highNe (tail_bounds.2.2.2.1 d) rmsb
      (local_host_absence.2.2.2.1 d),
    fun d e => move_support_erase _ _ _ _ highNe (tail_bounds.2.2.2.2 d e) rmsb
      (local_host_absence.2.2.2.2 d e)⟩

private theorem sign_support (c : Wire) (xs : List Wire) (S : Finset Wire)
    (hc : c∈S) (hx : xs.toFinset⊆S) : wires (signComplement c xs)⊆S := by
  intro q used
  have h := signComplement_wires_subset c xs used
  simp only [List.mem_toFinset,List.mem_cons] at h
  rcases h with rfl|h
  · exact hc
  · exact hx (List.mem_toFinset.mpr h)

private theorem rotate_support (right : Bool) (xs : List Wire) :
    wires (if right then rotateRight xs else rotateLeft xs)⊆xs.toFinset := by
  cases right
  · change wires (rotateLeft xs)⊆xs.toFinset
    rw [(rotate_wires xs).2]
    split <;> simp
  · change wires (rotateRight xs)⊆xs.toFinset
    rw [(rotate_wires xs).1]
    split <;> simp

private theorem data_parts :
    wires (GuardCompression.seed L)⊆dataSites ∧
    wires (OneReuse.newPrepare L)⊆dataSites ∧
    wires (rotateRight (BalancedCircuit.rawTarget L))⊆dataSites ∧
    wires (rotateLeft (BalancedCircuit.rawTarget L))⊆dataSites ∧
    wires (BalancedCleanup.prepareSign L.toLayout)⊆dataSites ∧
    wires (BalancedCleanup.prepareCompare L.toLayout)⊆dataSites ∧
    wires (BiasedCircuit.flipBias L)⊆dataSites ∧
    wires (BiasedInverse.unbiasView L)⊆dataSites ∧
    wires (Q6StructuralCell.exposure L)⊆dataSites ∧
    wires (signComplement L.sign L.y)⊆dataSites ∧
    wires (notRegister (BalancedCircuit.rawTarget L))⊆dataSites ∧
    wires (notRegister (L.one::L.r))⊆dataSites := by
  have ys : L.y.toFinset⊆dataSites := by
    intro q h; simp only [dataSites,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
  have rs : L.r.toFinset⊆dataSites := by
    intro q h; simp only [dataSites,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢; tauto
  have sign : L.sign∈dataSites := by simp [dataSites]
  have lower : L.lower∈dataSites := by simp [dataSites]
  have r0 : L.r0∈dataSites := rs (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  have rmsb : L.rmsb∈dataSites := rs (by simp [BalancedCleanup.Layout.r])
  have ymsb : L.ymsb∈dataSites := ys (by simp [BalancedCleanup.Layout.y])
  have one : L.one∈dataSites := by simp [dataSites]
  have parity : L.parity∈dataSites := by simp [dataSites]
  have firstY : L.ylow.getD 0 0∈dataSites := ys (by decide +kernel)
  have topR : L.rtail.getD 253 0∈dataSites := rs (by decide +kernel)
  have topR' : L.r.getD 254 0∈dataSites := rs (by decide +kernel)
  have target : (BalancedCircuit.rawTarget L).toFinset⊆dataSites := by
    intro q h
    simp only [BalancedCircuit.rawTarget,List.mem_toFinset,List.mem_append,List.mem_singleton] at h
    rcases h with h|rfl
    · exact rs (List.mem_toFinset.mpr h)
    · exact one
  have sc := sign_support L.sign L.y dataSites sign ys
  have cr := sign_support L.lower L.r dataSites lower rs
  have cy := sign_support L.lower L.y dataSites lower ys
  have rr := (rotate_support true (BalancedCircuit.rawTarget L)).trans target
  have rl := (rotate_support false (BalancedCircuit.rawTarget L)).trans target
  have rot := (rotate_support false L.r).trans rs
  have ps : wires (BalancedCleanup.prepareSign L.toLayout)⊆dataSites := by
    simp only [BalancedCleanup.prepareSign,wires_append,Finset.union_subset_iff]
    constructor
    · simp only [wires,Instr.wires,Finset.union_subset_iff,Finset.insert_subset_iff,
        Finset.singleton_subset_iff,Finset.empty_subset]
      tauto
    · exact cr
  have pc : wires (BalancedCleanup.prepareCompare L.toLayout)⊆dataSites := by
    simp only [BalancedCleanup.prepareCompare,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨rot,?_⟩,sc⟩,cy⟩,?_⟩
    · simp only [wires,Instr.wires,Finset.union_subset_iff,Finset.insert_subset_iff,
        Finset.singleton_subset_iff,Finset.empty_subset]
      tauto
    · simp only [wires,Instr.wires,Finset.union_subset_iff,Finset.singleton_subset_iff,Finset.empty_subset]
      tauto
  have seed : wires (GuardCompression.seed L)⊆dataSites := by
    simp only [GuardCompression.seed,wires,Instr.wires,Finset.union_subset_iff,
      Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.empty_subset]
    tauto
  have prep : wires (OneReuse.newPrepare L)⊆dataSites := by
    simp only [OneReuse.newPrepare,wires,Instr.wires,Finset.union_subset_iff,
      Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.empty_subset]
    tauto
  have bias : wires (BiasedCircuit.flipBias L)⊆dataSites := by
    simpa [BiasedCircuit.flipBias,wires,Instr.wires] using topR
  have view : wires (BiasedInverse.unbiasView L)⊆dataSites := by
    simp only [BiasedInverse.unbiasView,wires_append,wires_reverse,Finset.union_subset_iff]
    exact ⟨by simpa [wires,Instr.wires] using topR',ps⟩
  have exposure : wires (Q6StructuralCell.exposure L)⊆dataSites := by
    simp only [Q6StructuralCell.exposure,Arithmetic.Q6LowerExposure.expose,wires,Instr.wires,
      Finset.union_subset_iff,Finset.insert_subset_iff,Finset.singleton_subset_iff,Finset.empty_subset]
    tauto
  have nr : wires (notRegister (BalancedCircuit.rawTarget L))⊆dataSites := by
    rw [notRegister_wires]; exact target
  have nc : wires (notRegister (L.one::L.r))⊆dataSites := by
    rw [notRegister_wires,List.toFinset_cons]
    exact Finset.insert_subset_iff.mpr ⟨one,rs⟩
  exact ⟨seed,prep,rr,rl,ps,pc,bias,view,exposure,sc,nr,nc⟩

private def smallPieces : List Program :=
  let a := L.ylow.getD 0 0
  let b := L.low.getD 0 0
  let c := carries.getD 0 0
  [majority a b L.sign c,
   [.CX L.parity b,.CX a b,.CX L.sign b],
   eraseCarry a b L.sign c,
   [.CX a b,.CX L.sign b],
   [.CCX L.parity L.lower L.one,.CX L.lower L.rmsb],
   [.CX L.lower L.rmsb,.CX L.parity L.rmsb,.CX L.parity L.lower,
    .CX L.rmsb L.lower,.measureX L.one [] [.Z L.parity,.CZ L.parity L.rmsb]],
   [.CX L.parity L.lower,.CX L.rmsb L.lower,.CCX L.parity L.lower L.one,
    .CX L.lower L.rmsb,.CX L.parity L.rmsb],
   [.CX L.parity L.rmsb,.CX L.lower L.rmsb,.CX L.parity L.rmsb,
    .CX L.rmsb L.lower,.measureX L.one [] [.CZ L.parity L.rmsb]],
   majority (L.y.getD 0 0) (L.r.getD 0 0) L.one c,
   [.X L.one],eraseCarry (L.y.getD 0 0) (L.r.getD 0 0) L.one c,
   [.X b,.CX L.parity b],
   [.CX L.parity b,.X b],
   [.CX b L.parity,.CX (L.ylow.getD 0 0) L.parity,.CX L.rmsb L.one],
   [.CX L.parity L.r0],[.X L.sign],[.measureX L.one [] []]]

private def smallSites : Finset Wire :=
  [L.sign,L.parity,L.one,L.lower,L.rmsb,L.r0,L.ylow.getD 0 0,carries.getD 0 0].toFinset

private def physicalBool : Instr → Bool
  | .X _ => true
  | .CX c t => decide (c≠t)
  | .CCX a b t => decide (a≠t ∧ b≠t)
  | .measureX _ _ _ => true

private theorem physical_of_all (P : Program) (h : P.all physicalBool=true) : GatePhysical P := by
  unfold GatePhysical
  intro i hi
  have fact := (List.all_eq_true.mp h) i hi
  cases i <;> simp_all [physicalBool,PhysicalInstr,ProperGate]

private theorem small_leaf_certificate :
    ∀P∈smallPieces,wires P⊆smallSites ∧ GatePhysical P := by
  have certificate : smallPieces.all
      (fun P => decide (wires P⊆smallSites) && P.all physicalBool)=true := by decide +kernel
  intro P member
  have fact := Bool.and_eq_true_iff.mp ((List.all_eq_true.mp certificate) P member)
  exact ⟨of_decide_eq_true fact.1,physical_of_all P fact.2⟩

private theorem small_erased (retired : Nat) (hr : retired=719∨retired=720∨retired=760) :
    smallSites⊆footprint.erase (base retired) := by
  have data := data_erased retired hr
  have ys : L.y.toFinset⊆dataSites := by
    intro q h
    simp only [dataSites,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have rs : L.r.toFinset⊆dataSites := by
    intro q h
    simp only [dataSites,List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  have yhead : L.ylow.getD 0 0∈dataSites := by
    apply ys
    apply List.mem_toFinset.mpr
    change L.ylow.getD 0 0∈L.ylow++[L.ymsb]
    apply List.mem_append_left
    have bound : 0<L.ylow.length := by
      rw [(Q6EndpointCell.ports_widths base (base 2409)).2.1]
      omega
    rw [List.getD_eq_getElem _ _ bound]
    exact List.getElem_mem _
  have head : carries.getD 0 0=base 512 := by
    rw [carries_shape]
    change ((List.range' 512 (252+1)).map base++[base 1540,base 1797]).getD 0 0=base 512
    rw [List.range'_succ]
    rfl
  have chead : carries.getD 0 0∈footprint.erase (base retired) := by
    apply Finset.mem_erase.mpr
    constructor
    · rw [head]
      intro same
      have equal := base_injective same
      omega
    · apply envelope_fit
      apply Or.inr; apply Or.inr; apply Or.inl
      have bound : 0<carries.length := by
        rw [carries_shape]
        simp only [List.length_append,wireBlock,List.length_map,List.length_range',
          List.length_cons,List.length_nil]
        omega
      rw [List.getD_eq_getElem _ _ bound]
      exact List.getElem_mem _
  have sign : L.sign∈dataSites := by simp only [dataSites,List.mem_toFinset,List.mem_cons]; tauto
  have parity : L.parity∈dataSites := by simp only [dataSites,List.mem_toFinset,List.mem_cons]; tauto
  have one : L.one∈dataSites := by simp only [dataSites,List.mem_toFinset,List.mem_cons]; tauto
  have lower : L.lower∈dataSites := by simp only [dataSites,List.mem_toFinset,List.mem_cons]; tauto
  have rmsb : L.rmsb∈dataSites := rs (by simp [BalancedCleanup.Layout.r])
  have r0 : L.r0∈dataSites := rs (by simp [BalancedCleanup.Layout.r,BalancedCleanup.Layout.low])
  intro q h
  simp only [smallSites,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact data sign
  · exact data parity
  · exact data one
  · exact data lower
  · exact data rmsb
  · exact data r0
  · exact data yhead
  · exact chead

private theorem small_support (retired : Nat) (hr : retired=719∨retired=720∨retired=760)
    (P : Program) (h : P∈smallPieces) : wires P⊆footprint.erase (base retired) :=
  (small_leaf_certificate P h).1.trans (small_erased retired hr)

private theorem y_head : L.y.getD 0 0=L.ylow.getD 0 0 := by
  change (L.ylow++[L.ymsb]).getD 0 0=L.ylow.getD 0 0
  apply List.getD_append
  rw [(Q6EndpointCell.ports_widths base (base 2409)).2.1]
  omega

private theorem source_head : (GuardCompression.source L).getD 0 0=L.ylow.getD 0 0 := by
  have bound : 0<L.ylow.length := by
    rw [(Q6EndpointCell.ports_widths base (base 2409)).2.1]
    omega
  change ((L.ylow++[L.ymsb])++[L.ymsb]).getD 0 0=L.ylow.getD 0 0
  rw [List.getD_append _ _ _ _ (by simp),List.getD_append _ _ _ _ bound]

private theorem changed_support (retired : Nat) (hr : retired=719∨retired=720∨retired=760) :
    wires (rawAdd (base retired) L)⊆footprint.erase (base retired) ∧
    wires (rawSubTail (base retired) L)⊆footprint.erase (base retired) ∧
    wires (fold (base retired) L)⊆footprint.erase (base retired) ∧
    wires (unfoldStep (base retired) L)⊆footprint.erase (base retired) ∧
    (∀d,wires (compare (base retired) d L)⊆footprint.erase (base retired)) ∧
    wires (normalize (base retired) L)⊆footprint.erase (base retired) ∧
    (∀e,wires (unnormalize (base retired) e L)⊆footprint.erase (base retired)) := by
  have moved := moved_bounds retired hr
  have sc := data_parts.2.2.2.2.2.2.2.2.2.1.trans (data_erased retired hr)
  have nr := data_parts.2.2.2.2.2.2.2.2.2.2.1.trans (data_erased retired hr)
  have nc := data_parts.2.2.2.2.2.2.2.2.2.2.2.trans (data_erased retired hr)
  have s0 := small_support retired hr _ (show smallPieces[0]!∈smallPieces by decide +kernel)
  have s1 := small_support retired hr _ (show smallPieces[1]!∈smallPieces by decide +kernel)
  have s2 := small_support retired hr _ (show smallPieces[2]!∈smallPieces by decide +kernel)
  have s3 := small_support retired hr _ (show smallPieces[3]!∈smallPieces by decide +kernel)
  have s4 := small_support retired hr _ (show smallPieces[4]!∈smallPieces by decide +kernel)
  have s5 := small_support retired hr _ (show smallPieces[5]!∈smallPieces by decide +kernel)
  have s6 := small_support retired hr _ (show smallPieces[6]!∈smallPieces by decide +kernel)
  have s7 := small_support retired hr _ (show smallPieces[7]!∈smallPieces by decide +kernel)
  have s8 := small_support retired hr _ (show smallPieces[8]!∈smallPieces by decide +kernel)
  have s9 := small_support retired hr _ (show smallPieces[9]!∈smallPieces by decide +kernel)
  have s10 := small_support retired hr _ (show smallPieces[10]!∈smallPieces by decide +kernel)
  have s11 := small_support retired hr _ (show smallPieces[11]!∈smallPieces by decide +kernel)
  have s12 := small_support retired hr _ (show smallPieces[12]!∈smallPieces by decide +kernel)
  have s13 := small_support retired hr _ (show smallPieces[13]!∈smallPieces by decide +kernel)
  change wires (majority (L.ylow.getD 0 0) (L.low.getD 0 0) L.sign (carries.getD 0 0))⊆_ at s0
  change wires [.CX L.parity (L.low.getD 0 0),.CX (L.ylow.getD 0 0) (L.low.getD 0 0),
    .CX L.sign (L.low.getD 0 0)]⊆_ at s1
  simp only [smallPieces,List.getElem!_cons_zero,List.getElem!_cons_succ] at s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13
  have firstX : (GuardCompression.source L).getD 0 0=L.ylow.getD 0 0 := source_head
  have firstY : (BalancedCircuit.rawTarget L).getD 0 0=L.low.getD 0 0 := rfl
  have firstR : L.r.getD 0 0=L.low.getD 0 0 := rfl
  have firstSource : L.y.getD 0 0=L.ylow.getD 0 0 := y_head
  constructor
  · simp only [rawAdd,wires_append,wires_reverse,Finset.union_subset_iff]
    tauto
  constructor
  · simp only [rawSubTail,firstX,firstY,wires_append,Finset.union_subset_iff]
    tauto
  constructor
  · simpa only [fold,if_true,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro s4 (moved.2.2.2.1 true)) s5
  constructor
  · simpa only [unfoldStep,Bool.false_eq_true,if_false,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro s6 (moved.2.2.2.1 false)) s7
  constructor
  · intro d
    simpa only [compare,firstR,firstSource,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro (And.intro (And.intro (And.intro (And.intro nc s8) s9)
        (moved.2.2.1 d)) s9) s10) nc
  constructor
  · exact moved.2.2.2.2 false false
  · intro e
    exact moved.2.2.2.2 true e

private theorem forward_support_erased (retired : Nat) (hr : retired=719∨retired=720∨retired=760)
    (endpoint : Bool) : wires (forward (base retired) endpoint L)⊆footprint.erase (base retired) := by
  have data := data_parts
  have shrink := data_erased retired hr
  have changed := changed_support retired hr
  have seed := data.1.trans shrink
  have prep := data.2.1.trans shrink
  have rotate := data.2.2.1.trans shrink
  have sign := data.2.2.2.2.1.trans shrink
  have view := data.2.2.2.2.2.1.trans shrink
  have bias := data.2.2.2.2.2.2.1.trans shrink
  have exposure := data.2.2.2.2.2.2.2.2.1.trans shrink
  have finish := small_support retired hr _ (show smallPieces[16]!∈smallPieces by decide +kernel)
  simp only [forward,wires_append,wires_reverse,Finset.union_subset_iff]
  have cmp := changed.2.2.2.2.1 true
  have norm := changed.2.2.2.2.2.2 endpoint
  tauto

private theorem inverse_support_erased (retired : Nat) (hr : retired=719∨retired=720∨retired=760) :
    wires (inverse (base retired) L)⊆footprint.erase (base retired) := by
  have data := data_parts
  have shrink := data_erased retired hr
  have changed := changed_support retired hr
  have rotate := data.2.2.2.1.trans shrink
  have sign := data.2.2.2.2.1.trans shrink
  have view := data.2.2.2.2.2.1.trans shrink
  have unbias := data.2.2.2.2.2.2.2.1.trans shrink
  have exposure := data.2.2.2.2.2.2.2.2.1.trans shrink
  have parity := small_support retired hr _ (show smallPieces[14]!∈smallPieces by decide +kernel)
  simp only [inverse,wires_append,wires_reverse,Finset.union_subset_iff]
  have cmp := changed.2.2.2.2.1 false
  have norm := changed.2.2.2.2.2.1
  tauto

private theorem half_support_erased (retired : Nat) (hr : retired=719∨retired=720∨retired=760)
    (divide : Bool) : wires (half (base retired) divide base (base 2409))⊆
      footprint.erase (base retired) := by
  have edge := small_support retired hr _ (show smallPieces[15]!∈smallPieces by decide +kernel)
  cases divide
  · simpa only [half,Bool.false_eq_true,if_false,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro edge (inverse_support_erased retired hr)) edge
  · simpa only [half,if_true,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro edge (forward_support_erased retired hr false)) edge

private theorem halfE_support_erased (retired : Nat) (hr : retired=719∨retired=720∨retired=760)
    (divide : Bool) : wires (halfE (base retired) divide base (base 2409))⊆
      footprint.erase (base retired) := by
  cases divide
  · exact half_support_erased retired hr false
  · have edge := small_support retired hr _ (show smallPieces[15]!∈smallPieces by decide +kernel)
    simpa only [halfE,if_true,wires_append,Finset.union_subset_iff] using
      And.intro (And.intro edge (forward_support_erased retired hr true)) edge

theorem half_retired_free (retired : Nat) (hr : retired=719∨retired=720∨retired=760) (divide : Bool) :
    base retired∉wires (half (base retired) divide base (base 2409)) := by
  intro used
  exact (Finset.mem_erase.mp (half_support_erased retired hr divide used)).1 rfl

theorem half_support_old (retired : Nat) (hr : retired=719∨retired=720∨retired=760) (divide : Bool) :
    wires (half (base retired) divide base (base 2409))⊆
      wires (Q6EndpointCell.half divide base (base 2409)) :=
  (half_support_erased retired hr divide).trans
    (Finset.erase_subset _ _ |>.trans (footprint_old_half divide))

theorem halfE_support_old (retired : Nat) (hr : retired=719∨retired=720∨retired=760) (divide : Bool) :
    wires (halfE (base retired) divide base (base 2409))⊆
      wires (Q6EndpointCell.halfE divide base (base 2409)) :=
  (halfE_support_erased retired hr divide).trans
    (Finset.erase_subset _ _ |>.trans (footprint_old_halfE divide))

private theorem addTop_physical (xs ys cs : List Wire) (cin : Wire)
    (nd : (cin::(ys++cs)).Nodup) (apart : List.Disjoint xs (cin::(ys++cs))) :
    GatePhysical (addTop xs ys cs cin) := by
  induction xs generalizing ys cs cin with
  | nil => simp [addTop,GatePhysical]
  | cons a xs ih =>
    cases xs with
    | nil => cases ys <;> simp [addTop,GatePhysical]
    | cons a' xs =>
      cases ys with
      | nil => simp [addTop,GatePhysical]
      | cons b ys =>
        cases ys with
        | nil => simp [addTop,GatePhysical]
        | cons b' ys =>
          have ab : a≠b := fun e => List.disjoint_left.mp apart List.mem_cons_self (by simp [e])
          have cb : cin≠b := by
            intro e
            have h := (List.nodup_cons.mp nd).1
            exact h (by simp [e])
          by_cases last : xs=[] ∧ ys=[]
          · rcases last with ⟨rfl,rfl⟩
            have bb : b≠b' := by
              have h := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
              intro e; exact h (by simp [e])
            simp [addTop,dependentTop,GatePhysical,PhysicalInstr,ProperGate,ab,cb,bb]
          · cases cs with
            | nil =>
              cases xs <;> cases ys <;> simp_all [addTop,GatePhysical]
            | cons c cs =>
              have localND : [a,b,cin,c].Nodup := by
                have small : [b,cin,c].Nodup := by
                  apply List.nodup_iff_count.mpr
                  intro q
                  have h := List.nodup_iff_count.mp nd q
                  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
                  omega
                have off : a∉[b,cin,c] := by
                  intro h
                  apply List.disjoint_left.mp apart List.mem_cons_self
                  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at h ⊢
                  tauto
                exact List.nodup_cons.mpr ⟨off,small⟩
              have tailND : (c::((b'::ys)++cs)).Nodup := by
                apply List.nodup_iff_count.mpr
                intro q
                have h := List.nodup_iff_count.mp nd q
                simp only [List.count_cons,List.count_append] at h ⊢
                omega
              have tailApart : List.Disjoint (a'::xs) (c::((b'::ys)++cs)) := by
                apply List.disjoint_left.mpr
                intro q hq h
                apply List.disjoint_left.mp apart (List.mem_cons_of_mem _ hq)
                simp only [List.mem_cons,List.mem_append] at h ⊢
                tauto
              rw [addTop_step a a' b b' c cin xs ys cs last]
              simp only [gatePhysical_append]
              exact ⟨⟨⟨majority_physical _ _ _ _ localND,ih (b'::ys) cs c tailND tailApart⟩,
                eraseCarry_physical _ _ _ _⟩,by simp [GatePhysical,PhysicalInstr,ProperGate,ab,cb]⟩

private theorem carries_head : carries=carries.getD 0 0::carries.drop 1 := by
  have nonempty : carries≠[] := by
    intro e
    have len : carries.length=255 := by
      rw [carries_shape]
      simp only [List.length_append,wireBlock,List.length_map,List.length_range',List.length_cons,List.length_nil]
    rw [e] at len
    contradiction
  generalize carries=xs at nonempty ⊢
  cases xs
  · exact (nonempty rfl).elim
  · rfl

private theorem tail_physical :
    GatePhysical addTail ∧ GatePhysical topTail ∧
    (∀d,GatePhysical (cmpTail d)) ∧ (∀d,GatePhysical (foldBody d)) ∧
    (∀d e,GatePhysical (normBody d e)) := by
  have widths := Q6EndpointCell.ports_widths base (base 2409)
  have nd := Rolling1588Lifetime.half_ports_nodup760
  have cleanupND : L.toLayout.wires.Nodup := (List.nodup_append'.mp nd).2.1
  have cleanup := OneBankPhysical5.cleanup_physical L.toLayout widths cleanupND
  have cleanupParts := cleanup
  simp only [BalancedCleanup.program,gatePhysical_append] at cleanupParts
  have addOld := Q6EndpointCell.kernel_physical true base base_injective
  simp only [OwnQ6Core5.kernel,if_true,Q6StructuralCell.forward,
    Q6StructuralCell.forwardPrefix,gatePhysical_append] at addOld
  have raw : GatePhysical (Q6Structural.rawAdd L) := by tauto
  have outer : GatePhysical (CoherentTail.addPrefix L.ylow L.low carries
      L.ymsb L.rmsb L.one L.sign) := by
    simp only [Q6Structural.rawAdd,FifthCarry.rawAdd,Q6Structural.carryLayout,
      gatePhysical_append] at raw
    tauto
  have addChild (a b c aTop bTop one cin : Wire) (xs ys cs : List Wire)
      (hp : GatePhysical (CoherentTail.addPrefix (a::xs) (b::ys) (c::cs) aTop bTop one cin)) :
      GatePhysical (CoherentTail.addPrefix xs ys cs aTop bTop one c) := by
    simp only [CoherentTail.addPrefix,gatePhysical_append] at hp
    exact hp.1.1.2
  have yhead : L.ylow=L.ylow.getD 0 0::L.ylow.drop 1 := by
    have ne : L.ylow≠[] := by
      intro e
      have len := widths.2.1
      rw [e] at len
      contradiction
    generalize L.ylow=xs at ne ⊢
    cases xs
    · exact (ne rfl).elim
    · rfl
  have rhead : L.low=L.low.getD 0 0::L.low.drop 1 := rfl
  have addP : GatePhysical addTail := by
    apply addChild (L.ylow.getD 0 0) (L.low.getD 0 0) (carries.getD 0 0)
      L.ymsb L.rmsb L.one L.sign (L.ylow.drop 1) (L.low.drop 1) (carries.drop 1)
    rw [←yhead,←rhead,←carries_head]
    exact outer
  have targetND : (carries.getD 0 0::
      ((BalancedCircuit.rawTarget L).drop 1++carries.drop 1)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp footprint_nodup q
    have dropped := (List.drop_sublist 1 (BalancedCircuit.rawTarget L)).count_le q
    rw [carries_head] at h
    simp only [BalancedCircuit.rawTarget,List.count_cons,List.count_append,List.count_nil] at h dropped ⊢
    omega
  have yApart : List.Disjoint L.y (L.one::(L.r++carries)) := by
    apply List.disjoint_left.mpr
    intro q hy other
    have h := List.nodup_iff_count.mp footprint_nodup q
    have yCount := List.count_pos_iff.mpr hy
    have otherCount := List.count_pos_iff.mpr other
    simp only [List.count_cons,List.count_append] at h otherCount
    omega
  have topApart : List.Disjoint ((GuardCompression.source L).drop 1)
      (carries.getD 0 0::((BalancedCircuit.rawTarget L).drop 1++carries.drop 1)) := by
    apply List.disjoint_left.mpr
    intro q source target
    have hy : q∈L.y := by
      have full := List.mem_of_mem_drop source
      simp only [GuardCompression.source,List.mem_append,List.mem_singleton] at full
      rcases full with h|rfl
      · exact h
      · simp [BalancedCleanup.Layout.y]
    apply List.disjoint_left.mp yApart hy
    have head : carries.getD 0 0∈carries := by rw [carries_head]; simp
    have dropTarget : q∈(BalancedCircuit.rawTarget L).drop 1 → q∈L.r ∨ q=L.one := by
      intro h
      simpa only [BalancedCircuit.rawTarget,List.mem_append,List.mem_singleton] using List.mem_of_mem_drop h
    have dropCarry : q∈carries.drop 1 → q∈carries := List.mem_of_mem_drop
    simp only [List.mem_cons,List.mem_append] at target ⊢
    rcases target with rfl|h|h
    · tauto
    · have h' := dropTarget h; tauto
    · have h' := dropCarry h; tauto
  have topP : GatePhysical topTail := addTop_physical _ _ _ _ targetND topApart
  have cmpP (d : Bool) : GatePhysical (cmpTail d) := by
    apply compareChain_physical
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp footprint_nodup q
    have ydrop := (List.drop_sublist 1 L.y).count_le q
    have rdrop := (List.drop_sublist 1 L.r).count_le q
    rw [carries_head] at h
    simp only [List.count_cons,List.count_append] at h ⊢
    omega
  have window := OneReuse.window_physical L nd
  have folded (d : Bool) : GatePhysical (foldBody d) := by
    cases d <;>
      simp only [foldBody,if_true,Bool.false_eq_true,if_false] <;>
      simp only [OneReuse.foldWindow,OneReuse.unfoldWindow,gatePhysical_append] at window
    all_goals tauto
  have known := FifthCarry2.forwardE_physical L widths nd
  simp only [FifthCarry2.forwardE,FifthCarry2.forwardCoreE,FifthCarry2.cleanupE,
    FifthCarry2.cleanupRestE,gatePhysical_append] at known
  have normed (d e : Bool) : GatePhysical (normBody d e) := by
    cases d
    · exact cleanupParts.2.1
    · cases e
      · exact cleanupParts.2.2.2.2.2.1
      · tauto
  exact ⟨addP,topP,cmpP,folded,normed⟩

private theorem reverse_physical (P : Program) (hp : GatePhysical P) : GatePhysical P.reverse := by
  unfold GatePhysical at hp ⊢
  intro i hi
  exact hp i (List.mem_reverse.mp hi)

private theorem data_physical :
    GatePhysical (GuardCompression.seed L) ∧ GatePhysical (OneReuse.newPrepare L) ∧
    GatePhysical (rotateRight (BalancedCircuit.rawTarget L)) ∧
    GatePhysical (rotateLeft (BalancedCircuit.rawTarget L)) ∧
    GatePhysical (BalancedCleanup.prepareSign L.toLayout) ∧
    GatePhysical (BalancedCleanup.prepareCompare L.toLayout) ∧
    GatePhysical (BiasedCircuit.flipBias L) ∧ GatePhysical (BiasedInverse.unbiasView L) ∧
    GatePhysical (Q6StructuralCell.exposure L) ∧ GatePhysical (signComplement L.sign L.y) ∧
    GatePhysical (notRegister (BalancedCircuit.rawTarget L)) ∧ GatePhysical (notRegister (L.one::L.r)) := by
  have nd := Rolling1588Lifetime.half_ports_nodup760
  have cleanupND : L.toLayout.wires.Nodup := (List.nodup_append'.mp nd).2.1
  have cleanup := OneBankPhysical5.cleanup_physical L.toLayout
    (Q6EndpointCell.ports_widths base (base 2409)) cleanupND
  simp only [BalancedCleanup.program,gatePhysical_append] at cleanup
  have ps : GatePhysical (BalancedCleanup.prepareSign L.toLayout) := cleanup.1
  have pc : GatePhysical (BalancedCleanup.prepareCompare L.toLayout) := cleanup.2.2.1
  have rawND := (List.nodup_append'.mp (List.nodup_cons.mp (GuardCompression.rawFacts L nd).2.2).2).1
  have rotate := rotate_physical (BalancedCircuit.rawTarget L) rawND
  have seed : GatePhysical (GuardCompression.seed L) := physical_of_all _ (by decide +kernel)
  have prep : GatePhysical (OneReuse.newPrepare L) := physical_of_all _ (by decide +kernel)
  have bias : GatePhysical (BiasedCircuit.flipBias L) := by
    simp [BiasedCircuit.flipBias,GatePhysical,PhysicalInstr,ProperGate]
  have view : GatePhysical (BiasedInverse.unbiasView L) := by
    simp only [BiasedInverse.unbiasView,gatePhysical_append]
    exact ⟨by simp [GatePhysical,PhysicalInstr,ProperGate],reverse_physical _ ps⟩
  have exposure : GatePhysical (Q6StructuralCell.exposure L) := physical_of_all _ (by decide +kernel)
  have sc : GatePhysical (signComplement L.sign L.y) := by
    apply signComplement_physical
    rw [y_shape]
    exact OwnPlusHost.not_block 2409 770 256 (by omega)
  exact ⟨seed,prep,rotate.1,rotate.2,ps,pc,bias,view,exposure,sc,
    notRegister_physical _,notRegister_physical _⟩

private theorem changed_physical (retired : Nat) :
    GatePhysical (rawAdd (base retired) L) ∧ GatePhysical (rawSubTail (base retired) L) ∧
    GatePhysical (fold (base retired) L) ∧ GatePhysical (unfoldStep (base retired) L) ∧
    (∀d,GatePhysical (compare (base retired) d L)) ∧ GatePhysical (normalize (base retired) L) ∧
    (∀e,GatePhysical (unnormalize (base retired) e L)) := by
  have movedAdd := move_physical (base retired) L.r0 addTail tail_physical.1
  have movedTop := move_physical (base retired) L.r0 topTail tail_physical.2.1
  have movedCompare := fun d => move_physical (base retired) L.one (cmpTail d) (tail_physical.2.2.1 d)
  have movedFold := fun d => move_physical (base retired) L.rmsb (foldBody d) (tail_physical.2.2.2.1 d)
  have movedNorm := fun d e => move_physical (base retired) L.rmsb (normBody d e) (tail_physical.2.2.2.2 d e)
  have sc := data_physical.2.2.2.2.2.2.2.2.2.1
  have nr := data_physical.2.2.2.2.2.2.2.2.2.2.1
  have nc := data_physical.2.2.2.2.2.2.2.2.2.2.2
  have s0 := (small_leaf_certificate _ (show smallPieces[0]!∈smallPieces by decide +kernel)).2
  have s1 := (small_leaf_certificate _ (show smallPieces[1]!∈smallPieces by decide +kernel)).2
  have s2 := (small_leaf_certificate _ (show smallPieces[2]!∈smallPieces by decide +kernel)).2
  have s3 := (small_leaf_certificate _ (show smallPieces[3]!∈smallPieces by decide +kernel)).2
  have s4 := (small_leaf_certificate _ (show smallPieces[4]!∈smallPieces by decide +kernel)).2
  have s5 := (small_leaf_certificate _ (show smallPieces[5]!∈smallPieces by decide +kernel)).2
  have s6 := (small_leaf_certificate _ (show smallPieces[6]!∈smallPieces by decide +kernel)).2
  have s7 := (small_leaf_certificate _ (show smallPieces[7]!∈smallPieces by decide +kernel)).2
  have s8 := (small_leaf_certificate _ (show smallPieces[8]!∈smallPieces by decide +kernel)).2
  have s9 := (small_leaf_certificate _ (show smallPieces[9]!∈smallPieces by decide +kernel)).2
  have s10 := (small_leaf_certificate _ (show smallPieces[10]!∈smallPieces by decide +kernel)).2
  have s11 := (small_leaf_certificate _ (show smallPieces[11]!∈smallPieces by decide +kernel)).2
  have s12 := (small_leaf_certificate _ (show smallPieces[12]!∈smallPieces by decide +kernel)).2
  have s13 := (small_leaf_certificate _ (show smallPieces[13]!∈smallPieces by decide +kernel)).2
  simp only [smallPieces,List.getElem!_cons_zero,List.getElem!_cons_succ] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13
  have firstX : (GuardCompression.source L).getD 0 0=L.ylow.getD 0 0 := source_head
  have firstY : (BalancedCircuit.rawTarget L).getD 0 0=L.low.getD 0 0 := rfl
  constructor
  · simp only [rawAdd,gatePhysical_append]
    have reverseClear := reverse_physical _ s1
    tauto
  constructor
  · simp only [rawSubTail,firstX,firstY,gatePhysical_append]
    tauto
  constructor
  · simpa only [fold,if_true,gatePhysical_append] using And.intro (And.intro s4 (movedFold true)) s5
  constructor
  · simpa only [unfoldStep,Bool.false_eq_true,if_false,gatePhysical_append] using
      And.intro (And.intro s6 (movedFold false)) s7
  constructor
  · intro d
    simp only [compare,gatePhysical_append]
    have mid := movedCompare d
    tauto
  constructor
  · exact movedNorm false false
  · intro e; exact movedNorm true e

theorem half_physical (retired : Nat) (hr : retired=719∨retired=720∨retired=760) (divide : Bool) :
    GatePhysical (half (base retired) divide base (base 2409)) := by
  have retiredCase := hr
  clear retiredCase hr
  have changed := changed_physical retired
  have data := data_physical
  have edge := (small_leaf_certificate _ (show smallPieces[15]!∈smallPieces by decide +kernel)).2
  have finish := (small_leaf_certificate _ (show smallPieces[16]!∈smallPieces by decide +kernel)).2
  have parity := (small_leaf_certificate _ (show smallPieces[14]!∈smallPieces by decide +kernel)).2
  simp only [smallPieces,List.getElem!_cons_zero,List.getElem!_cons_succ] at edge finish parity
  have rs := reverse_physical _ data.2.2.2.2.1
  have rc := reverse_physical _ data.2.2.2.2.2.1
  have re := reverse_physical _ data.2.2.2.2.2.2.2.2.1
  cases divide <;> simp only [half,if_true,Bool.false_eq_true,if_false,forward,inverse,
    gatePhysical_append]
  all_goals
    have cmpF := changed.2.2.2.2.1 true
    have cmpI := changed.2.2.2.2.1 false
    have normF := changed.2.2.2.2.2.2 false
    tauto

theorem halfE_physical (retired : Nat) (hr : retired=719∨retired=720∨retired=760) (divide : Bool) :
    GatePhysical (halfE (base retired) divide base (base 2409)) := by
  cases divide
  · exact half_physical retired hr false
  · have changed := changed_physical retired
    have data := data_physical
    have edge := (small_leaf_certificate _ (show smallPieces[15]!∈smallPieces by decide +kernel)).2
    have finish := (small_leaf_certificate _ (show smallPieces[16]!∈smallPieces by decide +kernel)).2
    simp only [smallPieces,List.getElem!_cons_zero,List.getElem!_cons_succ] at edge finish
    have rs := reverse_physical _ data.2.2.2.2.1
    have rc := reverse_physical _ data.2.2.2.2.2.1
    have re := reverse_physical _ data.2.2.2.2.2.2.2.2.1
    have cmp := changed.2.2.2.2.1 true
    have norm := changed.2.2.2.2.2.2 true
    simp only [halfE,if_true,forward,gatePhysical_append]
    tauto

end ECDSAAdd.Entrant.Q6LifetimeResearch
end -- original module boundary


-- ===== R2Life760: helper facts about the generic half (same file, so GordoAR's private
-- footprint lemmas are visible) =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.Q6LifetimeResearch
open Arithmetic BalancedCircuit MappedCompressed RecordedQuantum

/-- The pad wire `base 1027` (the generic half's `one` flag) is a wire of both old halves. -/
theorem one_mem_old_half760 (divide : Bool) :
    base 1027∈wires (Q6EndpointCell.half divide base (base 2409)) := by
  have h : L.one∈footprint := by simp [footprint]
  exact footprint_old_half divide h

end ECDSAAdd.Entrant.Q6LifetimeResearch
end


-- ===== R2Life760: structural resource counts (no kernel evaluation of concrete programs) =====
section
/-! The lifetime half differs from the old generic half only in the head of the raw adder, the
fold/unfold windows, the two comparator chains (their leaves) and the top of the raw subtractor.
Each pair is compared by a list induction; the renamed windows keep their counts. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.R2Life760
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField Challenge Baselines

private theorem maj_c (a b c d : Wire) : toffoliCount (majority a b c d)=1 ∧
    measurementCount (majority a b c d)=0 ∧ gateSlots (majority a b c d)=6 := ⟨rfl,rfl,rfl⟩
private theorem ers_c (a b c d : Wire) : toffoliCount (eraseCarry a b c d)=0 ∧
    measurementCount (eraseCarry a b c d)=1 ∧ gateSlots (eraseCarry a b c d)=4 := ⟨rfl,rfl,rfl⟩

/-- New forward comparator chain against the old top-carry chain (`compareChainTop`). -/
theorem chain_true_counts (xs ys cs : List Wire) (e cin target : Wire)
    (hy : ys.length=xs.length) (hc : cs.length+1=xs.length) :
    toffoliCount (Q6LifetimeResearch.compareChain true xs ys cs cin target)=
      toffoliCount (TopCarry.compareChainTop xs ys (cs++[e]) cin target) ∧
    measurementCount (Q6LifetimeResearch.compareChain true xs ys cs cin target)=
      measurementCount (TopCarry.compareChainTop xs ys (cs++[e]) cin target) ∧
    gateSlots (Q6LifetimeResearch.compareChain true xs ys cs cin target)+2=
      gateSlots (TopCarry.compareChainTop xs ys (cs++[e]) cin target) := by
  induction cs generalizing xs ys cin with
  | nil =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | cons _ _ => simp at hc
      | nil =>
        cases ys with
        | nil => simp at hy
        | cons b ys =>
          cases ys with
          | cons _ _ => simp at hy
          | nil => exact ⟨rfl,rfl,rfl⟩
  | cons c cs ih =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | nil => simp at hc
      | cons a' as =>
        cases ys with
        | nil => simp at hy
        | cons b ys =>
          cases ys with
          | nil => simp at hy
          | cons b' bs =>
            have h := ih (a'::as) (b'::bs) c (by simpa using hy) (by simpa using hc)
            have eN : Q6LifetimeResearch.compareChain true (a::a'::as) (b::b'::bs) (c::cs) cin target=
                majority a b cin c++Q6LifetimeResearch.compareChain true (a'::as) (b'::bs) cs c target++
                  eraseCarry a b cin c := rfl
            have eO : TopCarry.compareChainTop (a::a'::as) (b::b'::bs) ((c::cs)++[e]) cin target=
                (majority a b cin c++TopCarry.compareChainTop (a'::as) (b'::bs) (cs++[e]) c target)++
                  eraseCarry a b cin c := by
              simp [TopCarry.compareChainTop]
            rw [eN,eO]
            simp only [toffoliCount_append,measurementCount_append,gateSlots_append,
              (maj_c a b cin c).1,(maj_c a b cin c).2.1,(maj_c a b cin c).2.2,
              (ers_c a b cin c).1,(ers_c a b cin c).2.1,(ers_c a b cin c).2.2]
            omega

/-- New inverse comparator chain against the library chain (`compareChain none`). -/
theorem chain_false_counts (xs ys cs : List Wire) (e cin target : Wire)
    (hy : ys.length=xs.length) (hc : cs.length+1=xs.length) :
    toffoliCount (Q6LifetimeResearch.compareChain false xs ys cs cin target)=
      toffoliCount (Arithmetic.compareChain none xs ys (cs++[e]) cin target) ∧
    measurementCount (Q6LifetimeResearch.compareChain false xs ys cs cin target)+1=
      measurementCount (Arithmetic.compareChain none xs ys (cs++[e]) cin target) ∧
    gateSlots (Q6LifetimeResearch.compareChain false xs ys cs cin target)+5=
      gateSlots (Arithmetic.compareChain none xs ys (cs++[e]) cin target) := by
  induction cs generalizing xs ys cin with
  | nil =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | cons _ _ => simp at hc
      | nil =>
        cases ys with
        | nil => simp at hy
        | cons b ys =>
          cases ys with
          | cons _ _ => simp at hy
          | nil => exact ⟨rfl,rfl,rfl⟩
  | cons c cs ih =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | nil => simp at hc
      | cons a' as =>
        cases ys with
        | nil => simp at hy
        | cons b ys =>
          cases ys with
          | nil => simp at hy
          | cons b' bs =>
            have h := ih (a'::as) (b'::bs) c (by simpa using hy) (by simpa using hc)
            have eN : Q6LifetimeResearch.compareChain false (a::a'::as) (b::b'::bs) (c::cs) cin target=
                majority a b cin c++Q6LifetimeResearch.compareChain false (a'::as) (b'::bs) cs c target++
                  eraseCarry a b cin c := rfl
            have eO : Arithmetic.compareChain none (a::a'::as) (b::b'::bs) ((c::cs)++[e]) cin target=
                majority a b cin c++Arithmetic.compareChain none (a'::as) (b'::bs) (cs++[e]) c target++
                  eraseCarry a b cin c := rfl
            rw [eN,eO]
            simp only [toffoliCount_append,measurementCount_append,gateSlots_append,
              (maj_c a b cin c).1,(maj_c a b cin c).2.1,(maj_c a b cin c).2.2,
              (ers_c a b cin c).1,(ers_c a b cin c).2.1,(ers_c a b cin c).2.2]
            omega

/-- New dependent-top adder against the old affine-top adder (`addInPlaceTop`). -/
theorem addTop_counts760 (xs ys cs : List Wire) (e cin : Wire)
    (hy : ys.length=xs.length) (hc : cs.length+2=xs.length) :
    toffoliCount (Q6LifetimeResearch.addTop xs ys cs cin)=
      toffoliCount (TopCarry.addInPlaceTop xs ys (cs++[e]) cin) ∧
    measurementCount (Q6LifetimeResearch.addTop xs ys cs cin)=
      measurementCount (TopCarry.addInPlaceTop xs ys (cs++[e]) cin) ∧
    gateSlots (Q6LifetimeResearch.addTop xs ys cs cin)+2=
      gateSlots (TopCarry.addInPlaceTop xs ys (cs++[e]) cin) := by
  induction cs generalizing xs ys cin with
  | nil =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | nil => simp at hc
      | cons a' xs =>
        cases xs with
        | cons _ _ => simp at hc
        | nil =>
          cases ys with
          | nil => simp at hy
          | cons b ys =>
            cases ys with
            | nil => simp at hy
            | cons z ys =>
              cases ys with
              | cons _ _ => simp at hy
              | nil => exact ⟨rfl,rfl,rfl⟩
  | cons c cs ih =>
    cases xs with
    | nil => simp at hc
    | cons a xs =>
      cases xs with
      | nil => simp at hc
      | cons a' as =>
        cases as with
        | nil => simp at hc
        | cons a'' as =>
          cases ys with
          | nil => simp at hy
          | cons b ys =>
            cases ys with
            | nil => simp at hy
            | cons b' bs =>
              cases bs with
              | nil => simp at hy
              | cons b'' bs =>
                have h := ih (a'::a''::as) (b'::b''::bs) c (by simpa using hy) (by simpa using hc)
                have eN : Q6LifetimeResearch.addTop (a::a'::a''::as) (b::b'::b''::bs) (c::cs) cin=
                    majority a b cin c++Q6LifetimeResearch.addTop (a'::a''::as) (b'::b''::bs) cs c++
                      eraseCarry a b cin c++[.CX a b,.CX cin b] := rfl
                have eO : TopCarry.addInPlaceTop (a::a'::a''::as) (b::b'::b''::bs) ((c::cs)++[e]) cin=
                    majority a b cin c++TopCarry.addInPlaceTop (a'::a''::as) (b'::b''::bs) (cs++[e]) c++
                      eraseCarry a b cin c++[.CX a b,.CX cin b] := by
                  simp [TopCarry.addInPlaceTop]
                rw [eN,eO]
                simp only [toffoliCount_append,measurementCount_append,gateSlots_append,
                  (maj_c a b cin c).1,(maj_c a b cin c).2.1,(maj_c a b cin c).2.2,
                  (ers_c a b cin c).1,(ers_c a b cin c).2.1,(ers_c a b cin c).2.2]
                simp only [toffoliCount,measurementCount,gateSlots_cons,gateSlots_nil,instructionSlots]
                omega


private theorem lists_cons {xs : List Wire} (h : xs≠[]) : ∃ a t, xs=a::t := List.exists_cons_of_ne_nil h

theorem fold_counts760 (retired : Wire) (L : BalancedCircuit.Layout) :
    toffoliCount (Q6LifetimeResearch.fold retired L)=toffoliCount (OneReuse.foldWindow L) ∧
    measurementCount (Q6LifetimeResearch.fold retired L)=measurementCount (OneReuse.foldWindow L) ∧
    gateSlots (Q6LifetimeResearch.fold retired L)=gateSlots (OneReuse.foldWindow L)+2 := by
  refine ⟨?_,?_,?_⟩ <;>
  simp only [Q6LifetimeResearch.fold,Q6LifetimeResearch.move,OneReuse.foldWindow,toffoliCount_append,
    measurementCount_append,gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    rename_gateSlots] <;>
  (try simp only [toffoliCount,measurementCount,gateSlots_cons,gateSlots_nil,instructionSlots,
    List.length_cons,List.length_nil]) <;>
  omega

theorem unfold_counts760 (retired : Wire) (L : BalancedCircuit.Layout) :
    toffoliCount (Q6LifetimeResearch.unfoldStep retired L)=toffoliCount (OneReuse.unfoldWindow L) ∧
    measurementCount (Q6LifetimeResearch.unfoldStep retired L)=measurementCount (OneReuse.unfoldWindow L) ∧
    gateSlots (Q6LifetimeResearch.unfoldStep retired L)=gateSlots (OneReuse.unfoldWindow L)+4 := by
  refine ⟨?_,?_,?_⟩ <;>
  simp only [Q6LifetimeResearch.unfoldStep,Q6LifetimeResearch.move,OneReuse.unfoldWindow,toffoliCount_append,
    measurementCount_append,gateSlots_append,(renameProgram_counts _ _).1,(renameProgram_counts _ _).2,
    rename_gateSlots] <;>
  (try simp only [toffoliCount,measurementCount,gateSlots_cons,gateSlots_nil,instructionSlots,
    List.length_cons,List.length_nil]) <;>
  omega

theorem normalize_counts760 (retired : Wire) (L : BalancedCircuit.Layout) :
    toffoliCount (Q6LifetimeResearch.normalize retired L)=toffoliCount (BalancedCleanup.normalize L.toLayout) ∧
    measurementCount (Q6LifetimeResearch.normalize retired L)=
      measurementCount (BalancedCleanup.normalize L.toLayout) ∧
    gateSlots (Q6LifetimeResearch.normalize retired L)=gateSlots (BalancedCleanup.normalize L.toLayout) := by
  refine ⟨?_,?_,?_⟩ <;>
  simp only [Q6LifetimeResearch.normalize,Q6LifetimeResearch.move,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,rename_gateSlots]

theorem unnormalize_counts760 (retired : Wire) (L : BalancedCircuit.Layout) :
    toffoliCount (Q6LifetimeResearch.unnormalize retired false L)=
      toffoliCount (BalancedCleanup.unnormalize L.toLayout) ∧
    measurementCount (Q6LifetimeResearch.unnormalize retired false L)=
      measurementCount (BalancedCleanup.unnormalize L.toLayout) ∧
    gateSlots (Q6LifetimeResearch.unnormalize retired false L)=
      gateSlots (BalancedCleanup.unnormalize L.toLayout) := by
  refine ⟨?_,?_,?_⟩ <;>
  simp only [Q6LifetimeResearch.unnormalize,Q6LifetimeResearch.move,Bool.false_eq_true,if_false,
    (renameProgram_counts _ _).1,(renameProgram_counts _ _).2,rename_gateSlots]

theorem rawAdd_counts760 (retired : Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (Q6LifetimeResearch.rawAdd retired L)=toffoliCount (Q6Structural.rawAdd L) ∧
    measurementCount (Q6LifetimeResearch.rawAdd retired L)=measurementCount (Q6Structural.rawAdd L) ∧
    gateSlots (Q6LifetimeResearch.rawAdd retired L)=gateSlots (Q6Structural.rawAdd L)+6 := by
  have eOld : Q6Structural.rawAdd L=signComplement L.sign L.y++
      CoherentTail.addPrefix L.ylow L.low ((Q6Structural.q6Carry L).take 255) L.ymsb L.rmsb L.one L.sign++
      signComplement L.sign L.y := rfl
  have cl : ((Q6Structural.q6Carry L).take 255).length=255 := by
    have len : (Q6Structural.q6Carry L).length=256 := (Q6StructuralCell.carry_widths L hw).2.2
    simp [List.length_take,len]
  have yl : L.ylow.length=255 := hw.2.1
  obtain ⟨a,ys,eY⟩ := lists_cons (xs:=L.ylow) (by intro h; rw [h] at yl; simp at yl)
  obtain ⟨c,cs,eC⟩ := lists_cons (xs:=(Q6Structural.q6Carry L).take 255) (by intro h; rw [h] at cl; simp at cl)
  have eL : L.low=L.r0::L.rtail := rfl
  rw [eOld]
  simp only [Q6LifetimeResearch.rawAdd,Q6LifetimeResearch.move]
  rw [eY,eC,eL]
  simp only [List.getD_cons_zero,List.drop_succ_cons,List.drop_zero,CoherentTail.addPrefix,
    toffoliCount_append,measurementCount_append,gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,rename_gateSlots,toffoliCount_reverse,measurementCount_reverse,
    reverse_gateSlots,(maj_c _ _ _ _).1,(maj_c _ _ _ _).2.1,(maj_c _ _ _ _).2.2,
    (ers_c _ _ _ _).1,(ers_c _ _ _ _).2.1,(ers_c _ _ _ _).2.2]
  simp only [toffoliCount,measurementCount,gateSlots_cons,gateSlots_nil,instructionSlots]
  omega

theorem compare_true_counts760 (retired : Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (Q6LifetimeResearch.compare retired true L)=toffoliCount (Q6Structural.compareForward L) ∧
    measurementCount (Q6LifetimeResearch.compare retired true L)=
      measurementCount (Q6Structural.compareForward L) ∧
    gateSlots (Q6LifetimeResearch.compare retired true L)+2=gateSlots (Q6Structural.compareForward L) := by
  have eOld : Q6Structural.compareForward L=
      TopCarryBorrow.compare L.y L.r ((Q6Structural.q6Carry L).take 255) L.one L.parity := rfl
  have w := BalancedCleanup.widths L.toLayout hw
  have cl : ((Q6Structural.q6Carry L).take 255).length=255 := by
    have len : (Q6Structural.q6Carry L).length=256 := (Q6StructuralCell.carry_widths L hw).2.2
    simp [List.length_take,len]
  have yl : L.y.length=256 := w.2.2.1
  have rl : L.r.length=256 := w.2.1
  obtain ⟨a,xs,eY⟩ := lists_cons (xs:=L.y) (by intro h; rw [h] at yl; simp at yl)
  obtain ⟨b,ys,eR⟩ := lists_cons (xs:=L.r) (by intro h; rw [h] at rl; simp at rl)
  obtain ⟨c,cs,eC⟩ := lists_cons (xs:=(Q6Structural.q6Carry L).take 255) (by intro h; rw [h] at cl; simp at cl)
  rw [eY] at yl
  rw [eR] at rl
  rw [eC] at cl
  have eT : TopCarryBorrow.compare (a::xs) (b::ys) (c::cs) L.one L.parity=
      notRegister (L.one::b::ys)++(majority a b L.one c++[.X L.one]++
        TopCarry.compareChainTop xs ys (cs++[L.one]) c L.parity++[.X L.one]++eraseCarry a b L.one c)++
      notRegister (L.one::b::ys) := rfl
  have ch := chain_true_counts xs ys cs L.one c L.parity (by simp at yl rl; omega) (by simp at yl cl; omega)
  rw [eOld]
  simp only [Q6LifetimeResearch.compare,Q6LifetimeResearch.move]
  rw [eY,eR,eC,eT]
  refine ⟨?_,?_,?_⟩ <;>
  simp only [List.getD_cons_zero,List.drop_succ_cons,List.drop_zero,
    toffoliCount_append,measurementCount_append,gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,rename_gateSlots,(maj_c _ _ _ _).1,(maj_c _ _ _ _).2.1,(maj_c _ _ _ _).2.2,
    (ers_c _ _ _ _).1,(ers_c _ _ _ _).2.1,(ers_c _ _ _ _).2.2] <;>
  (try simp only [toffoliCount,measurementCount,gateSlots_cons,gateSlots_nil,instructionSlots]) <;>
  omega

theorem compare_false_counts760 (retired : Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (Q6LifetimeResearch.compare retired false L)=toffoliCount (Q6Structural.compareInverse L) ∧
    measurementCount (Q6LifetimeResearch.compare retired false L)+1=
      measurementCount (Q6Structural.compareInverse L) ∧
    gateSlots (Q6LifetimeResearch.compare retired false L)+5=gateSlots (Q6Structural.compareInverse L) := by
  have eOld : Q6Structural.compareInverse L=
      CarryBorrow.compare L.y L.r ((Q6Structural.q6Carry L).take 255) L.one L.parity := rfl
  have w := BalancedCleanup.widths L.toLayout hw
  have cl : ((Q6Structural.q6Carry L).take 255).length=255 := by
    have len : (Q6Structural.q6Carry L).length=256 := (Q6StructuralCell.carry_widths L hw).2.2
    simp [List.length_take,len]
  have yl : L.y.length=256 := w.2.2.1
  have rl : L.r.length=256 := w.2.1
  obtain ⟨a,xs,eY⟩ := lists_cons (xs:=L.y) (by intro h; rw [h] at yl; simp at yl)
  obtain ⟨b,ys,eR⟩ := lists_cons (xs:=L.r) (by intro h; rw [h] at rl; simp at rl)
  obtain ⟨c,cs,eC⟩ := lists_cons (xs:=(Q6Structural.q6Carry L).take 255) (by intro h; rw [h] at cl; simp at cl)
  rw [eY] at yl
  rw [eR] at rl
  rw [eC] at cl
  have eT : CarryBorrow.compare (a::xs) (b::ys) (c::cs) L.one L.parity=
      notRegister (L.one::b::ys)++(majority a b L.one c++[.X L.one]++
        Arithmetic.compareChain none xs ys (cs++[L.one]) c L.parity++[.X L.one]++eraseCarry a b L.one c)++
      notRegister (L.one::b::ys) := rfl
  have ch := chain_false_counts xs ys cs L.one c L.parity (by simp at yl rl; omega) (by simp at yl cl; omega)
  rw [eOld]
  simp only [Q6LifetimeResearch.compare,Q6LifetimeResearch.move]
  rw [eY,eR,eC,eT]
  refine ⟨?_,?_,?_⟩ <;>
  simp only [List.getD_cons_zero,List.drop_succ_cons,List.drop_zero,
    toffoliCount_append,measurementCount_append,gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,rename_gateSlots,(maj_c _ _ _ _).1,(maj_c _ _ _ _).2.1,(maj_c _ _ _ _).2.2,
    (ers_c _ _ _ _).1,(ers_c _ _ _ _).2.1,(ers_c _ _ _ _).2.2] <;>
  (try simp only [toffoliCount,measurementCount,gateSlots_cons,gateSlots_nil,instructionSlots]) <;>
  omega

theorem rawSub_counts760 (retired : Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (Q6LifetimeResearch.rawSubTail retired L)=toffoliCount (Q6Structural.rawSub L) ∧
    measurementCount (Q6LifetimeResearch.rawSubTail retired L)=measurementCount (Q6Structural.rawSub L) ∧
    gateSlots (Q6LifetimeResearch.rawSubTail retired L)=gateSlots (Q6Structural.rawSub L)+5 := by
  have eOld : Q6Structural.rawSub L=signComplement L.sign L.y++
      (notRegister (BalancedCircuit.rawTarget L)++
        TopCarry.addInPlaceTop (GuardCompression.source L) (BalancedCircuit.rawTarget L)
          ((Q6Structural.q6Carry L).take 255++[L.parity]) L.sign++
        notRegister (BalancedCircuit.rawTarget L))++
      signComplement L.sign L.y := rfl
  have w := BalancedCleanup.widths L.toLayout hw
  have cl : ((Q6Structural.q6Carry L).take 255).length=255 := by
    have len : (Q6Structural.q6Carry L).length=256 := (Q6StructuralCell.carry_widths L hw).2.2
    simp [List.length_take,len]
  have sl : (GuardCompression.source L).length=257 := by
    simp [GuardCompression.source,w.2.2.1]
  have tl : (BalancedCircuit.rawTarget L).length=257 := by
    simp [BalancedCircuit.rawTarget,w.2.1]
  obtain ⟨a,xs,eS⟩ := lists_cons (xs:=GuardCompression.source L) (by intro h; rw [h] at sl; simp at sl)
  rw [eS] at sl
  obtain ⟨a',as,eX⟩ := lists_cons (xs:=xs) (by intro h; rw [h] at sl; simp at sl)
  subst eX
  obtain ⟨b,ys,eT⟩ := lists_cons (xs:=BalancedCircuit.rawTarget L) (by intro h; rw [h] at tl; simp at tl)
  rw [eT] at tl
  obtain ⟨b',bs,eY⟩ := lists_cons (xs:=ys) (by intro h; rw [h] at tl; simp at tl)
  subst eY
  obtain ⟨c,cs,eC⟩ := lists_cons (xs:=(Q6Structural.q6Carry L).take 255) (by intro h; rw [h] at cl; simp at cl)
  rw [eC] at cl
  have asne : as≠[] := by intro h; rw [h] at sl; simp at sl
  have eA : TopCarry.addInPlaceTop (a::a'::as) (b::b'::bs) ((c::cs)++[L.parity]) L.sign=
      majority a b L.sign c++TopCarry.addInPlaceTop (a'::as) (b'::bs) (cs++[L.parity]) c++
        eraseCarry a b L.sign c++[.CX a b,.CX L.sign b] := by
    simp [TopCarry.addInPlaceTop,asne]
  have ad := addTop_counts760 (a'::as) (b'::bs) cs L.parity c (by simp at sl tl ⊢; omega)
    (by simp at sl cl ⊢; omega)
  rw [eOld]
  simp only [Q6LifetimeResearch.rawSubTail,Q6LifetimeResearch.move]
  rw [eS,eT,eC,eA]
  refine ⟨?_,?_,?_⟩ <;>
  simp only [List.getD_cons_zero,List.drop_succ_cons,List.drop_zero,
    toffoliCount_append,measurementCount_append,gateSlots_append,(renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2,rename_gateSlots,(maj_c _ _ _ _).1,(maj_c _ _ _ _).2.1,(maj_c _ _ _ _).2.2,
    (ers_c _ _ _ _).1,(ers_c _ _ _ _).2.1,(ers_c _ _ _ _).2.2] <;>
  (try simp only [toffoliCount,measurementCount,gateSlots_cons,gateSlots_nil,instructionSlots]) <;>
  omega

theorem forward_counts760 (retired : Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (Q6LifetimeResearch.forward retired false L)=toffoliCount (Q6StructuralCell.forward L) ∧
    measurementCount (Q6LifetimeResearch.forward retired false L)=
      measurementCount (Q6StructuralCell.forward L) ∧
    gateSlots (Q6LifetimeResearch.forward retired false L)=gateSlots (Q6StructuralCell.forward L)+6 := by
  have ra := rawAdd_counts760 retired L hw
  have fo := fold_counts760 retired L
  have cm := compare_true_counts760 retired L hw
  have un := unnormalize_counts760 retired L
  refine ⟨?_,?_,?_⟩ <;>
  simp only [Q6LifetimeResearch.forward,Q6StructuralCell.forward,Q6StructuralCell.forwardPrefix,
    OneReuse.remainder,Q6StructuralCell.cleanup,FifthCarry2.cleanupRest,
    toffoliCount_append,measurementCount_append,gateSlots_append,toffoliCount_reverse,
    measurementCount_reverse,reverse_gateSlots] <;>
  omega

theorem inverse_counts760 (retired : Wire) (L : BalancedCircuit.Layout) (hw : L.Widths) :
    toffoliCount (Q6LifetimeResearch.inverse retired L)=toffoliCount (Q6StructuralCell.inverse L) ∧
    measurementCount (Q6LifetimeResearch.inverse retired L)+1=measurementCount (Q6StructuralCell.inverse L) ∧
    gateSlots (Q6LifetimeResearch.inverse retired L)=gateSlots (Q6StructuralCell.inverse L)+2 := by
  have no := normalize_counts760 retired L
  have cm := compare_false_counts760 retired L hw
  have uf := unfold_counts760 retired L
  have rs := rawSub_counts760 retired L hw
  refine ⟨?_,?_,?_⟩ <;>
  simp only [Q6LifetimeResearch.inverse,Q6StructuralCell.inverse,Q6StructuralCell.inversePrefix,
    Q6StructuralCell.recoverPrefix,CarryBorrow.recoverBefore,OneReuse.restoreRaw,
    toffoliCount_append,measurementCount_append,gateSlots_append,toffoliCount_reverse,
    measurementCount_reverse,reverse_gateSlots] <;>
  (try simp only [toffoliCount,measurementCount,gateSlots_cons,gateSlots_nil,instructionSlots]) <;>
  omega

/-- The lifetime half against the old generic half, for every retired wire and port map. -/
theorem lifetime_half_counts760 (retired : Wire) (divide : Bool) (w : Nat → Wire) (sign : Wire) :
    toffoliCount (Q6LifetimeResearch.half retired divide w sign)=toffoliCount (Q6EndpointCell.half divide w sign) ∧
    measurementCount (Q6LifetimeResearch.half retired divide w sign)+(if divide then 0 else 1)=
      measurementCount (Q6EndpointCell.half divide w sign) ∧
    gateSlots (Q6LifetimeResearch.half retired divide w sign)=
      gateSlots (Q6EndpointCell.half divide w sign)+(if divide then 6 else 2) := by
  have hw := Q6EndpointCell.ports_widths w sign
  have eOld : Q6EndpointCell.half divide w sign=[.X sign]++(if divide then
      Q6StructuralCell.forward (Q6EndpointCell.ports w sign)
      else Q6StructuralCell.inverse (Q6EndpointCell.ports w sign))++[.X sign] := rfl
  have eNew : Q6LifetimeResearch.half retired divide w sign=[.X sign]++(if divide then
      Q6LifetimeResearch.forward retired false (Q6EndpointCell.ports w sign)
      else Q6LifetimeResearch.inverse retired (Q6EndpointCell.ports w sign))++[.X sign] := rfl
  rw [eOld,eNew]
  cases divide
  · have k := inverse_counts760 retired (Q6EndpointCell.ports w sign) hw
    simp only [Bool.false_eq_true,if_false,toffoliCount_append,measurementCount_append,gateSlots_append]
    omega
  · have k := forward_counts760 retired (Q6EndpointCell.ports w sign) hw
    simp only [if_true,toffoliCount_append,measurementCount_append,gateSlots_append]
    omega

end ECDSAAdd.Entrant.R2Life760
end

-- ===== R2Life760: the delivered interface =====
section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace ECDSAAdd.Entrant.R2Life760
open Arithmetic MappedCompressed DirectSkywalk Secp256k1 BalancedField Challenge Baselines
-- Never let elaboration unfold the two 13.6K-instruction programs or their wire sets.
attribute [local irreducible] Q6LifetimeResearch.half Q6EndpointCell.half

/-- GordoAR's lifetime half with retired carry `base 760`; the inverse direction is followed by
one empty-correction erasure of the clean `one` flag `base 1027` (record/count alignment). -/
def half760 (divide : Bool) : Program :=
  Q6LifetimeResearch.half (base 760) divide base (base 2409)++
    (if divide then [] else [.measureX (base 1027) [] []])

theorem half760_true : half760 true=Q6LifetimeResearch.half (base 760) true base (base 2409) := by
  rw [half760,if_pos rfl,List.append_nil]

theorem half760_false : half760 false=
    Q6LifetimeResearch.half (base 760) false base (base 2409)++[.measureX (base 1027) [] []] := rfl

/-- An empty-correction erasure of a clean wire is the identity, for every record. -/
theorem pad_run (c : Wire) (m : List Bool) (t : State) (h : t.basis c=false) :
    run [Instr.measureX c [] []] m t=t := by
  obtain ⟨ph,bs⟩ := t
  simp only at h
  have e : writeBit bs c false=bs := by
    funext q
    by_cases hq : q=c
    · subst hq; simp [writeBit,h]
    · simp [writeBit,Function.update,hq]
  simp only [run,measureAndCorrect,h,Bool.and_false,Bool.xor_false,e]
  cases m.headD false <;> rfl

theorem member760 : base 760∈((Q6EndpointCell.ports base (base 2409)).carry.take 254).drop 1 := by
  decide +kernel

theorem one_work760 : base 1027∈BalancedCircuit.work (Q6EndpointCell.ports base (base 2409)) := by
  simp [BalancedCircuit.work,Q6EndpointCell.ports]

theorem half760_run_eq (divide : Bool)
    (hn : (Q6EndpointCell.ports base (base 2409)).wires.Nodup)
    (origin : BasisState) (clean : Q6EndpointCell.Clean base origin) (X Y : Fp)
    (s : State) (m n : List Bool)
    (input : PairFrame (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y
      origin (centerWord X) (centerWord Y) s.basis) :
    run (half760 divide) m s=run (Q6EndpointCell.half divide base (base 2409)) n s := by
  have core (r : List Bool) := Q6LifetimeProof.half_run_eq (base 760) divide base (base 2409) hn
    member760 origin clean X Y s r n input
  cases divide
  · rw [half760_false,run_append,core]
    apply pad_run
    have frame := (Q6EndpointCell.half_frame false base (base 2409) hn origin clean X Y s n input).2
    have away := OwnQ6Core5.work_away (Q6EndpointCell.ports base (base 2409)) hn (base 1027) one_work760
    exact (frame.2.2 _ away.1 away.2).trans
      (Q6EndpointCell.clean_work base (base 2409) origin clean _ one_work760)
  · rw [half760_true]
    exact core m

theorem half760_frame (divide : Bool)
    (hn : (Q6EndpointCell.ports base (base 2409)).wires.Nodup)
    (origin : BasisState) (hc : Q6EndpointCell.Clean base origin) (X Y : Fp) :
    Triple (PairFrame (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y
      origin (centerWord X) (centerWord Y)) (half760 divide)
      (PairFrame (Q6EndpointCell.ports base (base 2409)).r (Q6EndpointCell.ports base (base 2409)).y origin
        (centerWord (if divide then (X+(if origin (base 2409) then Y else -Y))/2
          else 2*X+(if origin (base 2409) then -Y else Y))) (centerWord Y)) := by
  intro s m input
  rw [half760_run_eq divide hn origin hc X Y s m m input]
  exact Q6EndpointCell.half_frame divide base (base 2409) hn origin hc X Y s m input

/-! ### Counts and slots -/

private theorem pad_counts : toffoliCount [Instr.measureX (base 1027) [] []]=0 ∧
    measurementCount [Instr.measureX (base 1027) [] []]=1 ∧
    gateSlots [Instr.measureX (base 1027) [] []]=1 := ⟨rfl,rfl,rfl⟩

theorem half760_counts (divide : Bool) :
    toffoliCount (half760 divide)=toffoliCount (Q6EndpointCell.half divide base (base 2409)) ∧
    measurementCount (half760 divide)=measurementCount (Q6EndpointCell.half divide base (base 2409)) := by
  have k := lifetime_half_counts760 (base 760) divide base (base 2409)
  cases divide
  · rw [half760_false,toffoliCount_append,measurementCount_append,pad_counts.1,pad_counts.2.1]
    simp only [Bool.false_eq_true,if_false] at k
    exact ⟨by omega,by omega⟩
  · rw [half760_true]
    simp only [if_true] at k
    exact ⟨by omega,by omega⟩

theorem half760_slots (divide : Bool) :
    gateSlots (half760 divide)=gateSlots (Q6EndpointCell.half divide base (base 2409))+
      (if divide then 6 else 3) := by
  have k := (lifetime_half_counts760 (base 760) divide base (base 2409)).2.2
  cases divide
  · rw [half760_false,gateSlots_append,pad_counts.2.2,if_neg (by decide)]
    simp only [Bool.false_eq_true,if_false] at k
    omega
  · rw [half760_true,if_pos rfl]
    simp only [if_true] at k
    omega

/-! ### Support and physicality -/

private theorem retired760 : (760:Nat)=719∨(760:Nat)=720∨(760:Nat)=760 := Or.inr (Or.inr rfl)

theorem half760_support (divide : Bool) :
    wires (half760 divide)⊆(wires (Q6EndpointCell.half divide base (base 2409))).erase (base 760) := by
  intro q hq
  have core (hq : q∈wires (Q6LifetimeResearch.half (base 760) divide base (base 2409))) :
      q∈(wires (Q6EndpointCell.half divide base (base 2409))).erase (base 760) := by
    refine Finset.mem_erase.mpr ⟨?_,Q6LifetimeResearch.half_support_old 760 retired760 divide hq⟩
    rintro rfl
    exact Q6LifetimeResearch.half_retired_free 760 retired760 divide hq
  cases divide
  · rw [half760_false,wires_append,Finset.mem_union] at hq
    rcases hq with hq|hq
    · exact core hq
    · have e : q=base 1027 := by simpa [wires,Instr.wires,correctionWires] using hq
      subst e
      exact Finset.mem_erase.mpr ⟨by decide,Q6LifetimeResearch.one_mem_old_half760 false⟩
  · rw [half760_true] at hq
    exact core hq

theorem half760_physical (divide : Bool) : GatePhysical (half760 divide) := by
  have core := Q6LifetimeResearch.half_physical 760 retired760 divide
  cases divide
  · rw [half760_false,gatePhysical_append]
    refine ⟨core,?_⟩
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    subst hi
    trivial
  · rw [half760_true]
    exact core

theorem half760_free (divide : Bool) : base 760∉wires (half760 divide) := fun used =>
  (Finset.mem_erase.mp (half760_support divide used)).1 rfl

end ECDSAAdd.Entrant.R2Life760
end

#print axioms ECDSAAdd.Entrant.R2Life760.half760_run_eq
#print axioms ECDSAAdd.Entrant.R2Life760.half760_frame
#print axioms ECDSAAdd.Entrant.R2Life760.half760_counts
#print axioms ECDSAAdd.Entrant.R2Life760.half760_slots
#print axioms ECDSAAdd.Entrant.R2Life760.half760_support
#print axioms ECDSAAdd.Entrant.R2Life760.half760_physical
#print axioms ECDSAAdd.Entrant.R2Life760.half760_free

-- Seal the program for downstream modules (MainB/MainC use only the interface above).
attribute [irreducible] ECDSAAdd.Entrant.R2Life760.half760
