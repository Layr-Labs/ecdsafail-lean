import ECDSAAdd.Submission.Entrant.FrontierEntry1591Endpoints
import ECDSAAdd.Submission.Entrant.FrontierEntry1591KernelCompose

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.FrontierEntry1591EntryFrame
open Arithmetic Secp256k1 MappedCompressed CompressedAllocation CompressedFieldSupport BalancedField
  NewHistory5 EntryFuse
attribute [local irreducible] run wires NewHistory5.allEncode

theorem encoded_retarget (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s t : State) (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (input : NewHistory5.EncodedCanonicalFrame5 origin Y 0 s) :
    NewHistory5.EncodedFieldFrame5 base (base 2409) origin (Y/2) 0 t := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  let R := (balancedSharedPorts base (base 2409)).r
  let W := (balancedSharedPorts base (base 2409)).y
  have rEq : R=wireBlock base 2056 256 := balancedSharedPorts_r base (base 2409)
  have wEq : W=wireBlock base 770 256 := balancedSharedPorts_y base (base 2409)
  have split : (skywalkSharedField base).z=R++[base 2312] ∧
      (skywalkSharedField base).a=W++[base 1026] := by
    rw [skywalkShared_field_z,rEq,wEq]
    constructor
    · have h := wireBlock_append base 2056 256 1
      simpa only [show wireBlock base 2312 1=[base 2312] from rfl,Nat.reduceAdd] using h.symm
    · have h := wireBlock_append base 770 256 1
      simpa only [show wireBlock base 1026 1=[base 1026] from rfl,Nat.reduceAdd] using h.symm
  obtain ⟨raw,rawPhase,rawFrame,encoded⟩ := input
  rw [split.1,split.2,ZMod.val_zero] at rawFrame
  have yBound : Y.val<2^256 := (ZMod.val_lt Y).trans (by norm_num [p])
  have narrow := balancedPair_narrow R W (base 2312) (base 1026) origin raw.basis Y.val 0
    (by rw [rEq,wireBlock_length]; exact yBound) (by rw [wEq,wireBlock_length]; norm_num)
    rawFrame hr hy
  have dis : R.Disjoint W :=
    (List.nodup_append'.mp (balancedSharedLayout_pairND base (base 2409) hn)).2.2
  let raw' : State := ⟨t.phase,fun q => if q∈R then t.basis q else raw.basis q⟩
  have keeps (q : Wire) (hq : q∉R) : raw'.basis q=raw.basis q := by simp [raw',hq]
  have target : regValue R raw'.basis=centerWord (Y/2) := by
    have h : regValue R raw'.basis=regValue R t.basis := by
      apply regValue_congr
      intro q hq
      simp [raw',hq]
    rw [h,rEq]
    exact value
  have pf : PairFrame R W origin (centerWord (Y/2)) (centerWord 0) raw'.basis := by
    rw [NewHalfField5.centerWord_zero]
    exact PairFrame.update_temp R W origin raw.basis raw'.basis Y.val 0 _ dis narrow keeps target
  have rawPhase' : raw'.phase=raw.phase := by
    change t.phase=raw.phase
    exact phase.trans rawPhase.symm
  have support := NewHalfField5.encoder_pool_support
  have away (q : Wire) (hq : q∈wires (NewHistory5.allEncode base 102)) : q∉R := by
    rw [rEq]
    exact pool_away q (List.mem_toFinset.mp (support hq))
  have reads : ∀q∈wires (NewHistory5.allEncode base 102),raw'.basis q=raw.basis q := by
    intro q hq
    exact keeps q (away q hq)
  have inc := run_local_increment (NewHistory5.allEncode base 102) raw' raw [] reads
  have eqphase : (run (NewHistory5.allEncode base 102) [] raw').phase =
      (run (NewHistory5.allEncode base 102) [] raw).phase := by
    rw [rawPhase'] at inc
    cases raw.phase <;> simpa using inc.1
  have encoded' : t=run (NewHistory5.allEncode base 102) [] raw' := by
    apply State.extensionality
    · rw [eqphase,←encoded]
      exact phase
    · funext q
      by_cases hq : q∈R
      · have unused : q∉wires (NewHistory5.allEncode base 102) := fun h => away q h hq
        rw [run_preserves_outside _ [] raw' q unused]
        simp [raw',hq]
      · have eq : (run (NewHistory5.allEncode base 102) [] raw').basis q=
            (run (NewHistory5.allEncode base 102) [] raw).basis q := by
          by_cases used : q∈wires (NewHistory5.allEncode base 102)
          · exact inc.2 q used
          · rw [run_preserves_outside _ [] raw' q used,run_preserves_outside _ [] raw q used]
            exact keeps q hq
        rw [eq,←encoded]
        apply same q
        simpa only [rEq] using hq
  exact ⟨raw',rfl,pf,encoded'⟩


theorem canonical_to_field (hn : (skywalkSharedWires base).Nodup)
    (origin : BasisState) (hr : origin (base 2312)=false) (hy : origin (base 1026)=false)
    (Y : Fp) (s t : State) (phase : t.phase=s.phase)
    (same : ∀q,q∉wireBlock base 2056 256 → t.basis q=s.basis q)
    (value : regValue (wireBlock base 2056 256) t.basis=centerWord (Y/2))
    (input : NewFieldFrameOB5.EncodedCanonicalFrame origin Y 0 s) :
    NewFieldFrameOB5.EncodedFieldFrame origin (Y/2) 0 t := by
  apply encoded_retarget hn origin hr hy Y (pullState (OB5.sig 511) s)
    (pullState (OB5.sig 511) t) phase
  · intro q hq
    exact same _ (EntryFuse.sig_num_away q hq)
  · apply (regValue_congr _ _ _ ?_).trans value
    intro q hq
    change t.basis (OB5.sig 511 q)=t.basis q
    rw [EntryFuse.sig_num_fix q hq]
  · exact input

end ECDSAAdd.Entrant.FrontierEntry1591EntryFrame
