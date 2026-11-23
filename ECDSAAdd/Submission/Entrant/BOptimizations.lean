import ECDSAAdd.Framework.MeasuredLocality
import ECDSAAdd.Framework.WireRename
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
import ECDSAAdd.Baselines.SlotMapped
import ECDSAAdd.Arithmetic.PairFrameUnique
import ECDSAAdd.Arithmetic.KnownOutputAdderPhysical
import ECDSAAdd.Arithmetic.NarrowSignedRecord
import ECDSAAdd.Arithmetic.Compare
import ECDSAAdd.Arithmetic.ExactBorrowErase
import ECDSAAdd.Arithmetic.MeasuredCanonicalMod
import ECDSAAdd.Arithmetic.DisjointPrograms
import ECDSAAdd.Challenge.Contract
import Mathlib.Tactic.FinCases
import ECDSAAdd.Arithmetic.CuccaroStreamedSquareProof
import ECDSAAdd.Submission.Entrant.BOptimizationsCore
import ECDSAAdd.Framework.Cost
import ECDSAAdd.Framework.PacketSequenceFrame
import ECDSAAdd.Arithmetic.MappedCompressedAllocationSites
import ECDSAAdd.Arithmetic.SignedWordBits
import ECDSAAdd.Arithmetic.SignedHalf
import ECDSAAdd.Arithmetic.BalancedCoreLayoutProof
import ECDSAAdd.Arithmetic.SignedWord
import ECDSAAdd.Math.SkywalkTerminationBudget
import ECDSAAdd.Math.SkywalkTrace
import ECDSAAdd.Arithmetic.RecordedRailRippleCertificate
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Arithmetic.SwapRegisters
import ECDSAAdd.Arithmetic.RecordedRailVentedProof
import ECDSAAdd.Framework.WireRenameEquivalence
import ECDSAAdd.Framework.WireRenameComposition
import ECDSAAdd.Submission.Entrant.StairSideA0

-- Rebalanced closed source chunks; all ordinary declarations and circuit literals retained.
section

-- Verified ABC18 optimization component C105CacheFrames
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop MixedLiteralAdderDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem sub_frame(s:State)(m:List Bool)(H:Nat)(hH:H<2^130)
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hosts.map s.basis=ReorderedCacheBits.values 4 105 H (976*H/1024)):
 run HighConsumedC105Research.sub m s=
 scatterState hosts (List.replicate hosts.length false) (run rawI m s):=by
 have fast:=HighConsumedC105Research.sub_run_eq s raw_nd geometry.1 geometry.2.1 geometry.2.2
  hz hi H hH source target saved m
 rw [fast]
 exact ReorderedConsumedSub.frame 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
  raw_nd geometry.1 geometry.2.1 geometry.2.2 s m hz hi H (976*H/1024) source target saved

theorem inverse_frame(s:State)(m:List Bool)(H:Nat)(hH:H<2^130)
 (hz:∀q∈cs,(run preInv m s).basis q=false)(hi:(run preInv m s).basis cin=false)
 (source:regValue xs (run preInv m s).basis=H)
 (target:regValue ys (run preInv m s).basis=976*H/1024)
 (saved:hosts.map s.basis=ReorderedCacheBits.values 4 105 H (976*H/1024)):
 run newI m s=scatterState hosts (List.replicate hosts.length false) (run I m s):=by
 have same:hosts.map (run preInv m s).basis=hosts.map s.basis:=
  by
   apply List.map_congr_left
   intro q hq
   exact run_preserves_outside preInv m s q (preInv_off q hq)
 simp only [newI,I,ControlledBorrowResearch.run_cat]
 exact sub_frame (run preInv m s) _ H hH hz hi source target (same.trans saved)

theorem forward_frame(s:State)(m:List Bool)(H:Nat)
 (zero:∀q∈hosts,(run (head++C105LowEraseResearch.clear) (m.take (measurementCount (head++C105LowEraseResearch.clear))) s).basis q=false)
 (values:(((cs.drop 4).take 105).map (run (carryPrefix (4+105) xs ys cs cin) []
  (run (head++C105LowEraseResearch.clear) (m.take (measurementCount (head++C105LowEraseResearch.clear))) s)).basis)=
   ReorderedCacheBits.values 4 105 H (976*H/1024)):
 run newF m s=scatterState hosts (ReorderedCacheBits.values 4 105 H (976*H/1024)) (run F m s):=by
 have h:=CacheBetweenFrameResearch.forward (head++C105LowEraseResearch.clear) top 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  geometry.1 (fun q hq bad=>geometry.2.2 q hq (by simp only [List.mem_cons,List.mem_append];tauto))
  rawF_off top_off s m zero
 rw [values] at h
 exact h

theorem forward_measurements:measurementCount newF=measurementCount F:=by
 have h:=(ReorderedGenericCache.count_balance 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)).2.1
 simp only [newF,F,rawF,measurementCount_append]
 rw [h]


end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105ForwardErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem low_copies(H:Nat)(s:State)(ready:WReady acc pad bank cin src H s):
 s.basis 4505=s.basis 4243 ∧ s.basis 4506=s.basis 4244 ∧ s.basis 4507=(s.basis 4245 ^^ s.basis 4243):=by
 have cp:=LowWordRecovery.copies acc src s.basis (by rw [acc_length];decide)
  (by rw [source_length];decide) (by rw [ready.2.1];exact ready.1)
 have c4:s.basis 4505=s.basis 4243:=by
  simpa only [show src.getD 0 0=4243 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.1.symm
 have c5:s.basis 4506=s.basis 4244:=by
  simpa only [show src.getD 1 0=4244 from by decide +kernel,
   show acc.getD 5 0=4506 from by decide +kernel] using cp.2.1.symm
 refine ⟨c4,c5,?_⟩
 have c6:s.basis 4245=(s.basis 4507 ^^ s.basis 4505):=by
  simpa only [show src.getD 2 0=4245 from by decide +kernel,
   show acc.getD 6 0=4507 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.2.2
 rw [c6,←c4]
 simp [Bool.xor_assoc]

theorem plain_split:ReorderedCPlain.build acc pad bank cin src=head++(rawF++top):=by
 simpa only [head,rawF,top,List.append_assoc] using
  ReorderedCBuild.plain_split acc pad bank cin src source_length

theorem rest_off(q:Wire)(hq:q∈C105LowEraseResearch.low):q∉wires (rawF++top):=by
 simp only [wires_append,Finset.mem_union,not_or]
 exact ⟨rawF_off q (low_hosts q hq),top_off q (low_hosts q hq)⟩

theorem head_copies(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 (run head m s).basis 4505=(run head m s).basis 4243 ∧
 (run head m s).basis 4506=(run head m s).basis 4244 ∧
 (run head m s).basis 4507=((run head m s).basis 4245 ^^ (run head m s).basis 4243):=by
 let u:=run (ReorderedCPlain.build acc pad bank cin src) m s
 have ready:WReady acc pad bank cin src (regValue src s.basis) u:=
  Ghost3CacheC.plain_ready s m hz hb hi ha
 have cp:=low_copies _ u ready
 have low(q:Wire)(hq:q∈C105LowEraseResearch.low):u.basis q=(run head m s).basis q:=by
  dsimp [u]
  rw [plain_split,run_cat]
  exact run_preserves_outside _ _ _ q (rest_off q hq)
 have frame:=ReorderedCHead.head_triple acc pad bank cin src acc_length (by have h:=source_length;omega)
  fits s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have away:∀q∈src,q∉acc:=by decide +kernel
 have source(q:Wire)(hq:q∈src):u.basis q=(run head m s).basis q:=by
  have h:= (regValue_eq_iff src _ _).mp ready.2.1 q hq
  exact h.trans (frame.2.2 q (away q hq)).symm
 rw [low 4505 (by decide),low 4506 (by decide),low 4507 (by decide),source 4243 (by decide +kernel),source 4244 (by decide +kernel),source 4245 (by decide +kernel)] at cp
 exact cp

theorem forward_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 run F m s=C105LowEraseResearch.erase (run (ReorderedCPlain.build acc pad bank cin src) m s):=by
 have cp:=head_copies s m hz hb hi ha
 have eq:=C105LowEraseResearch.forward_erased head (rawF++top) s m rest_off cp.1 cp.2.1 cp.2.2
 simpa only [F,plain_split,List.append_assoc] using eq

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105ForwardClean
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem forward_zero(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false):
 ∀q∈hosts,(run F m s).basis q=false:=by
 rw [forward_erased s m hz hb hi ha]
 let u:=run (ReorderedCPlain.build acc pad bank cin src) m s
 have ready:WReady acc pad bank cin src (regValue src s.basis) u:=
  Ghost3CacheC.plain_ready s m hz hb hi ha
 intro q hq
 rcases List.mem_append.mp hq with hq|hq
 · rw [C105LowEraseResearch.bit_same _ q (by
    have away:=old_away q hq
    intro bad
    apply away
    simp only [C105LowEraseResearch.low,List.mem_cons,List.not_mem_nil,or_false] at bad
    rcases bad with rfl|rfl|rfl <;>decide)]
   exact (run_preserves_outside _ m s q (ReorderedCFixed.off_plain q hq).1).trans (zero q hq)
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 0 (by decide)
      (by rw [acc_length];decide) ready.1
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 1 (by decide)
      (by rw [acc_length];decide) ready.1
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 2 (by decide)
      (by rw [acc_length];decide) ready.1
   · exact C105LowEraseResearch.zero _ _ (by decide)
   · exact C105LowEraseResearch.zero _ _ (by decide)
   · exact C105LowEraseResearch.zero _ _ (by decide)

theorem prefix_zero(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false):
 ∀q∈hosts,(run (head++C105LowEraseResearch.clear) m s).basis q=false:=by
 have clean:=forward_zero s m hz hb hi ha zero
 intro q hq
 have off:q∉wires (rawF++top):=by
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨rawF_off q hq,top_off q hq⟩
 have eq:(run F m s).basis q=(run (head++C105LowEraseResearch.clear) m s).basis q:=by
  have partition:F=(head++C105LowEraseResearch.clear)++(rawF++top):=by simp only [F,List.append_assoc]
  rw [partition,run_cat]
  exact run_preserves_outside _ _ _ q off
 exact eq.symm.trans (clean q hq)

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CHeadArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CHeadArithmeticResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem ready(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=0):
 let t:=run (ReorderedCHead.head acc Z bank cin src) m s
 (∀q∈bank.take 129,t.basis q=false) ∧ t.basis cin=false ∧
 regValue src t.basis=regValue src s.basis ∧
 regValue ((acc.take 140).drop 10) t.basis=((2^140-48*regValue src s.basis)%2^140)/1024:=by
 let H:=regValue src s.basis
 let t:=run (ReorderedCHead.head acc Z bank cin src) m s
 have frame:=ReorderedCHead.head_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have hf10:=hf _ (A161NarrowAcc.terms_mem src).2.1
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;>omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=frame.2.2 q (away q hq)
 have len:(acc.take 140).length=140:=by simp [hacc]
 have pref:=regValue_take_drop_of_lt acc 140 ((2^140-48*H)%2^140) t.basis
  (by omega) frame.2.1 (Nat.mod_lt _ (by positivity))
 refine ⟨?_,?_,?_,?_⟩
 · intro q hq
   exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 · exact (same cin (Or.inr rfl)).trans hi
 · exact regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 · rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
   rfl

end ECDSAAdd.Entrant.CHeadArithmeticResearch

end

-- Verified ABC18 optimization component C105ForwardValues
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem x_in(q:Wire)(hq:q∈xs):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_left cs (List.mem_append_left ys hq))
theorem y_in(q:Wire)(hq:q∈ys):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_left cs (List.mem_append_right xs hq))
theorem c_in(q:Wire)(hq:q∈cs):q∈domain:=
 List.mem_cons_of_mem cin (List.mem_append_right (xs++ys) hq)
theorem cin_in:cin∈domain:=List.mem_cons_self

theorem domain_away_low(q:Wire)(hq:q∈domain):q∉C105LowEraseResearch.low:=by
 intro bad
 exact geometry.2.2 q (low_hosts q bad) hq

theorem prefix_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 run (head++C105LowEraseResearch.clear) m s=C105LowEraseResearch.erase (run head m s):=by
 rw [run_cat]
 have cp:=head_copies s m hz hb hi ha
 exact C105LowEraseResearch.clear_eq_erase _ _ cp.1 cp.2.1 cp.2.2

theorem forward_values(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 (((cs.drop 4).take 105).map (run (carryPrefix (4+105) xs ys cs cin) []
  (run (head++C105LowEraseResearch.clear) m s)).basis)=
 ReorderedCacheBits.values 4 105 (regValue src s.basis) (976*regValue src s.basis/1024):=by
 let H:=regValue src s.basis
 let u:=run head m s
 let t:=run (head++C105LowEraseResearch.clear) m s
 have te:t=C105LowEraseResearch.erase u:=prefix_erased s m hz hb hi ha
 have hH:H<2^130:=by simpa only [H,source_length] using regValue_lt src s.basis
 have ready:(∀q∈cs,u.basis q=false) ∧ u.basis cin=false ∧ regValue xs u.basis=H ∧
  regValue ys u.basis=((2^140-48*H)%2^140)/1024:=by
  simpa only [cs,xs,ys,u,head,H] using
   CHeadArithmeticResearch.ready acc pad bank cin src acc_length source_length fits s m hz hb hi ha
 have eraseBit(q:Wire)(hq:q∈domain):t.basis q=u.basis q:=by
  rw [te]
  exact C105LowEraseResearch.bit_same _ q (domain_away_low q hq)
 have eraseReg(r:List Wire)(sub:∀q∈r,q∈domain):regValue r t.basis=regValue r u.basis:=
  regValue_congr _ _ _ (fun q hq=>eraseBit q (sub q hq))
 have sy:regValue ys t.basis=((2^140-48*H)%2^140)/1024:=
  (eraseReg ys y_in).trans ready.2.2.2
 have sh:regValue xs t.basis=H:=
  (eraseReg xs x_in).trans ready.2.2.1
 have sb:∀q∈cs,t.basis q=false:=by
  intro q hq
  exact (eraseBit q (c_in q hq)).trans (ready.1 q hq)
 have si:t.basis cin=false:=
  (eraseBit cin cin_in).trans ready.2.1
 exact ReorderedCacheBits.forward_values 4 105 H (((2^140-48*H)%2^140)/1024) (976*H/1024)
  xs ys cs cin t (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide) raw_nd sb si sh sy (fun j hj=>by
   simpa only [show 130+10=140 by decide] using
    ReorderedCacheArithmetic.high_add_low 130 (4+j+1) H (by omega) hH)

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CPreInverseArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CPreInverseArithmeticResearch
open InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem ready(acc Z bank:List Wire)(cin:Wire)(src:List Wire)
 (hacc:acc.length=163)(hsrc:src.length=130)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State)(m:List Bool)(hz:∀q∈Z,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis cin=false)(ha:regValue acc s.basis=4294968272*regValue src s.basis):
 let t:=run (C163Carry.unbuildPre acc Z bank cin src) m s
 (∀q∈bank.take 129,t.basis q=false) ∧ t.basis cin=false ∧
 regValue src t.basis=regValue src s.basis ∧
 regValue ((acc.take 140).drop 10) t.basis=976*regValue src s.basis/1024:=by
 let H:=regValue src s.basis
 let t:=run (C163Carry.unbuildPre acc Z bank cin src) m s
 have frame:=C163Carry.unbuildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have hf10:=hf _ (A161NarrowAcc.terms_mem src).2.1
 have away(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):q∉acc:=by
  intro bad
  have h:=List.nodup_iff_count_le_one.mp hf10.nd q
  have a:=List.count_pos_iff.mpr bad
  rcases hq with hq|rfl
  · have b:=List.count_pos_iff.mpr hq
    simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
    split at h <;>omega
  · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
    omega
 have same(q:Wire)(hq:q∈src++Z++bank ∨ q=cin):t.basis q=s.basis q:=frame.2.2 q (away q hq)
 have len:(acc.take 140).length=140:=by simp [hacc]
 have hH:H<2^130:=by simpa only [H,hsrc] using regValue_lt src s.basis
 have pref:=regValue_take_drop_of_lt acc 140 (976*H) t.basis
  (by omega) frame.2.1 (by norm_num at hH ⊢;omega)
 refine ⟨?_,?_,?_,?_⟩
 · intro q hq
   exact (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
 · exact (same cin (Or.inr rfl)).trans hi
 · exact regValue_congr _ _ _ (fun q hq=>same q (Or.inl (by simp [hq])))
 · rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
   rfl

end ECDSAAdd.Entrant.CPreInverseArithmeticResearch

end

-- Verified ABC18 optimization component C105InverseReady
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem pre_raw_ready(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 (∀q∈cs,(run preInv m s).basis q=false) ∧ (run preInv m s).basis cin=false ∧
 regValue xs (run preInv m s).basis=H ∧ regValue ys (run preInv m s).basis=976*H/1024:=by
 have h:=CPreInverseArithmeticResearch.ready acc pad bank cin src acc_length source_length fits s m
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 (by rw [ready.2.1];exact ready.1)
 simpa only [preInv,xs,ys,cs,ready.2.1] using h

theorem scattered_erased_domain(s:State)(vs:List Bool)(q:Wire)(hq:q∈domain):
 (scatterState hosts vs (C105LowEraseResearch.erase s)).basis q=s.basis q:=by
 rw [scatter_outside hosts vs _ q (by intro bad;exact geometry.2.2 q bad hq)]
 exact C105LowEraseResearch.bit_same s q (domain_away_low q hq)

theorem inverse_ready(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 let vs:=ReorderedCacheBits.values 4 105 H (976*H/1024)
 let t:=scatterState hosts vs (C105LowEraseResearch.erase s)
 run newI m t=scatterState hosts (List.replicate hosts.length false) (run I m t):=by
 dsimp only
 let vs:=ReorderedCacheBits.values 4 105 H (976*H/1024)
 let t:=scatterState hosts vs (C105LowEraseResearch.erase s)
 have hH:H<2^130:=by rw [←ready.2.1];simpa only [source_length] using regValue_lt src s.basis
 have commute:run preInv m t=scatterState hosts vs (C105LowEraseResearch.erase (run preInv m s)):=by
  rw [show t=scatterState hosts vs (C105LowEraseResearch.erase s) from rfl,
   run_scatter preInv hosts vs _ _ preInv_off,
   C105LowEraseResearch.commute preInv m s (fun q hq=>preInv_off q (low_hosts q hq))]
 have bits(q:Wire)(hq:q∈domain):(run preInv m t).basis q=(run preInv m s).basis q:=by
  rw [commute]
  exact scattered_erased_domain _ vs q hq
 have regs(r:List Wire)(sub:∀q∈r,q∈domain):regValue r (run preInv m t).basis=regValue r (run preInv m s).basis:=
  regValue_congr _ _ _ (fun q hq=>bits q (sub q hq))
 have rr:=pre_raw_ready H s m ready
 have saved:hosts.map t.basis=vs:=scatter_saved_map hosts vs _ geometry.1
  (by simp only [vs,ReorderedCacheBits.values,List.length_map,geometry.2.1,List.length_range])
 apply inverse_frame t m H hH
 · intro q hq
   rw [bits q (c_in q hq)]
   exact rr.1 q hq
 · rw [bits cin cin_in]
   exact rr.2.1
 · rw [regs xs x_in]
   exact rr.2.2.1
 · rw [regs ys y_in]
   exact rr.2.2.2
 · exact saved

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105MiddleErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev oldF:Program:=ReorderedCPlain.build acc pad bank cin src
abbrev oldM:Program:=KnownCMidStaged.body
abbrev M:Program:=CKAliasesResearch.program

theorem measurements:measurementCount F=measurementCount oldF:=by
 rw [oldF,plain_split]
 simp only [F,measurementCount_append,C105LowEraseResearch.counts.2.1,Nat.add_zero,Nat.zero_add,List.append_assoc]

theorem middle_erased(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 middleState F M s m=C105LowEraseResearch.erase (middleState oldF oldM s m):=by
 unfold middleState
 rw [measurements,CKAliasesResearch.counts.2.1,forward_erased s _ hz hb hi ha]
 exact C105LowEraseResearch.aliases_erased (regValue src s.basis) _ _
  (Ghost3CacheC.plain_ready s _ hz hb hi ha) after flag

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Restore
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem rawI_eq:rawI=Acc.op (acc.take 140) pad bank cin 140 true (Acc.earlyTerm src false 10):=by
 simp only [rawI,ReorderedConsumedSub.plain,Acc.op,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,
  source_length,Bool.false_eq_true,ite_false,Nat.sub_self,List.take_zero,List.append_nil,
  MixedLiteralAdderDevelop.read_add_eq,subInPlace]
 rfl

theorem I_source(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 ∀q∈src,(run I m s).basis q=s.basis q:=by
 have hH:regValue src s.basis<2^130:=by simpa only [source_length] using regValue_lt src s.basis
 have pre:=C163Carry.unbuildPre_triple acc pad bank cin src acc_length source_length fits s.basis
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2
 have sub:=ReorderedAcc.op_mod_prefix_triple acc pad bank cin 163 140 (Acc.earlyTerm src false 10)
  acc_length (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.1)
  (by simp only [Acc.earlyTerm,source_length];decide) (by norm_num [Acc.earlyTerm])
  s.basis ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 true (976*regValue src s.basis)
  (by norm_num at hH ⊢;omega)
 have frame:=(pre.seq sub) s m ⟨by rw [ready.2.1];exact ready.1,fun _ _=>rfl⟩
 have eq:I=C163Carry.unbuildPre acc pad bank cin src++Acc.op (acc.take 140) pad bank cin 140 true (Acc.earlyTerm src false 10):=by
  rw [I,rawI_eq];rfl
 have away:∀q∈src,q∉acc:=by decide +kernel
 intro q hq
 rw [eq]
 exact frame.2.2 q (away q hq)

theorem restored(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 run (I++C105LowEraseResearch.clear) m (C105LowEraseResearch.erase s)=run I m s:=by
 have cp:=low_copies H s ready
 have low(q:Wire)(hq:q∈C105LowEraseResearch.low):(run I m s).basis q=s.basis q:=
  run_preserves_outside I m s q (I_off q (low_hosts q hq))
 have source:=I_source H s m ready
 apply C105LowEraseResearch.suffix I s m (fun q hq=>I_off q (low_hosts q hq))
 · rw [low 4505 (by decide),source 4243 (by decide +kernel)]
   exact cp.1
 · rw [low 4506 (by decide),source 4244 (by decide +kernel)]
   exact cp.2.1
 · rw [low 4507 (by decide),source 4245 (by decide +kernel),source 4243 (by decide +kernel)]
   exact cp.2.2

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105UnbuildSplit
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev tail:Program:=ReorderedCUnbuild.after acc pad bank cin src

theorem unbuild_split:ReorderedCPlain.unbuild acc pad bank cin src=I++tail:=by
 simpa only [I,preInv,rawI,xs,ys,cs,tail] using ReorderedCUnbuild.plain_split acc pad bank cin src source_length

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105ErasedSuffix
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem erased_suffix(H:Nat)(u:State)(m:List Bool)(ready:WReady acc pad bank cin src H u):
 run (I++C105LowEraseResearch.clear++tail) m (C105LowEraseResearch.erase u)=run (I++tail) m u:=by
 exact ClearContextResearch.suffix I C105LowEraseResearch.clear tail C105LowEraseResearch.counts.2.1
  (C105LowEraseResearch.erase u) u m (restored H u m ready)


end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105PlainLoop
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem plain_loop(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run (F++M++(I++C105LowEraseResearch.clear++tail)) m s=
 run (oldF++oldM++ReorderedCPlain.unbuild acc pad bank cin src) m s:=by
 have eq:=middle_erased s m hz hb hi ha after flag
 apply ClearContextResearch.projected F M oldF oldM (I++C105LowEraseResearch.clear++tail)
  (ReorderedCPlain.unbuild acc pad bank cin src) C105LowEraseResearch.erase s m measurements
  CKAliasesResearch.counts.2.1 eq
 exact (erased_suffix _ _ _ after).trans
  (congrArg (fun P=>run P (m.drop (measurementCount oldF+measurementCount oldM))
   (middleState oldF oldM s m)) unbuild_split.symm)


end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105CacheLoop
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem cache_loop(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run (newF++M++newI) m s=run (F++M++I) m s:=by
 let H:=regValue src s.basis
 let vs:=ReorderedCacheBits.values 4 105 H (976*H/1024)
 have mid:=middle_erased s m hz hb hi ha after flag
 have forward:=forward_frame s (m.take (measurementCount F)) H
  (prefix_zero s _ hz hb hi ha zero) (forward_values s _ hz hb hi ha)
 apply CacheFromCleanForwardResearch.equivalent F newF M I newI hosts vs
  forward_measurements middle_fresh I_off geometry.1 s m
  (forward_zero s _ hz hb hi ha zero) forward
 rw [mid]
 exact inverse_ready H (middleState oldF oldM s m) _ after

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Core
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def core:Program:=(newF++M++newI)++(C105LowEraseResearch.clear++tail)

theorem inverse_measurements:measurementCount newI=measurementCount I:=by
 have h:=ReorderedConsumedSub.measurement_eq 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide)
 have eq:measurementCount HighConsumedC105Research.sub=measurementCount rawI:=
  HighConsumedC105Research.sub_measurements.trans h
 simp only [newI,I,measurementCount_append,eq]

theorem prefix_measurements:measurementCount (newF++M++newI)=measurementCount (F++M++I):=by
 simp only [measurementCount_append,forward_measurements,inverse_measurements]

theorem core_plain(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run core m s=run (oldF++oldM++ReorderedCPlain.unbuild acc pad bank cin src) m s:=by
 have eq:=ClearContextResearch.append_at (newF++M++newI) (F++M++I) (C105LowEraseResearch.clear++tail)
  s m prefix_measurements (cache_loop s m hz hb hi ha zero after flag)
 have shape:(F++M++I)++(C105LowEraseResearch.clear++tail)=F++M++(I++C105LowEraseResearch.clear++tail):=by
  have g(A B C D E:Program):(A++B++C)++(D++E)=A++B++(C++D++E):=by simp only [List.append_assoc]
  exact g F M I C105LowEraseResearch.clear tail
 exact eq.trans ((congrArg (fun P=>run P m s) shape).trans (plain_loop s m hz hb hi ha after flag))

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CKKnownMiddle
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKKnownMiddleResearch
open ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires C163Low4Middle.bankChecked

theorem measurements:measurementCount KnownCMidStaged.body=measurementCount C163Low4Middle.bankChecked.out:=
 (KnownSparseFold.Cert.counts _ _ _ _ _ KnownCMidStaged.cert).2

theorem equivalent(H:Nat)(s:State)(m:List Bool)
 (before:WReady ga pad bank L.core.cin src H s):
 run KnownCMidStaged.body m s=run C163Low4Middle.bankChecked.out m s:=by
 have z:KnownSparseFold.Zero KnownCMidStaged.known0 s:=by
  intro u hu
  rcases ReorderedKnownC.guard u hu with ⟨_,_,hb⟩
  exact hb.elim (fun h=>before.2.2.2.1 u h) (fun h=>h.symm ▸ before.2.2.2.2)
 exact (KnownSparseFold.Cert.correct _ _ _ _ _ KnownCMidStaged.cert s m z).1

theorem middle_eq(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)
 (hi:s.basis L.core.cin=false)(ha:regValue ga s.basis=0):
 middleState (ReorderedCPlain.build ga pad bank L.core.cin src) KnownCMidStaged.body s m=
 middleState (ReorderedCPlain.build ga pad bank L.core.cin src) C163Low4Middle.bankChecked.out s m:=by
 unfold middleState
 rw [measurements]
 exact equivalent _ _ _ (Ghost3CacheC.plain_ready s _ hz hb hi ha)


end ECDSAAdd.Entrant.CKKnownMiddleResearch

end

-- Verified ABC18 optimization component C105Frame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.C105Research
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
 InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires C163Low4Middle.bankChecked C163Low4Middle.specialChecked
abbrev p:=C163Low4Middle.p
theorem core_frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) core
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have len:=lengths
 have fit:=fits
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue ga s.basis=0:=C163Low4Ghost.ghostAcc_zero L s.basis clean
 have qz:s.basis q=false:=(regValue_zero _ _).mp clean.work q (by decide)
 have rz:s.basis r=false:=(regValue_zero _ _).mp clean.work r (by decide)
 have pz:s.basis p=false:=(hf.2 p (by decide)).trans hp
 have dz:s.basis d=false:=(hf.2 d (by decide)).trans hd
 have zeroU:∀u∈hs,s.basis u=false:=by
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · rcases List.mem_append.mp hu with hu|hu
    · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
    · have e:u=d:=by simpa only [List.mem_singleton] using hu
      subst u
      exact dz
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_take hu)
 have zeroOld:∀u∈ReorderedCFixed.hosts,s.basis u=false:=by
  intro u hu
  simp only [ReorderedCFixed.hosts,List.mem_cons] at hu
  rcases hu with rfl|rfl|rfl|hu
  · exact qz
  · exact rz
  · exact pz
  · exact zeroU u hu
 have offHs:∀u∈hs,u∉wires (ReorderedCPlain.build ga pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (by simp only [ReorderedCFixed.hosts,List.mem_cons];exact Or.inr (Or.inr (Or.inr hu)))).1
 have goodOld:=fun record=>good base hc O hO s record hf
 have goodSpecial:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) specialChecked.out s m):=by
  rw [ReorderedRetape.c_middle_eq ga pad bank L.core.cin src specialChecked.out
   len.1 len.2.2.2 fit s m hz hb clean.cin ha]
  exact goodOld _
 have middleEq:=bank_cert.middle_eq hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) s m zeroU offHs
 have goodBank:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) bankChecked.out s m):=by
  rw [middleEq]
  exact goodSpecial
 have knownEq:=CKKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
 have goodKnown:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) KnownCMidStaged.body s m):=by
  rw [knownEq]
  exact goodBank
 have buildFrame:=ReorderedCPlain.build_triple ga pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
  s.basis hz hb clean.cin s (m.take (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  ⟨ha,fun _ _=>rfl⟩
 have flag:(run (ReorderedCPlain.build ga pad bank L.core.cin src)
  (m.take (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src))) s).basis 4762=false:=
  (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
 have cachedNew:=core_plain s m hz hb clean.cin ha zeroOld goodKnown flag
 have midEq:run KnownCMidStaged.body (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s)=
  run C163Low4Middle.bankChecked.out (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using knownEq
 have ctxt:=ReorderedKnownA.context_eq
  (ReorderedCPlain.build ga pad bank L.core.cin src) C163Low4Middle.bankChecked.out KnownCMidStaged.body
  (ReorderedCPlain.unbuild ga pad bank L.core.cin src) s m CKKnownMiddleResearch.measurements midEq
 have cacheEq:=cachedNew.trans ctxt
 have middleReplace:=bank_cert.surround_eq hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) (ReorderedCPlain.unbuild ga pad bank L.core.cin src)
  s m zeroU offHs
 have plainEq:=ReorderedRetape.c_loop_eq ga pad bank L.core.cin src specialChecked.out
  len.1 len.2.2.2 fit s m hz hb clean.cin ha goodOld
 let record:=ReorderedRetape.tape (measurementCount (C163NarrowAcc.build8 ga pad bank L.core.cin src))
  (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)) m
 have oldFrame:=C163Low4Middle.frame base hc hp hd O hO s record hf
 rw [eq_plain base hc hp hd O hO s record hf] at oldFrame
 have finalEq:run core m s=run (C163NarrowAcc.build8 ga pad bank L.core.cin src++specialChecked.out++
  C163SourceAdd.unbuild ga pad bank L.core.cin src) record s:=cacheEq.trans (middleReplace.trans plainEq)
 exact transport (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)) s _ _ finalEq oldFrame



end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Sign
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.C105SignResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=C105Research.hosts
abbrev p:=C163Low4Middle.p

def suffix:Program:=C105LowEraseResearch.clear++
 ReorderedGenericCache.cachedAdd 105 C105Research.xs C105Research.ys C105Research.cs hosts L.core.cin++
 C105Research.top++C105Research.M++C105Research.newI++C105LowEraseResearch.clear++C105Research.tail

def loop:Program:=SignCHead.head++suffix

theorem loop_eq(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p)
 (s:State)(m:List Bool)(hf:SquareFrame L.core.out base O s.basis):
 run loop m s=run C105Research.core
  (SignRetape.tape SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) m) s:=by
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue ga s.basis=0:=ghostAcc_zero L s.basis clean
 have h:∀a b:List Bool,run SignCHead.head a s=run (ReorderedCHead.head ga pad bank L.core.cin src) b s:=by
  intro a b
  exact ReorderedFrameUnique.program_eq ga s.basis 0 ((2^140-48*regValue src s.basis)%2^140) _ _
   (SignCHead.frame s.basis hz hb clean.cin)
   (ReorderedCHead.head_triple ga pad bank L.core.cin src lengths.1 (by decide) fits s.basis hz hb clean.cin)
   s a b ⟨ha,fun _ _=>rfl⟩
 have eq:=SignRetape.replace SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) suffix s m h
 simpa only [loop,suffix,C105Research.core,C105Research.newF,C105Research.head,C105Research.xs,
  C105Research.ys,C105Research.cs,List.append_assoc] using eq


theorem frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have e:=loop_eq base hc O hO s m hf
 have old:=C105Research.core_frame base hc hp hd O hO s (SignRetape.tape SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) m) hf
 exact ReorderedCFixed.transport _ s _ _ e old

theorem fold_frame(base:BasisState)(hv:AccView L base (OwnDiagAll12Square.accCItem L))(hc:L.PairClean base)
 (M:Nat)(pv:regValue L.core.product base=M^2)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-Acc.accVal base 0 (OwnDiagAll12Square.accCItem L).spec else Acc.accVal base 0 (OwnDiagAll12Square.accCItem L).spec)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have f:=frame base hc (spare_zero L hw base M pv) hd O hO s m hf
 have e:=congrArg (fun A:Nat=>((if base g then C163Low4Facts.Klow-A else A)+(SquareReduction.p-1-O))%SquareReduction.p)
  (C163Fold.payload_spec L base)
 exact ⟨f.1,Eq.mp (congrArg (fun n:Nat=>SquareFrame L.core.out base n (run loop m s).basis) e) f.2⟩

def rawBody:Program:=C163Low4Body.bodyProgram L loop

theorem raw_body_frame(base:BasisState)(M:Nat)(pv:regValue L.core.product base=M^2)
 (clean:L.PairClean base)(disabled:base g=false→M=0)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) rawBody
  (SquareFrame L.core.out base (C163Low4Body.resCFK C163Low4Facts.Klow (base g) (M^2) O)):=by
 intro s m hf
 have away(q:Wire)(hq:q∈L.core.product):q∉L.core.out:=
  fun ho=>List.disjoint_left.mp (L.product_out_disjoint hn) hq ho
 have prod:regValue L.core.product s.basis=M^2:=
  (regValue_congr _ _ _ (fun q hq=>hf.2 q (away q hq))).trans pv
 have cs:=L.squareFrame_clean hn base s.basis O hf clean
 have gs:s.basis g=base g:=hf.2 g (by decide)
 have ds:s.basis d=false:=(hf.2 d (by decide)).trans hd
 have dm:s.basis g=false→M=0:=by rw [gs];exact disabled
 have out:=C163Low4Body.body_output L hw g (List.nodup_cons.mpr ⟨geometry.1,hn⟩)
  d loop C163Low4Facts.Klow cap fold_frame M O hO s m prod dm cs hf.1 ds
 rw [gs] at out
 exact ⟨out.1,out.2.1,fun q hq=>(out.2.2 q hq).trans (hf.2 q hq)⟩

def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin

theorem body_frame(base:BasisState)(M:Nat)(pv:regValue L.core.product base=M^2)
 (clean:L.PairClean base)(disabled:base g=false→M=0)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) body
  (SquareFrame L.core.out base (C163Low4Body.resCFK C163Low4Facts.Klow (base g) (M^2) O)):=by
 intro s m hf
 have f:=raw_body_frame base M pv clean disabled hd O hO s (m.take (measurementCount rawBody)) hf
 have hz:(run rawBody (m.take (measurementCount rawBody)) s).basis L.core.cin=false:=
  (f.2.2 L.core.cin (by decide)).trans clean.cin
 have eq:run body m s=run rawBody (m.take (measurementCount rawBody)) s:=by
  rw [body,run_append,ReorderedRecordPadding.run_zero 7 L.core.cin _ _ hz]
 exact ReorderedCFixed.transport _ s _ _ eq f



end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Counts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105SignResearch
open C105PrefixResearch C105Research Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem loop_counts:toffoliCount loop+3=toffoliCount HighSignCResearch.loop ∧
 measurementCount loop=measurementCount HighSignCResearch.loop:=by
 have aa:C163Low4Middle.ga=acc:=by decide +kernel
 have ap:C163Low4Middle.pad=pad:=by decide +kernel
 have ab:C163Low4Middle.bank=bank:=by decide +kernel
 have ax:C163Low4Middle.src=src:=by decide +kernel
 have ai:C163Low4Middle.L.core.cin=L.core.cin:=by decide +kernel
 have nc:=ReorderedGenericCache.count_balance 105 xs ys cs C105Research.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
 have oc:=ReorderedGenericCache.count_balance 102 xs ys cs Ghost3CacheC.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
 have ni:=HighConsumedC105Research.sub_toffoli
 have nm:=HighConsumedC105Research.sub_measurements
 have oi:=HighUnbuildCResearch.toffoli acc rfl
 have om:=HighUnbuildCResearch.measurements acc rfl
 have mt:=CKAliasesResearch.counts.1
 have mm:=CKAliasesResearch.counts.2.1
 have ot:=GhostRelocatedKnown.C.counts.1
 have omid:=GhostRelocatedKnown.C.counts.2
 have nt:=notRegister_counts ys
 simp only [ReorderedConsumedSub.consumed,toffoliCount_append,measurementCount_append] at ni nm oi om
 simp only [ReorderedCUnbuild.unbuild,ReorderedConsumedSub.consumed,toffoliCount_append,measurementCount_append] at oi om
 simp only [loop,suffix,newI,preInv,top,tail,M,HighSignCResearch.loop,HighSignCResearch.suffix,
  toffoliCount_append,measurementCount_append,C105LowEraseResearch.counts.1,C105LowEraseResearch.counts.2.1]
 -- replay memory (build-chain s5-lc): unfold the aliases in the hypotheses by simp, in the goal by rw (props first);
 -- simp on the goal made the kernel evaluate the generated programs (+5.6 GB).
 simp only [xs,ys,cs,HighConsumedC105Research.xs,HighConsumedC105Research.ys,HighConsumedC105Research.cs,HighConsumedC105Research.cin,HighConsumedC105Research.hs,C105PrefixResearch.cin,CKAliasesResearch.original,Ghost3CacheC.middle,GhostRelocatedKnown.C.original,HighSignCResearch.hosts,C105SignResearch.hosts,aa,ap,ab,ax,ai] at nc oc ni nm oi om mt mm ot omid nt
 try rw [aa]
 try rw [ap]
 try rw [ab]
 try rw [ax]
 try rw [ai]
 repeat (first | rw [xs] | rw [ys] | rw [cs] | rw [HighConsumedC105Research.xs] | rw [HighConsumedC105Research.ys] | rw [HighConsumedC105Research.cs] | rw [HighConsumedC105Research.cin] | rw [HighConsumedC105Research.hs] | rw [C105PrefixResearch.cin] | rw [CKAliasesResearch.original] | rw [Ghost3CacheC.middle] | rw [GhostRelocatedKnown.C.original] | rw [HighSignCResearch.hosts] | rw [C105SignResearch.hosts])
 exact ⟨by omega,by omega⟩

 theorem body_counts:toffoliCount body+3=toffoliCount HighSignCResearch.body ∧
 measurementCount body=measurementCount HighSignCResearch.body:=by
 have h:=loop_counts
 simp only [body,rawBody,HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,
  toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩


end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Slots
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105SignResearch
open C105PrefixResearch C105Research Challenge
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Challenge.gateSlots
 theorem loop_slots:gateSlots loop+12=gateSlots HighSignCResearch.loop:=by
 have aa:C163Low4Middle.ga=acc:=by decide +kernel
 have ap:C163Low4Middle.pad=pad:=by decide +kernel
 have ab:C163Low4Middle.bank=bank:=by decide +kernel
 have ax:C163Low4Middle.src=src:=by decide +kernel
 have ai:C163Low4Middle.L.core.cin=L.core.cin:=by decide +kernel
 have nc:=ReorderedSlots.cache 105 xs ys cs C105Research.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide) geometry.2.1
 have oc:=ReorderedSlots.cache 102 xs ys cs Ghost3CacheC.hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide) Ghost3CacheC.geometry.2.1
 have ni:=HighConsumedC105Research.sub_slots
 have oi:=HighUnbuildCResearch.slots acc rfl
 have mid:=CKAliasesResearch.counts.2.2
 have oldmid:=RelocateResources.slots GhostRelocatedKnown.ports KnownCMidStaged.body
 simp only [ReorderedConsumedSub.consumed,gateSlots_append] at ni
 simp only [ReorderedCUnbuild.unbuild,ReorderedConsumedSub.consumed,gateSlots_append] at oi
 simp only [loop,suffix,newI,preInv,top,tail,M,HighSignCResearch.loop,HighSignCResearch.suffix,
  gateSlots_append,C105LowEraseResearch.counts.2.2]
 try rw [xs] at *
 try rw [ys] at *
 try rw [cs] at *
 try rw [HighConsumedC105Research.xs] at *
 try rw [HighConsumedC105Research.ys] at *
 try rw [HighConsumedC105Research.cs] at *
 try rw [HighConsumedC105Research.cin] at *
 try rw [HighConsumedC105Research.hs] at *
 try rw [C105PrefixResearch.cin] at *
 try rw [CKAliasesResearch.original] at *
 try rw [Ghost3CacheC.middle] at *
 try rw [GhostRelocatedKnown.C.program] at *
 try rw [GhostRelocatedKnown.C.original] at *
 try rw [HighSignCResearch.hosts] at *
 try rw [C105SignResearch.hosts] at *
 try rw [xs] at *
 try rw [ys] at *
 try rw [cs] at *
 try rw [HighConsumedC105Research.xs] at *
 try rw [HighConsumedC105Research.ys] at *
 try rw [HighConsumedC105Research.cs] at *
 try rw [HighConsumedC105Research.cin] at *
 try rw [HighConsumedC105Research.hs] at *
 try rw [C105PrefixResearch.cin] at *
 try rw [CKAliasesResearch.original] at *
 try rw [Ghost3CacheC.middle] at *
 try rw [GhostRelocatedKnown.C.program] at *
 try rw [GhostRelocatedKnown.C.original] at *
 try rw [HighSignCResearch.hosts] at *
 try rw [C105SignResearch.hosts] at *
 simp only [aa,ap,ab,ax,ai] at *
 omega
 theorem body_slots:gateSlots body+12=gateSlots HighSignCResearch.body:=by
 have h:=loop_slots
 simp only [body,rawBody,HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,gateSlots_append]
 omega


end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Scope
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires
abbrev S:=wires HighSignCResearch.body
def oldPrefix:Program:=SignCHead.head++ReorderedGenericCache.cachedAdd 102 C163Low4Middle.src ((C163Low4Middle.ga.take 140).drop 10)
 (C163Low4Middle.bank.take 129) Ghost3CacheC.hosts C163Low4Middle.L.core.cin

theorem old_prefix_support:wires oldPrefix⊆S:=by
 intro q h
 simp only [oldPrefix,wires_append,Finset.mem_union] at h
 change q∈wires HighSignCResearch.body
 simp only [HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,
  HighSignCResearch.loop,HighSignCResearch.suffix,wires_append,Finset.mem_union]
 tauto

theorem old_middle_support:wires GhostRelocatedKnown.C.program⊆S:=by
 intro q h
 change q∈wires HighSignCResearch.body
 simp only [HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,
  HighSignCResearch.loop,HighSignCResearch.suffix,Ghost3CacheC.middle,wires_append,Finset.mem_union]
 tauto

def domainSelected396 : Program := [
 .CX 4243 4505,
 .CX 4244 4506,
 .CX 4245 4507,
 .CX 4246 4508,
 .CX 4247 4509,
 .CX 4248 4510,
 .CX 4249 4511,
 .CX 4250 4512,
 .CX 4251 4513,
 .CX 4252 4514,
 .CX 4253 4515,
 .CX 4254 4516,
 .CX 4255 4517,
 .CX 4256 4518,
 .CX 4257 4519,
 .CX 4258 4520,
 .CX 4259 4521,
 .CX 4260 4522,
 .CX 4261 4523,
 .CX 4262 4524,
 .CX 4263 4525,
 .CX 4264 4526,
 .CX 4265 4527,
 .CX 4266 4528,
 .CX 4267 4529,
 .CX 4268 4530,
 .CX 4269 4531,
 .CX 4270 4532,
 .CX 4271 4533,
 .CX 4272 4534,
 .CX 4273 4535,
 .CX 4274 4536,
 .CX 4275 4537,
 .CX 4276 4538,
 .CX 4277 4539,
 .CX 4278 4540,
 .CX 4279 4541,
 .CX 4280 4542,
 .CX 4281 4543,
 .CX 4282 4544,
 .CX 4283 4545,
 .CX 4284 4546,
 .CX 4285 4547,
 .CX 4286 4548,
 .CX 4287 4549,
 .CX 4288 4550,
 .CX 4289 4551,
 .CX 4290 4552,
 .CX 4291 4553,
 .CX 4292 4554,
 .CX 4293 4555,
 .CX 4294 4556,
 .CX 4295 4557,
 .CX 4296 4558,
 .CX 4297 4559,
 .CX 4298 4560,
 .CX 4299 4561,
 .CX 4300 4562,
 .CX 4301 4563,
 .CX 4302 4564,
 .CX 4303 4565,
 .CX 4304 4566,
 .CX 4305 4567,
 .CX 4306 4568,
 .CX 4307 4569,
 .CX 4308 4570,
 .CX 4309 4571,
 .CX 4310 4572,
 .CX 4311 4573,
 .CX 4312 4574,
 .CX 4313 4575,
 .CX 4314 4576,
 .CX 4315 4577,
 .CX 4316 4578,
 .CX 4317 4579,
 .CX 4318 4580,
 .CX 4319 4581,
 .CX 4320 4582,
 .CX 4321 4583,
 .CX 4322 4584,
 .CX 4323 4585,
 .CX 4324 4586,
 .CX 4325 4587,
 .CX 4326 4588,
 .CX 4327 4589,
 .CX 4328 4590,
 .CX 4329 4591,
 .CX 4330 4592,
 .CX 4331 4593,
 .CX 4332 4594,
 .CX 4333 4595,
 .CX 4334 4596,
 .CX 4335 4597,
 .CX 4336 4598,
 .CX 4337 4599,
 .CX 4338 4600,
 .CX 4339 4601,
 .CX 4340 4602,
 .CX 4341 4603,
 .CX 4342 4604,
 .CX 4343 4605,
 .CX 4344 4606,
 .CX 4345 4607,
 .CX 4346 4608,
 .CX 4347 4609,
 .CX 4348 4610,
 .CX 4349 4611,
 .CX 4350 4612,
 .CX 4351 4613,
 .CX 4352 4614,
 .CX 4353 4615,
 .CX 4354 4616,
 .CX 4355 4617,
 .CX 4356 4618,
 .CX 4357 4619,
 .CX 4358 4620,
 .CX 4359 4621,
 .CX 4360 4622,
 .CX 4361 4623,
 .CX 4362 4624,
 .CX 4363 4625,
 .CX 4364 4626,
 .CX 4365 4627,
 .CX 4366 4628,
 .CX 4367 4629,
 .CX 4368 4630,
 .CX 4369 4631,
 .CX 4370 4632,
 .CX 4371 4633,
 .CX 4372 4634,
 .CX 4796 4635,
 .CX 4797 4636,
 .CX 4798 4637,
 .CX 4799 4638,
 .CX 4800 4639,
 .CX 4801 4640,
 .CX 4243 4760,
 .CCX 4507 4760 4373,
 .CCX 4508 4373 4374,
 .CCX 4509 4374 4375,
 .CCX 4510 4375 4376,
 .CCX 4511 4376 4377,
 .CCX 4512 4377 4378,
 .CCX 4513 4378 4379,
 .CCX 4514 4379 4380,
 .CCX 4515 4380 4381,
 .CCX 4516 4381 4382,
 .CCX 4517 4382 4383,
 .CCX 4518 4383 4384,
 .CCX 4519 4384 4385,
 .CCX 4520 4385 4386,
 .CCX 4521 4386 4387,
 .CCX 4522 4387 4388,
 .CCX 4523 4388 4389,
 .CCX 4524 4389 4390,
 .CCX 4525 4390 4391,
 .CCX 4526 4391 4392,
 .CCX 4527 4392 4393,
 .CCX 4528 4393 4394,
 .CCX 4529 4394 4395,
 .CCX 4530 4395 4396,
 .CCX 4531 4396 4397,
 .CCX 4532 4397 4398,
 .CCX 4533 4398 4399,
 .CCX 4534 4399 4400,
 .CCX 4535 4400 4401,
 .CCX 4536 4401 4402,
 .CCX 4537 4402 4403,
 .CCX 4538 4403 4404,
 .CCX 4539 4404 4405,
 .CCX 4540 4405 4406,
 .CCX 4541 4406 4407,
 .CCX 4542 4407 4408,
 .CCX 4543 4408 4409,
 .CCX 4544 4409 4410,
 .CCX 4545 4410 4411,
 .CCX 4546 4411 4412,
 .CCX 4547 4412 4413,
 .CCX 4548 4413 4414,
 .CCX 4549 4414 4415,
 .CCX 4550 4415 4416,
 .CCX 4551 4416 4417,
 .CCX 4552 4417 4418,
 .CCX 4553 4418 4419,
 .CCX 4554 4419 4420,
 .CCX 4555 4420 4421,
 .CCX 4556 4421 4422,
 .CCX 4557 4422 4423,
 .CCX 4558 4423 4424,
 .CCX 4559 4424 4425,
 .CCX 4560 4425 4426,
 .CCX 4561 4426 4427,
 .CCX 4562 4427 4428,
 .CCX 4563 4428 4429,
 .CCX 4564 4429 4430,
 .CCX 4565 4430 4431,
 .CCX 4566 4431 4432,
 .CCX 4567 4432 4433,
 .CCX 4568 4433 4434,
 .CCX 4569 4434 4435,
 .CCX 4570 4435 4436,
 .CCX 4571 4436 4437,
 .CCX 4572 4437 4438,
 .CCX 4573 4438 4439,
 .CCX 4574 4439 4440,
 .CCX 4575 4440 4441,
 .CCX 4576 4441 4442,
 .CCX 4577 4442 4443,
 .CCX 4578 4443 4444,
 .CCX 4579 4444 4445,
 .CCX 4580 4445 4446,
 .CCX 4581 4446 4447,
 .CCX 4582 4447 4448,
 .CCX 4583 4448 4449,
 .CCX 4584 4449 4450,
 .CCX 4585 4450 4451,
 .CCX 4586 4451 4452,
 .CCX 4587 4452 4453,
 .CCX 4588 4453 4454,
 .CCX 4589 4454 4455,
 .CCX 4590 4455 4456,
 .CCX 4591 4456 4457,
 .CCX 4592 4457 4458,
 .CCX 4593 4458 4459,
 .CCX 4594 4459 4460,
 .CCX 4595 4460 4461,
 .CCX 4596 4461 4462,
 .CCX 4597 4462 4463,
 .CCX 4598 4463 4464,
 .CCX 4599 4464 4465,
 .CCX 4600 4465 4466,
 .CCX 4601 4466 4467,
 .CCX 4602 4467 4468,
 .CCX 4603 4468 4469,
 .CCX 4604 4469 4470,
 .CCX 4605 4470 4471,
 .CCX 4606 4471 4472,
 .CCX 4607 4472 4473,
 .CCX 4608 4473 4474,
 .CCX 4609 4474 4475,
 .CCX 4610 4475 4476,
 .CCX 4611 4476 4477,
 .CCX 4612 4477 4478,
 .CCX 4613 4478 4479,
 .CCX 4614 4479 4480,
 .CCX 4615 4480 4481,
 .CCX 4616 4481 4482,
 .CCX 4617 4482 4483,
 .CCX 4618 4483 4484,
 .CCX 4619 4484 4485,
 .CCX 4620 4485 4486,
 .CCX 4621 4486 4487,
 .CCX 4622 4487 4488,
 .CCX 4623 4488 4489,
 .CCX 4624 4489 4490,
 .CCX 4625 4490 4491,
 .CCX 4626 4491 4492,
 .CCX 4627 4492 4493,
 .CCX 4628 4493 4494,
 .CCX 4629 4494 4495,
 .CCX 4630 4495 4496,
 .CCX 4631 4496 4497,
 .CCX 4632 4497 4498,
 .CCX 4633 4498 4499,
 .CCX 4634 4499 4500,
 .CCX 4635 4500 4764,
 .CX 4377 4664,
 .CX 4378 4665,
 .CX 4379 4116,
 .CX 4380 4666,
 .CX 4381 4667,
 .CX 4382 4668,
 .CX 4383 4669,
 .CX 4384 4670,
 .CX 4385 4671,
 .CX 4386 4672,
 .CX 4387 4673,
 .CX 4388 4674,
 .CX 4389 4675,
 .CX 4390 4676,
 .CX 4391 4677,
 .CX 4392 4678,
 .CX 4393 4679,
 .CX 4394 4680,
 .CX 4395 4681,
 .CX 4396 4682,
 .CX 4397 4683,
 .CX 4398 4684,
 .CX 4399 4685,
 .CX 4400 4686,
 .CX 4401 4687,
 .CX 4402 4688,
 .CX 4403 4689,
 .CX 4404 4690,
 .CX 4405 4691,
 .CX 4406 4692,
 .CX 4407 4693,
 .CX 4408 4694,
 .CX 4409 4695,
 .CX 4410 4696,
 .CX 4411 4697,
 .CX 4412 4698,
 .CX 4413 4699,
 .CX 4414 4700,
 .CX 4415 4701,
 .CX 4416 4702,
 .CX 4417 4703,
 .CX 4418 4704,
 .CX 4419 4705,
 .CX 4420 4706,
 .CX 4421 4707,
 .CX 4422 4708,
 .CX 4423 4709,
 .CX 4424 4710,
 .CX 4425 4711,
 .CX 4426 4712,
 .CX 4427 4713,
 .CX 4428 4714,
 .CX 4429 4715,
 .CX 4430 4716,
 .CX 4431 4717,
 .CX 4432 4718,
 .CX 4433 4719,
 .CX 4434 4720,
 .CX 4435 4721,
 .CX 4436 4722,
 .CX 4437 4723,
 .CX 4438 4724,
 .CX 4439 4725,
 .CX 4440 4726,
 .CX 4441 4727,
 .CX 4442 4728,
 .CX 4443 4729,
 .CX 4444 4730,
 .CX 4445 4731,
 .CX 4446 4732,
 .CX 4447 4733,
 .CX 4448 4734,
 .CX 4449 4735,
 .CX 4450 4736,
 .CX 4451 4737,
 .CX 4452 4738,
 .CX 4453 4739,
 .CX 4454 4740,
 .CX 4455 4741,
 .CX 4456 4742,
 .CX 4457 4743,
 .CX 4458 4744,
 .CX 4459 4745,
 .CX 4460 4746,
 .CX 4461 4747,
 .CX 4462 4748,
 .CX 4463 4749,
 .CX 4464 4750,
 .CX 4465 4751,
 .CX 4466 4752,
 .CX 4467 4753,
 .CX 4468 4754,
 .CX 4469 4755,
 .CX 4470 4756,
 .CX 4471 5655,
 .CX 4472 4501,
 .CX 4473 4502,
 .CX 4474 4503,
 .CX 4475 4504,
 .CX 4476 4757,
 .CX 4477 4758,
 .CX 4478 4759
]

 theorem domainSelectedSublist396 : domainSelected396.Sublist oldPrefix := by decide +kernel
 theorem domainSelectedCovers396 : (domain++hosts++ports).all (fun q=>decide (q=4762)||C163Touch.touched domainSelected396 q)=true := by decide +kernel
 theorem checked : (domain++hosts++ports).all (fun q=>decide (q=4762)||C163Touch.touched oldPrefix q)=true := by
 apply List.all_eq_true.mpr
 intro q hq
 have h := List.all_eq_true.mp domainSelectedCovers396 q hq
 simp only [Bool.or_eq_true] at h ⊢
 rcases h with h|h
 · exact Or.inl h
 · exact Or.inr ((C163Touch.touched_spec _ _).mpr
    (RawDomainStructural390.sublist_support domainSelected396 oldPrefix domainSelectedSublist396 ((C163Touch.touched_spec _ _).mp h)))

theorem mod_old:4762∈S:=by
 have used:C163Touch.touched (GhostRelocatedKnown.C.program.take 2500) 4762=true:=by decide +kernel
 have h:4762∈wires (GhostRelocatedKnown.C.program.take 2500):=(C163Touch.touched_spec _ _).mp used
 have sub:wires (GhostRelocatedKnown.C.program.take 2500)⊆wires GhostRelocatedKnown.C.program:=by
  simpa only [List.drop_zero] using CKMiddleResearch.slice_subset GhostRelocatedKnown.C.program 0 2500
 exact old_middle_support (sub h)

theorem scope_in(q:Wire)(hq:q∈domain++hosts++ports):q∈S:=by
 have h:=List.all_eq_true.mp checked q hq
 simp only [Bool.or_eq_true] at h
 rcases h with h|h
 · have e:q=4762:=of_decide_eq_true h
   subst q
   exact mod_old
 · exact old_prefix_support ((C163Touch.touched_spec _ _).mp h)

theorem ports_in(q:Wire)(hq:q∈ports):q∈S:=scope_in q (List.mem_append_right _ hq)

theorem raw_domain_in:domain.toFinset∪hosts.toFinset⊆S:=by
 intro q hq
 have h:q∈domain++hosts:=by simpa only [List.mem_toFinset,List.mem_append,Finset.mem_union] using hq
 exact scope_in q (List.mem_append_left _ h)

theorem middle_support:wires M⊆S:=by
 intro q hq
 by_contra bad
 have ne(a:Wire)(ha:a∈ports):q≠a:=by intro eq;subst q;exact bad (ports_in a ha)
 have off:q∉wires oldM:=by
  intro h
  apply bad
  apply old_middle_support
  apply RelocateMembershipResearch.kept GhostRelocatedKnown.ports KnownCMidStaged.body q ?_ h
  intro i
  exact ne _ (by fin_cases i <;>decide)
 have one:q∉wires CKAliasesResearch.single:=CKMiddleResearch.fresh_of_old q off
  (fix q 4757 4760 (ne _ (by decide)) (ne _ (by decide))) (ne _ (by decide))
 have two:q∉wires M:=CKAliasesResearch.fresh_of_single q one
  (fix q 4505 4243 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4506 4244 (ne _ (by decide)) (ne _ (by decide)))
  (fix q 4507 4245 (ne _ (by decide)) (ne _ (by decide)))
  (ne _ (by decide)) (ne _ (by decide))
 exact two hq


end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Physical
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] GatePhysical ECDSAAdd.wires

theorem endpoint_physical:GatePhysical top ∧ GatePhysical preInv ∧ GatePhysical tail:=by
 have old:=Ghost3BodyResources.c_physical
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,C163Low4Body.bodyProgram,Ghost3SignC.loop,Ghost3SignC.suffix,
  ReorderedCUnbuild.unbuild,gatePhysical_append] at old
 simp only [top,preInv,tail]
 tauto

theorem cache_physical:GatePhysical (ReorderedGenericCache.cachedAdd 105 xs ys cs hosts cin) ∧
 GatePhysical (ReorderedConsumedSub.consumed 105 xs ys cs hosts cin):=by
 have f:=ReorderedPhysical.cached 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  raw_nd (fun q hq bad=>geometry.2.2 q hq (c_in q bad))
 have n:=notRegister_physical ys
 refine ⟨f.1,?_⟩
 simp only [ReorderedConsumedSub.consumed,gatePhysical_append]
 exact ⟨⟨n,f.2⟩,n⟩

theorem loop_physical:GatePhysical C105SignResearch.loop:=by
 have hi:GatePhysical newI:=by
  simp only [newI,gatePhysical_append]
  exact ⟨endpoint_physical.2.1,HighConsumedC105Research.sub_physical cache_physical.2⟩
 simp only [C105SignResearch.loop,C105SignResearch.suffix,C105SignResearch.hosts,gatePhysical_append]
 exact ⟨SignCHeadResources.physical,⟨⟨⟨⟨⟨⟨C105LowEraseResearch.physical,cache_physical.1⟩,endpoint_physical.1⟩,
  CKAliasesResearch.physical⟩,hi⟩,C105LowEraseResearch.physical⟩,endpoint_physical.2.2⟩⟩

theorem body_physical:GatePhysical C105SignResearch.body:=by
 have old:=HighBodyCResourceResearch.physical
 simp only [HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,gatePhysical_append] at old
 simp only [C105SignResearch.body,C105SignResearch.rawBody,C163Low4Body.bodyProgram,gatePhysical_append]
 have lp:=loop_physical
 tauto

end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Support
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch ControlLoan1589BFFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem clear_support:wires C105LowEraseResearch.clear⊆S:=by
 have eq:wires C105LowEraseResearch.clear=([4243,4505,4244,4506,4245,4507]:List Wire).toFinset:=by
  ext q
  simp [C105LowEraseResearch.clear,wires,Instr.wires,correctionWires]
  tauto
 rw [eq]
 intro q hq
 have sub:([4243,4505,4244,4506,4245,4507]:List Wire)⊆ports:=by decide
 exact ports_in q (sub (List.mem_toFinset.mp hq))

theorem endpoint_support:wires top⊆S ∧ wires preInv⊆S ∧ wires tail⊆S:=by
 have aa:C163Low4Middle.ga=acc:=by decide +kernel
 have ap:C163Low4Middle.pad=pad:=by decide +kernel
 have ab:C163Low4Middle.bank=bank:=by decide +kernel
 have ax:C163Low4Middle.src=src:=by decide +kernel
 have ai:C163Low4Middle.L.core.cin=L.core.cin:=by decide +kernel
 have whole:wires HighSignCResearch.loop⊆S:=by
  simp only [S,HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,wires_append]
  exact Finset.subset_union_right.trans Finset.subset_union_left
 have parts:=whole
 simp only [HighSignCResearch.loop,HighSignCResearch.suffix,wires_append,Finset.union_subset_iff] at parts
 have inv:=parts.2.2
 simp only [HighUnbuildCResearch.unbuild,wires_append,Finset.union_subset_iff] at inv
 refine ⟨?_,?_,?_⟩
 · simpa only [top,aa,ap,ab,ax,ai] using parts.2.1.1.2
 · simpa only [preInv,aa,ap,ab,ax,ai] using inv.1.1
 · simpa only [tail,aa,ap,ab,ax,ai] using inv.2

theorem cache_support:wires (ReorderedGenericCache.cachedAdd 105 xs ys cs hosts cin)⊆S ∧
 wires (ReorderedConsumedSub.consumed 105 xs ys cs hosts cin)⊆S:=by
 have c:=ReorderedSupport.cached 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
 have i:=ReorderedSupport.consumed 105 xs ys cs hosts cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
 exact ⟨c.1.trans raw_domain_in,i.trans raw_domain_in⟩

theorem loop_support:wires C105SignResearch.loop⊆S:=by
 have hh:wires SignCHead.head⊆S:=by
  apply Finset.Subset.trans ?_ old_prefix_support
  rw [oldPrefix,wires_append]
  exact Finset.subset_union_left
 have hi:wires newI⊆S:=by
  simp only [newI,wires_append]
  exact Finset.union_subset endpoint_support.2.1 (HighConsumedC105Research.sub_support.trans cache_support.2)
 simp only [C105SignResearch.loop,C105SignResearch.suffix,C105SignResearch.hosts,wires_append,Finset.union_subset_iff]
 exact ⟨hh,⟨⟨⟨⟨⟨⟨clear_support,cache_support.1⟩,endpoint_support.1⟩,middle_support⟩,hi⟩,clear_support⟩,endpoint_support.2.2⟩⟩

theorem body_support:wires C105SignResearch.body⊆S:=by
 have h:=BodySupportContextResearch.replace1
  (mixFoldsQTq C163Low4Middle.L false [.inl (negRot C163Low4Middle.L)])
  HighSignCResearch.loop C105SignResearch.loop
  (ReorderedRecordPadding.program 7 C163Low4Middle.L.core.cin) loop_support
 exact h


end ECDSAAdd.Entrant.C105Research

end

end
section


-- Verified B optimization component BArithmeticCounts
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.BArithmeticCountsResearch
open ReorderedBPrefixResearch ReorderedBSupportResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false

def newBuild:Program:=ReorderedABuild.build 89 acc pad bank cin src hosts
def newInv:Program:=ReorderedAUnbuild.unbuild 89 acc pad bank cin src hosts

theorem cnt_newBuild:(toffoliCount newBuild,measurementCount newBuild,Challenge.gateSlots newBuild)=(386,386,5148):=by
 decide +kernel
theorem cnt_newInv:(toffoliCount newInv,measurementCount newInv,Challenge.gateSlots newInv)=(143,386,4485):=by
 decide +kernel
theorem cnt_build:(toffoliCount SixCarryLoopAnchor.build,measurementCount SixCarryLoopAnchor.build,
  Challenge.gateSlots SixCarryLoopAnchor.build)=(387,388,5173):=by
 decide +kernel
theorem cnt_unbuild:(toffoliCount LocalEightLoop.unbuild,measurementCount LocalEightLoop.unbuild,
  Challenge.gateSlots LocalEightLoop.unbuild)=(144,388,4638):=by
 decide +kernel

theorem counts:
 toffoliCount newBuild+toffoliCount newInv+2=
  toffoliCount SixCarryLoopAnchor.build+toffoliCount LocalEightLoop.unbuild ∧
 measurementCount newBuild+measurementCount newInv+4=
  measurementCount SixCarryLoopAnchor.build+measurementCount LocalEightLoop.unbuild ∧
 Challenge.gateSlots newBuild+Challenge.gateSlots newInv+178=
  Challenge.gateSlots SixCarryLoopAnchor.build+Challenge.gateSlots LocalEightLoop.unbuild:=by
 have h1:=cnt_newBuild
 have h2:=cnt_newInv
 have h3:=cnt_build
 have h4:=cnt_unbuild
 simp only [Prod.mk.injEq] at h1 h2 h3 h4
 omega

end ECDSAAdd.Entrant.BArithmeticCountsResearch

end

-- Verified B optimization component BBodyBalance
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.BBodyBalanceResearch
open ReorderedBPrefixResearch ControlLoan1589BFFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots
 SixCarryLoopAnchor.build SixCarryLoopAnchor.output LocalEightLoop.unbuild EightCarryPrefix.improved
 ReorderedABuild.build ReorderedAUnbuild.unbuild LocalEFoldOptimize.improved LocalRebuild.improved

def shell(p:Program):Program:=LocalSevenBody.bodyForBoth L p LocalEFoldOptimize.improved LocalRebuild.improved

theorem new_shape:ReorderedBBodyResearch.body=shell ReorderedBBodyResearch.actualLoop:=by rfl

theorem old_shape:LocalEightBody99.body=shell LocalEightLoop.improved:=by rfl

theorem loop_t:toffoliCount ReorderedBBodyResearch.actualLoop=toffoliCount LocalEightLoop.improved+6:=by
 have a:=BArithmeticCountsResearch.counts.1
 have b:=EightCarryPrefix.toffoli
 rw [LocalSevenShape.core_shape] at b
 simp only [toffoliCount_append] at b
 have n:toffoliCount ReorderedBBodyResearch.actualLoop=toffoliCount BArithmeticCountsResearch.newBuild+toffoliCount SixCarryLoopAnchor.output+toffoliCount BArithmeticCountsResearch.newInv:=by
  change toffoliCount (BArithmeticCountsResearch.newBuild++SixCarryLoopAnchor.output++BArithmeticCountsResearch.newInv)=_
  simp only [toffoliCount_append]
 have o:toffoliCount LocalEightLoop.improved=toffoliCount EightCarryPrefix.improved+toffoliCount LocalEightLoop.unbuild:=by
  rw [LocalEightLoop.improved,toffoliCount_append]
 omega

theorem shell_t(p q:Program)(h:toffoliCount p=toffoliCount q+6):toffoliCount (shell p)=toffoliCount (shell q)+6:=by
 simp only [shell,LocalSevenBody.bodyForBoth,LowAccCarryDevelop.foldFor,toffoliCount_append]
 omega

theorem loop_m:measurementCount ReorderedBBodyResearch.actualLoop+4=measurementCount LocalEightLoop.improved:=by
 have a:=BArithmeticCountsResearch.counts.2.1
 have b:=EightCarryPrefix.measurements
 rw [LocalSevenShape.core_shape] at b
 simp only [measurementCount_append] at b
 have n:measurementCount ReorderedBBodyResearch.actualLoop=measurementCount BArithmeticCountsResearch.newBuild+measurementCount SixCarryLoopAnchor.output+measurementCount BArithmeticCountsResearch.newInv:=by
  change measurementCount (BArithmeticCountsResearch.newBuild++SixCarryLoopAnchor.output++BArithmeticCountsResearch.newInv)=_
  simp only [measurementCount_append]
 have o:measurementCount LocalEightLoop.improved=measurementCount EightCarryPrefix.improved+measurementCount LocalEightLoop.unbuild:=by
  rw [LocalEightLoop.improved,measurementCount_append]
 omega

theorem shell_m(p q:Program)(h:measurementCount p+4=measurementCount q):measurementCount (shell p)+4=measurementCount (shell q):=by
 simp only [shell,LocalSevenBody.bodyForBoth,LowAccCarryDevelop.foldFor,measurementCount_append]
 omega

theorem loop_s:Challenge.gateSlots ReorderedBBodyResearch.actualLoop+191=Challenge.gateSlots LocalEightLoop.improved:=by
 have a:=BArithmeticCountsResearch.counts.2.2
 have b:=EightCarryPrefix.slots
 rw [LocalSevenShape.core_shape] at b
 simp only [Challenge.gateSlots_append] at b
 have n:Challenge.gateSlots ReorderedBBodyResearch.actualLoop=Challenge.gateSlots BArithmeticCountsResearch.newBuild+Challenge.gateSlots SixCarryLoopAnchor.output+Challenge.gateSlots BArithmeticCountsResearch.newInv:=by
  change Challenge.gateSlots (BArithmeticCountsResearch.newBuild++SixCarryLoopAnchor.output++BArithmeticCountsResearch.newInv)=_
  simp only [Challenge.gateSlots_append]
 have o:Challenge.gateSlots LocalEightLoop.improved=Challenge.gateSlots EightCarryPrefix.improved+Challenge.gateSlots LocalEightLoop.unbuild:=by
  rw [LocalEightLoop.improved,Challenge.gateSlots_append]
 omega

theorem shell_s(p q:Program)(h:Challenge.gateSlots p+191=Challenge.gateSlots q):Challenge.gateSlots (shell p)+191=Challenge.gateSlots (shell q):=by
 simp only [shell,LocalSevenBody.bodyForBoth,LowAccCarryDevelop.foldFor,Challenge.gateSlots_append]
 omega

theorem toffoli:toffoliCount ReorderedBBodyResearch.body=toffoliCount LocalEightBody99.body+6:=by
 rw [new_shape,old_shape]
 exact shell_t _ _ loop_t

theorem measurements:measurementCount ReorderedBBodyResearch.body+4=measurementCount LocalEightBody99.body:=by
 rw [new_shape,old_shape]
 exact shell_m _ _ loop_m

theorem slots:Challenge.gateSlots ReorderedBBodyResearch.body+191=Challenge.gateSlots LocalEightBody99.body:=by
 rw [new_shape,old_shape]
 exact shell_s _ _ loop_s



end ECDSAAdd.Entrant.BBodyBalanceResearch

end

-- Verified B optimization component BPatchedPaddedFrame
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BPatchedPaddedResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ReorderedBPrefixResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.measurementCount BPatchedBodyResearch.body
def body : Program := BPatchedBodyResearch.body ++ ReorderedRecordPadding.program 4 L.core.cin

















end ECDSAAdd.Entrant.BPatchedPaddedResearch

end

-- Verified B optimization component BPatchedPaddedCounts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BPatchedPaddedResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ReorderedBPrefixResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.toffoliCount Challenge.gateSlots GatePhysical LocalEightBody99.body

theorem toffoli:toffoliCount body+8=toffoliCount LocalEightBody99.body:=by
 have a:=BPatchedResourceResearch.toffoli
 have b:=BBodyBalanceResearch.toffoli
 have h:=ReorderedRecordPadding.counts 4 L.core.cin
 simp only [body,toffoliCount_append]
 omega

theorem measurements:measurementCount body=measurementCount LocalEightBody99.body:=by
 have a:=BPatchedResourceResearch.measurements
 have b:=BBodyBalanceResearch.measurements
 have h:=ReorderedRecordPadding.counts 4 L.core.cin
 simp only [body,measurementCount_append]
 omega

theorem slots:Challenge.gateSlots body+177≤Challenge.gateSlots LocalEightBody99.body:=by
 have a:=BPatchedResourceResearch.slots
 have b:=BBodyBalanceResearch.slots
 have h:=ReorderedRecordPadding.counts 4 L.core.cin
 simp only [body,Challenge.gateSlots_append]
 omega




end ECDSAAdd.Entrant.BPatchedPaddedResearch

end

-- Verified B optimization component BPatchedPaddedSupport
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BPatchedPaddedResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ReorderedBPrefixResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires GatePhysical LocalEFoldOptimize.improved LocalRebuild.improved


































end ECDSAAdd.Entrant.BPatchedPaddedResearch

end

-- Verified B optimization component BPatchedPadded
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.BPatchedPaddedResearch


end ECDSAAdd.Entrant.BPatchedPaddedResearch

end

-- Verified B optimization component BGenericSupport
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.BStrongSupportResearch
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedBPrefixResearch ReorderedBSupportResearch ControlLoan1589BFFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires List.toFinset LocalEFoldOptimize.improved LocalRebuild.improved
theorem cached_support(A:List Wire)(len:A.length=161)
 (fit:∀f∈earlyHTerms src,Acc.Fits A pad bank L.core.cin 161 f):
 wires (ReorderedABuild.build 89 A pad bank L.core.cin src hosts)⊆
  (L.core.cin::(src++A++pad++bank)).toFinset∪hosts.toFinset ∧
 wires (ReorderedAUnbuild.unbuild 89 A pad bank L.core.cin src hosts)⊆
  (L.core.cin::(src++A++pad++bank)).toFinset∪hosts.toFinset:=by
 let D:Finset Wire:=(L.core.cin::(src++A++pad++bank)).toFinset∪hosts.toFinset
 have pf:wires (ReorderedAPlain.build A pad bank L.core.cin src)⊆D:=
  (Ghost3CacheA.plain_support A len fit).1.trans Finset.subset_union_left
 have pi:wires (ReorderedAPlain.unbuild A pad bank L.core.cin src)⊆D:=
  (Ghost3CacheA.plain_support A len fit).2.trans Finset.subset_union_left
 have cd:(L.core.cin::(src++(A.take 138).drop 10++bank.take 127)).toFinset∪hosts.toFinset⊆D:=by
  apply Finset.union_subset ?_ Finset.subset_union_right
  intro q hq
  apply Finset.mem_union_left
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [List.mem_cons,List.mem_append] at h ⊢
  have aa:q∈(A.take 138).drop 10→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:q∈bank.take 127→q∈bank:=List.mem_of_mem_take
  tauto
 have cc:=ReorderedSupport.cached 89 src ((A.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by simp [len]) (by decide) (by simp [len];decide +kernel) (by simp [len];decide +kernel)
 have ci:=ReorderedSupport.consumed 89 src ((A.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by simp [len]) (by decide) (by simp [len];decide +kernel) (by simp [len];decide +kernel)
 have hhead:wires (ReorderedAHead.head A pad bank L.core.cin src)⊆D:=by
  intro q hq
  apply pf
  simp only [ReorderedAPlain.build,ReorderedAPre.pre,ReorderedAHead.head,A161Carry.buildPost,wires_append,Finset.mem_union] at hq ⊢
  tauto
 have hpost:wires (A161Carry.buildPost A pad bank L.core.cin src)⊆D:=by
  intro q hq
  apply pf
  simp only [ReorderedAPlain.build,ReorderedAPre.pre,A161Carry.buildPost,wires_append,Finset.mem_union] at hq ⊢
  tauto
 have hpre:wires (A161Carry.unbuildPre A pad bank L.core.cin src)⊆D:=by
  intro q hq
  apply pi
  simp only [ReorderedAPlain.unbuild,wires_append,Finset.mem_union]
  tauto
 have hafter:wires (ReorderedAUnbuild.after A pad bank L.core.cin src)⊆D:=by
  intro q hq
  apply pi
  simp only [ReorderedAPlain.unbuild,ReorderedAUnbuild.after,wires_append,Finset.mem_union] at hq ⊢
  tauto
 constructor
 · simp only [ReorderedABuild.build,wires_append]
   exact Finset.union_subset (Finset.union_subset hhead (cc.1.trans cd)) hpost
 · simp only [ReorderedAUnbuild.unbuild,wires_append]
   exact Finset.union_subset (Finset.union_subset hpre (ci.trans cd)) hafter


end ECDSAAdd.Entrant.BStrongSupportResearch

end

-- Verified B optimization component BOldDomain
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BOldDomainResearch
open ReorderedBPrefixResearch ReorderedBSupportResearch ControlLoan1589BFFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.wires
abbrev domain:List Wire:=(cin::(src++(ECDSAAdd.Entrant.accReg L).take 161++pad++bank))++hosts

def selected : Program := [
 .CX 4115 4501,
 .CX 4116 4502,
 .CX 4117 4503,
 .CX 4118 4504,
 .CX 4119 4505,
 .CX 4120 4506,
 .CX 4121 4507,
 .CX 4122 4508,
 .CX 4123 4509,
 .CX 4124 4510,
 .CX 4125 4511,
 .CX 4126 4512,
 .CX 4127 4513,
 .CX 4128 4514,
 .CX 4129 4515,
 .CX 4130 4516,
 .CX 4131 4517,
 .CX 4132 4518,
 .CX 4133 4519,
 .CX 4134 4520,
 .CX 4135 4521,
 .CX 4136 4522,
 .CX 4137 4523,
 .CX 4138 4524,
 .CX 4139 4525,
 .CX 4140 4526,
 .CX 4141 4527,
 .CX 4142 4528,
 .CX 4143 4529,
 .CX 4144 4530,
 .CX 4145 4531,
 .CX 4146 4532,
 .CX 4147 4533,
 .CX 4148 4534,
 .CX 4149 4535,
 .CX 4150 4536,
 .CX 4151 4537,
 .CX 4152 4538,
 .CX 4153 4539,
 .CX 4154 4540,
 .CX 4155 4541,
 .CX 4156 4542,
 .CX 4157 4543,
 .CX 4158 4544,
 .CX 4159 4545,
 .CX 4160 4546,
 .CX 4161 4547,
 .CX 4162 4548,
 .CX 4163 4549,
 .CX 4164 4550,
 .CX 4165 4551,
 .CX 4166 4552,
 .CX 4167 4553,
 .CX 4168 4554,
 .CX 4169 4555,
 .CX 4170 4556,
 .CX 4171 4557,
 .CX 4172 4558,
 .CX 4173 4559,
 .CX 4174 4560,
 .CX 4175 4561,
 .CX 4176 4562,
 .CX 4177 4563,
 .CX 4178 4564,
 .CX 4179 4565,
 .CX 4180 4566,
 .CX 4181 4567,
 .CX 4182 4568,
 .CX 4183 4569,
 .CX 4184 4570,
 .CX 4185 4571,
 .CX 4186 4572,
 .CX 4187 4573,
 .CX 4188 4574,
 .CX 4189 4575,
 .CX 4190 4576,
 .CX 4191 4577,
 .CX 4192 4578,
 .CX 4193 4579,
 .CX 4194 4580,
 .CX 4195 4581,
 .CX 4196 4582,
 .CX 4197 4583,
 .CX 4198 4584,
 .CX 4199 4585,
 .CX 4200 4586,
 .CX 4201 4587,
 .CX 4202 4588,
 .CX 4203 4589,
 .CX 4204 4590,
 .CX 4205 4591,
 .CX 4206 4592,
 .CX 4207 4593,
 .CX 4208 4594,
 .CX 4209 4595,
 .CX 4210 4596,
 .CX 4211 4597,
 .CX 4212 4598,
 .CX 4213 4599,
 .CX 4214 4600,
 .CX 4215 4601,
 .CX 4216 4602,
 .CX 4217 4603,
 .CX 4218 4604,
 .CX 4219 4605,
 .CX 4220 4606,
 .CX 4221 4607,
 .CX 4222 4608,
 .CX 4223 4609,
 .CX 4224 4610,
 .CX 4225 4611,
 .CX 4226 4612,
 .CX 4227 4613,
 .CX 4228 4614,
 .CX 4229 4615,
 .CX 4230 4616,
 .CX 4231 4617,
 .CX 4232 4618,
 .CX 4233 4619,
 .CX 4234 4620,
 .CX 4235 4621,
 .CX 4236 4622,
 .CX 4237 4623,
 .CX 4238 4624,
 .CX 4239 4625,
 .CX 4240 4626,
 .CX 4241 4627,
 .CX 4242 4628,
 .CX 4243 4629,
 .CX 4244 4630,
 .CX 4245 4631,
 .CX 4246 4632,
 .CX 4247 4633,
 .CX 4248 4634,
 .CX 4249 4635,
 .CX 4250 4636,
 .CX 4251 4637,
 .CX 4252 4638,
 .CX 4253 4639,
 .CX 4254 4640,
 .CX 4255 4641,
 .CX 4256 4642,
 .CX 4257 4643,
 .CX 4258 4644,
 .CX 4259 4645,
 .CX 4260 4646,
 .CX 4261 4647,
 .CX 4262 4648,
 .CX 4263 4649,
 .CX 4264 4650,
 .CX 4265 4651,
 .CX 4266 4652,
 .CX 4267 4653,
 .CX 4268 4654,
 .CX 4269 4655,
 .CX 4270 4656,
 .CX 4271 4657,
 .CX 4272 4658,
 .CX 4273 4659,
 .CX 4274 4660,
 .CX 4275 4661,
 .CX 4276 4662,
 .CX 4277 4663,
 .CX 4278 4664,
 .CX 4279 4665,
 .CX 4280 4666,
 .CX 4281 4667,
 .CX 4282 4668,
 .CX 4283 4669,
 .CX 4284 4670,
 .CX 4285 4671,
 .CX 4286 4672,
 .CX 4287 4673,
 .CX 4288 4674,
 .CX 4289 4675,
 .CX 4290 4676,
 .CX 4291 4677,
 .CX 4292 4678,
 .CX 4293 4679,
 .CX 4294 4680,
 .CX 4295 4681,
 .CX 4296 4682,
 .CX 4297 4683,
 .CX 4298 4684,
 .CX 4299 4685,
 .CX 4300 4686,
 .CX 4301 4687,
 .CX 4302 4688,
 .CX 4303 4689,
 .CX 4304 4690,
 .CX 4305 4691,
 .CX 4306 4692,
 .CX 4307 4693,
 .CX 4308 4694,
 .CX 4309 4695,
 .CX 4310 4696,
 .CX 4311 4697,
 .CX 4312 4698,
 .CX 4313 4699,
 .CX 4314 4700,
 .CX 4315 4701,
 .CX 4316 4702,
 .CX 4317 4703,
 .CX 4318 4704,
 .CX 4319 4705,
 .CX 4320 4706,
 .CX 4321 4707,
 .CX 4322 4708,
 .CX 4323 4709,
 .CX 4324 4710,
 .CX 4325 4711,
 .CX 4326 4712,
 .CX 4327 4713,
 .CX 4328 4714,
 .CX 4329 4715,
 .CX 4330 4716,
 .CX 4331 4717,
 .CX 4332 4718,
 .CX 4333 4719,
 .CX 4334 4720,
 .CX 4335 4721,
 .CX 4336 4722,
 .CX 4337 4723,
 .CX 4338 4724,
 .CX 4339 4725,
 .CX 4340 4726,
 .CX 4341 4727,
 .CX 4342 4728,
 .CX 4343 4729,
 .CX 4344 4730,
 .CX 4345 4731,
 .CX 4346 4732,
 .CX 4347 4733,
 .CX 4348 4734,
 .CX 4349 4735,
 .CX 4350 4736,
 .CX 4351 4737,
 .CX 4352 4738,
 .CX 4353 4739,
 .CX 4354 4740,
 .CX 4355 4741,
 .CX 4356 4742,
 .CX 4357 4743,
 .CX 4358 4744,
 .CX 4359 4745,
 .CX 4360 4746,
 .CX 4361 4747,
 .CX 4362 4748,
 .CX 4363 4749,
 .CX 4364 4750,
 .CX 4365 4751,
 .CX 4366 4752,
 .CX 4367 4753,
 .CX 4368 4754,
 .CX 4369 4755,
 .CX 4370 4756,
 .CX 4501 4760,
 .CCX 2 4760 4373,
 .CCX 3 4373 4374,
 .CCX 4 4374 4375,
 .CCX 5 4375 4376,
 .CCX 6 4376 4377,
 .CCX 7 4377 4378,
 .CCX 8 4378 4379,
 .CCX 9 4379 4380,
 .CCX 10 4380 4381,
 .CCX 11 4381 4382,
 .CCX 12 4382 4383,
 .CCX 13 4383 4384,
 .CCX 14 4384 4385,
 .CCX 15 4385 4386,
 .CCX 16 4386 4387,
 .CCX 17 4387 4388,
 .CCX 18 4388 4389,
 .CCX 19 4389 4390,
 .CCX 20 4390 4391,
 .CCX 21 4391 4392,
 .CCX 22 4392 4393,
 .CCX 23 4393 4394,
 .CCX 24 4394 4395,
 .CCX 25 4395 4396,
 .CCX 26 4396 4397,
 .CCX 27 4397 4398,
 .CCX 28 4398 4399,
 .CCX 29 4399 4400,
 .CCX 30 4400 4401,
 .CCX 31 4401 4402,
 .CCX 32 4402 4403,
 .CCX 33 4403 4404,
 .CCX 34 4404 4405,
 .CCX 35 4405 4406,
 .CCX 36 4406 4407,
 .CCX 37 4407 4408,
 .CCX 38 4408 4409,
 .CCX 39 4409 4410,
 .CCX 40 4410 4411,
 .CCX 41 4411 4412,
 .CCX 42 4412 4413,
 .CCX 43 4413 4414,
 .CCX 44 4414 4415,
 .CCX 45 4415 4416,
 .CCX 46 4416 4417,
 .CCX 47 4417 4418,
 .CCX 48 4418 4419,
 .CCX 49 4419 4420,
 .CCX 50 4420 4421,
 .CCX 51 4421 4422,
 .CCX 52 4422 4423,
 .CCX 53 4423 4424,
 .CCX 54 4424 4425,
 .CCX 55 4425 4426,
 .CCX 56 4426 4427,
 .CCX 57 4427 4428,
 .CCX 58 4428 4429,
 .CCX 59 4429 4430,
 .CCX 60 4430 4431,
 .CCX 61 4431 4432,
 .CCX 62 4432 4433,
 .CCX 63 4433 4434,
 .CCX 64 4434 4435,
 .CCX 65 4435 4436,
 .CCX 66 4436 4437,
 .CCX 67 4437 4438,
 .CCX 68 4438 4439,
 .CCX 69 4439 4440,
 .CCX 70 4440 4441,
 .CCX 71 4441 4442,
 .CCX 72 4442 4443,
 .CCX 73 4443 4444,
 .CCX 74 4444 4445,
 .CCX 75 4445 4446,
 .CCX 76 4446 4447,
 .CCX 77 4447 4448,
 .CCX 78 4448 4449,
 .CCX 79 4449 4450,
 .CCX 80 4450 4451,
 .CCX 81 4451 4452,
 .CCX 82 4452 4453,
 .CCX 83 4453 4454,
 .CCX 84 4454 4455,
 .CCX 85 4455 4456,
 .CCX 86 4456 4457,
 .CCX 87 4457 4458,
 .CCX 88 4458 4459,
 .CCX 89 4459 4460,
 .CCX 90 4460 4461,
 .CCX 91 4461 4462,
 .CCX 92 4462 4463,
 .CCX 93 4463 4464,
 .CCX 94 4464 4465,
 .CCX 95 4465 4466,
 .CCX 96 4466 4467,
 .CCX 97 4467 4468,
 .CCX 98 4468 4469,
 .CCX 99 4469 4470,
 .CCX 100 4470 4471,
 .CCX 101 4471 4472,
 .CCX 102 4472 4473,
 .CCX 103 4473 4474,
 .CCX 104 4474 4475,
 .CCX 105 4475 4476,
 .CCX 106 4476 4477,
 .CCX 107 4477 4478,
 .CCX 108 4478 4479,
 .CCX 109 4479 4480,
 .CCX 110 4480 4481,
 .CCX 111 4481 4482,
 .CCX 112 4482 4483,
 .CCX 113 4483 4484,
 .CCX 114 4484 4485,
 .CCX 115 4485 4486,
 .CCX 116 4486 4487,
 .CCX 117 4487 4488,
 .CCX 118 4488 4489,
 .CCX 119 4489 4490,
 .CCX 120 4490 4491,
 .CCX 121 4491 4492,
 .CCX 122 4492 4493,
 .CCX 123 4493 4494,
 .CCX 124 4494 4495,
 .CCX 125 4495 4496,
 .CCX 126 4496 4497,
 .CCX 127 4497 4498,
 .CCX 128 4498 4499,
 .CCX 129 4499 4500,
 .CCX 130 4500 4764,
 .CCX 131 4764 4765,
 .CCX 132 4765 4766,
 .CCX 133 4766 4767,
 .CCX 134 4767 4768,
 .CCX 135 4768 4769,
 .CCX 136 4769 4770,
 .CCX 137 4770 4771,
 .CCX 138 4771 4772,
 .CCX 139 4772 4773,
 .CCX 140 4773 4774,
 .CCX 141 4774 4775,
 .CCX 142 4775 4776,
 .CCX 143 4776 4777,
 .CCX 144 4777 4778,
 .CCX 145 4778 4779,
 .CCX 146 4779 4780,
 .CCX 147 4780 4781,
 .CCX 148 4781 4782,
 .CCX 149 4782 4783,
 .CCX 150 4783 4784,
 .CCX 151 4784 4785,
 .CCX 152 4785 4786,
 .CCX 153 4786 4787,
 .CCX 154 4787 4788,
 .CCX 155 4788 4789,
 .CCX 156 4789 4790,
 .CCX 157 4790 4791,
 .CCX 158 4791 4792,
 .CCX 159 4792 4793,
 .CCX 160 4793 4794,
 .CCX 161 4794 4795,
 .CCX 162 4795 4796,
 .CCX 163 4796 4797,
 .CCX 164 4797 4798,
 .CCX 165 4798 4799,
 .CCX 166 4799 4800,
 .CCX 167 4800 4801,
 .CCX 168 4801 4802,
 .CCX 169 4802 4803,
 .CCX 170 4803 4804,
 .CCX 171 4804 4805,
 .CCX 172 4805 4806,
 .CCX 173 4806 4807,
 .CCX 174 4807 4808,
 .CCX 175 4808 4809,
 .CCX 176 4809 4810,
 .CCX 177 4810 4811,
 .CCX 178 4811 4812,
 .CCX 179 4812 4813,
 .CCX 180 4813 4814,
 .CCX 181 4814 4815,
 .CCX 182 4815 4816,
 .CCX 183 4816 4817,
 .CCX 184 4817 4818,
 .CCX 185 4818 4819,
 .CCX 186 4819 4820,
 .CCX 187 4820 4821,
 .CCX 188 4821 4822,
 .CCX 189 4822 4823,
 .CCX 190 4823 4824,
 .CCX 191 4824 4825,
 .CCX 192 4825 4826,
 .CX 4377 4763
]

theorem selected_low : (selected.take 448).Sublist ((FullBTemp.prefixP LowAccCarryDevelop.L).take 1655) := by decide +kernel
theorem selected_high : (selected.drop 448).Sublist (EightCarryPrefix.improved.take 1477) := by decide +kernel

theorem selected_sublist : selected.Sublist LocalEightBody99.body := by
 rw [LocalEightBody99Costs.new_shape, ← List.take_append_drop 448 selected]
 refine List.Sublist.append (selected_low.trans (List.take_sublist _ _)) ?_
 refine List.Sublist.trans ?_ (List.sublist_append_left _ _)
 have e : LocalEightLoop.improved = EightCarryPrefix.improved ++ LocalEightLoop.unbuild := rfl
 rw [e]
 exact (selected_high.trans (List.take_sublist _ _)).trans (List.sublist_append_left _ _)

theorem selected_covers : domain.all (C163Touch.touched selected)=true := by decide +kernel

theorem sublist_support (A P : Program) (h : A.Sublist P) : wires A ⊆ wires P := by
 intro q hq
 have ha : A.any (C163Touch.instructionTouches q)=true := (C163Touch.touched_spec A q).mpr hq
 obtain ⟨i, hi, ht⟩ := List.any_eq_true.mp ha
 exact (C163Touch.touched_spec P q).mp (List.any_eq_true.mpr ⟨i, h.subset hi, ht⟩)

theorem checked:domain.all (C163Touch.touched LocalEightBody99.body)=true:=by
 apply List.all_eq_true.mpr
 intro q hq
 apply (C163Touch.touched_spec LocalEightBody99.body q).mpr
 apply sublist_support selected LocalEightBody99.body selected_sublist
 exact (C163Touch.touched_spec selected q).mp (List.all_eq_true.mp selected_covers q hq)



theorem support:domain.toFinset⊆wires LocalEightBody99.body:=by
 intro q hq
 exact (C163Touch.touched_spec _ _).mp (List.all_eq_true.mp checked q (List.mem_toFinset.mp hq))

end ECDSAAdd.Entrant.BOldDomainResearch

end

-- Verified B optimization component BOldSupport
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BOldSupportResearch
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedBPrefixResearch ReorderedBSupportResearch ControlLoan1589BFFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires List.toFinset KnownBHeadResearch.output
 HighUnbuildBResearch.unbuild ReorderedAUnbuild.unbuild LocalEFoldOptimize.improved
 LocalRebuild.improved LocalSevenBody.bodyForBoth SixCarryLoopAnchor.output
abbrev realAcc := (ECDSAAdd.Entrant.accReg L).take 161
abbrev S:=wires LocalEightBody99.body

theorem domain_in:(L.core.cin::(src++realAcc++pad++bank)).toFinset∪hosts.toFinset⊆S:=by
 simpa only [BOldDomainResearch.domain,List.toFinset_append] using BOldDomainResearch.support

theorem cached_support:
 wires (ReorderedABuild.build 89 acc pad bank L.core.cin src hosts)⊆S ∧
 wires (ReorderedAUnbuild.unbuild 89 acc pad bank L.core.cin src hosts)⊆S:=by
 have len:realAcc.length=161:=by
  simp [realAcc,ECDSAAdd.Entrant.accReg,LowAccCarryDevelop.layout_widths.core.work]
 have fit:∀f∈earlyHTerms src,Acc.Fits realAcc pad bank L.core.cin 161 f:=
  A161GenericFold.smallFit L LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup
 have h:=BStrongSupportResearch.cached_support realAcc len fit
 change wires (ReorderedABuild.build 89 ((LowAccCarryDevelop.ghostAcc L).take 161) pad bank L.core.cin src hosts)⊆S ∧
  wires (ReorderedAUnbuild.unbuild 89 ((LowAccCarryDevelop.ghostAcc L).take 161) pad bank L.core.cin src hosts)⊆S
 rw [BGhostStructureResearch.build,BGhostStructureResearch.inverse]
 exact ⟨h.1.trans domain_in,h.2.trans domain_in⟩

theorem middle_support:wires ReorderedBMiddlePatchesResearch.output⊆S:=by
 have hl:wires LocalEightLoop.improved⊆S:=by
  change wires LocalEightLoop.improved⊆wires LocalEightBody99.body
  rw [LocalEightBody99Costs.new_shape,wires_append,wires_append]
  exact Finset.subset_union_left.trans Finset.subset_union_right
 have hh:wires ReorderedBMiddlePatchesResearch.output⊆wires LocalEightLoop.improved:=by
  rw [LocalEightLoopResources.new_shape,ReorderedBMiddlePatchesResearch.shape8,wires_append,wires_append]
  exact Finset.subset_union_right.trans Finset.subset_union_left
 exact hh.trans hl









def shell(p:Program):Program:=LocalSevenBody.bodyForBoth L p LocalEFoldOptimize.improved LocalRebuild.improved

theorem shell_support(p q:Program)(hp:wires (shell p)⊆S)(hq:wires q⊆S):wires (shell q)⊆S:=by
 simp only [shell,LocalSevenBody.bodyForBoth,LowAccCarryDevelop.foldFor,wires_append,Finset.union_subset_iff] at hp ⊢
 tauto













end ECDSAAdd.Entrant.BOldSupportResearch

end

-- Verified B optimization component BPatchedSelector
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BPatchedSelectorResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] BPatchedPaddedResearch.body ZeroSetDevelop.compileS? ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots


























end ECDSAAdd.Entrant.BPatchedSelectorResearch


end

-- Verified B optimization component BPatchedPort
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.BPatchedPortResearch
open Arithmetic Secp256k1 Challenge Baselines ControlledPointLayout MappedCompressed
  CompressedPointDialog LowZero18Square ControlLoan1589BFFold R2SqEp760
attribute [local irreducible] run wires


































































































































































































































































































section Final
open Secp256k1 CompressedPointDialog


























































































end Final








































































                                                                                            

attribute [local irreducible] toffoliCount measurementCount gateSlots






















































end ECDSAAdd.Entrant.BPatchedPortResearch
end

end

-- Verified B optimization component BPatchedCore
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
section
namespace ECDSAAdd.Entrant.BPatchedCoreResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop FullASelectedDevelop R2SqEp760

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires



























































































































end ECDSAAdd.Entrant.BPatchedCoreResearch
end

end

-- Verified B optimization component BPatchedSquare
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
section
namespace ECDSAAdd.Entrant.BPatchedSquareResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout Secp256k1
 ControlLoan1589BFFold CompressedPointDialog

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

















































































private instance : NeZero p := ⟨by norm_num [p]⟩
private instance : Fact (1<p) := ⟨by norm_num [p]⟩
















































































end ECDSAAdd.Entrant.BPatchedSquareResearch
end

end

-- Verified B optimization component BPatchedEntry
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
section
namespace ECDSAAdd.Entrant.BPatchedEntryResearch
open Arithmetic Secp256k1 ControlledPointLayout CompressedPointDialog

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
private instance : NeZero p := ⟨by norm_num [p]⟩











































































end ECDSAAdd.Entrant.BPatchedEntryResearch
end

end

-- Verified B optimization component BPatchedProgramBalance
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BPatchedProgramBalanceResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout Challenge Baselines ControlLoan1589BFFold
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots
 BPatchedPaddedResearch.body LocalEightBody99.body






























































end ECDSAAdd.Entrant.BPatchedProgramBalanceResearch

end

-- Verified B optimization component BPatchedProgramPhysical
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
section
namespace ECDSAAdd.Entrant.BPatchedProgramPhysicalResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout R2SqEp760
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires


































end ECDSAAdd.Entrant.BPatchedProgramPhysicalResearch
end

end

-- Verified B optimization component BProgramActual
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BProgramActualResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout Challenge Baselines
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots
 HighSignAResearch.body HighSignCResearch.body



















































end ECDSAAdd.Entrant.BProgramActualResearch

end


-- Verified B95 optimization component HighConsumedB95
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.HighConsumedB95Research
abbrev xs:List Wire:=ReorderedBPrefixResearch.src
abbrev ys:List Wire:=(ReorderedBPrefixResearch.acc.take 138).drop 10
abbrev cs:List Wire:=ReorderedBPrefixResearch.bank.take 127
abbrev hs:List Wire:=B95Research.hosts
abbrev cin:Wire:=ReorderedBPrefixResearch.cin
def ports:Fin 12→Wire:=![4367,4368,4369,4370,4635,4636,4637,4638,4496,4497,4498,4499]
def old:Program:=ReorderedGenericCache.consumedAdd 95 xs ys cs hs cin
def pre:Program:=old.take 364
def post:Program:=old.drop 393
def fast:Program:=pre++PlacedUniformAdder4Research.fastAt ports++post

theorem ports_inj:Function.Injective ports:=by decide +kernel

theorem window:(old.drop 364).take 29=PlacedUniformAdder4Research.originalAt ports:=by decide +kernel

theorem shape:old=pre++PlacedUniformAdder4Research.originalAt ports++post:=by
 rw [pre,post,←window,←List.take_add]
 exact (List.take_append_drop 393 old).symm

theorem pre_measurements:measurementCount pre=0:=by decide +kernel

theorem pre_fresh:∀q∈UniformAdderSpliceResearch.cs ports,q∉wires pre:=by
 have rs4_h:(UniformAdderSpliceResearch.cs ports).all (fun q=>!C163Touch.touched pre q)=true:=by decide +kernel
 intro q hq
 exact HighConsumedStreamResearch.untouched _ _ (by simpa using List.all_eq_true.mp rs4_h q hq)

theorem post_fresh:∀q∈UniformAdderSpliceResearch.ys ports,q∉wires post:=by
 have rs4_h:(UniformAdderSpliceResearch.ys ports).all (fun q=>!C163Touch.touched post q)=true:=by decide +kernel
 intro q hq
 exact HighConsumedStreamResearch.untouched _ _ (by simpa using List.all_eq_true.mp rs4_h q hq)

theorem toffoli:toffoliCount fast+3=toffoliCount old:=by
 have h:=congrArg toffoliCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [toffoliCount_append] at h
 have g:toffoliCount fast=toffoliCount pre+toffoliCount (PlacedUniformAdder4Research.fastAt ports)+toffoliCount post:=by
  simp only [fast,toffoliCount_append]
 omega

theorem measurements:measurementCount fast=measurementCount old:=by
 have h:=congrArg measurementCount shape
 have q:=PlacedUniformAdder4Research.counts ports
 simp only [measurementCount_append] at h
 have g:measurementCount fast=measurementCount pre+measurementCount (PlacedUniformAdder4Research.fastAt ports)+measurementCount post:=by
  simp only [fast,measurementCount_append]
 omega


end ECDSAAdd.Entrant.HighConsumedB95Research


namespace ECDSAAdd.Entrant.HighConsumedB95Research
open InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop

theorem source_length:xs.length=128:=by decide +kernel

theorem target_length:ys.length=128:=by decide +kernel

theorem carry_length:cs.length=127:=by decide +kernel

theorem high_targets:ys.drop 124=UniformAdderSpliceResearch.ys ports:=by decide +kernel

theorem high_carries:∀q∈UniformAdderSpliceResearch.cs ports,q∈cs:=by
 intro q hq
 simp only [UniformAdderSpliceResearch.cs,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel

theorem high_word (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=95)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^128)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 95 H (976*H/1024)):
 regValue (UniformAdderSpliceResearch.ys ports)
  (run old [] (run (notRegister ys) [] s)).basis=0 ∨
 regValue (UniformAdderSpliceResearch.ys ports)
  (run old [] (run (notRegister ys) [] s)).basis=15:=by
 have v:=HighConsumedInputsResearch.inner_value 95 xs ys cs hs cin (by rw [source_length];decide) (by rw [target_length];decide)
   (by rw [carry_length];decide) (source_length.trans target_length.symm)
   (by rw [carry_length,target_length]) hn nd len fresh s [] hz hi H (976*H/1024) source target saved
 change regValue ys (run old [] (run (notRegister ys) [] s)).basis=
  (H+(2^ys.length-1-976*H/1024))%2^ys.length at v
 rw [target_length] at v
 rw [←high_targets,CuccaroStreamedSquareWideLayout.regValue_drop_div ys 124 (by rw [target_length];decide),v]
 have power:16*(2^124)=2^128:=by norm_num
 have a:=HighBorrowArithmeticResearch.borrow_remainder_high (2^124) H (by positivity)
  (show H<16*2^124 by simpa only [power] using hH)
 rw [power] at a
 by_cases h0:H=0
 · right;rw [a,if_pos h0]
 · left;rw [a,if_neg h0]

theorem inner_run_eq (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=95)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^128)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 95 H (976*H/1024)) (m:List Bool):
 run fast m (run (notRegister ys) [] s)=run old m (run (notRegister ys) [] s):=by
 let u:=run (notRegister ys) [] s
 have cys:∀q∈cs,q∉ys:=by
  intro q hq bad
  exact List.disjoint_left.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).2.2
   (List.mem_append_right _ bad) hq
 have cu:∀q∈UniformAdderSpliceResearch.cs ports,u.basis q=false:=by
  intro q hq
  have hc:=high_carries q hq
  have off:q∉wires (notRegister ys):=by simpa only [notRegister_wires,List.mem_toFinset] using cys q hc
  exact (run_preserves_outside (notRegister ys) [] s q off).trans (hz q hc)
 have ready:regValue (UniformAdderSpliceResearch.ys ports)
   (run (pre++PlacedUniformAdder4Research.originalAt ports++post) [] u).basis=0 ∨
  regValue (UniformAdderSpliceResearch.ys ports)
   (run (pre++PlacedUniformAdder4Research.originalAt ports++post) [] u).basis=15:=by
  simpa only [←shape] using high_word s hn nd len fresh hz hi H hH source target saved
 have eq:=UniformAdderSpliceResearch.replace ports ports_inj pre post u m pre_measurements cu pre_fresh post_fresh ready
 simpa only [fast,←shape] using eq

def sub:Program:=notRegister ys++fast++notRegister ys

theorem sub_measurements:measurementCount sub=measurementCount (ReorderedConsumedSub.consumed 95 xs ys cs hs cin):=by
 simp only [sub,ReorderedConsumedSub.consumed,measurementCount_append,measurements,old]


theorem sub_run_eq (s:State)
 (hn:(cin::(xs++ys++cs)).Nodup)(nd:hs.Nodup)(len:hs.length=95)
 (fresh:∀h∈hs,h∉cin::(xs++ys++cs))
 (hz:∀q∈cs,s.basis q=false)(hi:s.basis cin=false)
 (H:Nat)(hH:H<2^128)(source:regValue xs s.basis=H)(target:regValue ys s.basis=976*H/1024)
 (saved:hs.map s.basis=ReorderedCacheBits.values 4 95 H (976*H/1024)) (m:List Bool):
 run sub m s=run (ReorderedConsumedSub.consumed 95 xs ys cs hs cin) m s:=by
 have eq:=CodexKnownOnesTail.Helpers.run_mid_congr (notRegister ys) fast old (notRegister ys) m s
  (notRegister_counts ys).2 measurements (fun r=>inner_run_eq s hn nd len fresh hz hi H hH source target saved r)
 simpa only [sub,ReorderedConsumedSub.consumed,old] using eq



end ECDSAAdd.Entrant.HighConsumedB95Research


end

-- Verified B95 optimization component HighB95Resources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.HighConsumedB95Research

theorem support:wires fast⊆wires old:=by
 have q:=HighBorrowResourceResearch.placed_support ports
 have e:=congrArg wires shape
 simp only [wires_append] at e
 rw [fast,wires_append,wires_append,e]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem physical(h:GatePhysical old):GatePhysical fast:=by
 rw [shape] at h
 simp only [gatePhysical_append] at h
 change GatePhysical (pre++PlacedUniformAdder4Research.fastAt ports++post)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,HighBorrowResourceResearch.placed_physical ports ports_inj⟩,h.2⟩

theorem slots:Challenge.gateSlots fast+3=Challenge.gateSlots old:=by
 have h:=congrArg Challenge.gateSlots shape
 have q:=HighBorrowResourceResearch.placed_slots ports
 simp only [Challenge.gateSlots_append] at h
 have g:Challenge.gateSlots fast=Challenge.gateSlots pre+Challenge.gateSlots (PlacedUniformAdder4Research.fastAt ports)+Challenge.gateSlots post:=by
  simp only [fast,Challenge.gateSlots_append]
 omega

theorem sub_support:wires sub⊆wires (ReorderedConsumedSub.consumed 95 xs ys cs hs cin):=by
 have q:wires fast⊆wires (ReorderedGenericCache.consumedAdd 95 xs ys cs hs cin):=by simpa only [old] using support
 simp only [sub,ReorderedConsumedSub.consumed,wires_append]
 exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) q) (Finset.Subset.refl _)

theorem sub_physical(h:GatePhysical (ReorderedConsumedSub.consumed 95 xs ys cs hs cin)):GatePhysical sub:=by
 simp only [ReorderedConsumedSub.consumed,gatePhysical_append] at h
 change GatePhysical (notRegister ys++fast++notRegister ys)
 simp only [gatePhysical_append]
 exact ⟨⟨h.1.1,physical h.1.2⟩,h.2⟩

theorem sub_toffoli:toffoliCount sub+3=toffoliCount (ReorderedConsumedSub.consumed 95 xs ys cs hs cin):=by
 have q:=toffoli
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,toffoliCount_append]
 omega

theorem sub_slots:Challenge.gateSlots sub+3=Challenge.gateSlots (ReorderedConsumedSub.consumed 95 xs ys cs hs cin):=by
 have q:=slots
 simp only [old] at q
 simp only [sub,ReorderedConsumedSub.consumed,Challenge.gateSlots_append]
 omega
end ECDSAAdd.Entrant.HighConsumedB95Research


end

-- Verified B95 optimization component BGhostFixed
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BGhostFixedResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
abbrev L:=ReorderedBPrefixResearch.L
abbrev acc:=ReorderedBPrefixResearch.acc
abbrev src:=ReorderedBPrefixResearch.src
abbrev pad:=ReorderedBPrefixResearch.pad
abbrev bank:=ReorderedBPrefixResearch.bank
abbrev hosts:=ReorderedBSupportResearch.hosts






theorem off_plain(u:Wire)(hu:u∈hosts):
 u∉wires (ReorderedAPlain.build acc pad bank L.core.cin src) ∧
 u∉wires (ReorderedAPlain.unbuild acc pad bank L.core.cin src):=
 ReorderedBSupportResearch.plain_free u hu



end ECDSAAdd.Entrant.BGhostFixedResearch

end

-- Verified ABC18 optimization component BRelocatedReady (patched)
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BRelocatedReadyResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold BGhostFixedResearch
 ReorderedBRetapeResearch InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem patched_after(s:State)(m:List Bool)(hc:ExtraCarryDomain.Clean s.basis)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)
 (ha:regValue ReorderedBPrefixResearch.ga s.basis=0)
 (zero:∀q∈ReorderedBSupportResearch.hosts,s.basis q=false)
 (good:∀r:List Bool,WReady ReorderedBPrefixResearch.ga pad bank L.core.cin src (regValue src s.basis)
  (middleState oldBuild (FullBTemp.middle L LowAccCarryDevelop.c) s r)):
 WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState newBuild ReorderedBMiddlePatchesResearch.output s m):=by
 obtain ⟨cm,hcm⟩:=LocalEightLoop.exists_cm
 have z88:∀q∈LowAccCarryDevelop.hosts88,s.basis q=false:=by
  intro q hq
  exact zero q (List.mem_cons_of_mem _ hq)
 have oq:∀q∈LowAccCarryDevelop.hosts88,q∉wires oldBuild:=by
  intro q hq
  exact (ReorderedBLoopResearch.old_plain_free q (List.mem_cons_of_mem _ hq)).1
 have cmReady(r:List Bool):WReady ReorderedBPrefixResearch.ga pad bank L.core.cin src (regValue src s.basis)
  (middleState oldBuild cm.out s r):=by
  have eq:=cm.proof.middle_eq LowAccCarryDevelop.hosts88
   (FullBTemp.middle L LowAccCarryDevelop.c) cm.out oldBuild s r z88 oq
  rw [eq]
  exact good r
 have ready:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState newBuild cm.out s m):=by
  rw [ReorderedBRetapeResearch.middle_eq cm.out s m hz hb hi ha]
  have old:=cmReady (tape m)
  refine ⟨?_,old.2⟩
  change regValue (ReorderedBPrefixResearch.ga.take 161) _=_
  rw [regValue_take_mod ReorderedBPrefixResearch.ga 161 (by rw [LowAccCarryDevelop.ga_length];decide),old.1,
   Nat.mod_eq_of_lt (ReorderedBPrefixResearch.word_bound s.basis)]
 have eq:middleState newBuild ReorderedBMiddlePatchesResearch.output s m=middleState newBuild cm.out s m:=by
  rw [ReorderedBRetapeResearch.middle_eq _ s m hz hb hi ha,
   ReorderedBRetapeResearch.middle_eq _ s m hz hb hi ha,hcm]
  exact BCachedBuildFrameResearch.plain_middle_eq s (tape m) hc hz hb hi ha
   (zero _ List.mem_cons_self) z88
 rw [eq]
 exact ready


end ECDSAAdd.Entrant.BRelocatedReadyResearch

end

-- Verified B95 optimization component B95Middle (semantic)
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95MiddleResearch
open BShortGhostFactsResearch BShortGhostProgramsResearch B95FactsResearch B95RetimeResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem run_erased(s:State)(m:List Bool)
 (q0:s.basis 4757=false)(q1:s.basis 4758=false)(q2:s.basis 4759=false)
 (ci:s.basis 4760=false)(fl:s.basis 4762=false):
 run program m s=erase 4758 (run ReorderedBMiddlePatchesResearch.output m s):=by
 rcases BShortGhostFactsResearch.checked with ⟨ciA,_,_,flA,_,q2A,_,_,_,_,_,_,_,fbm,_,_,_⟩
 have tc:(run a (m.take (measurementCount a)) s).basis 4760=false:=(PairedWritesResearch.preserved 4760 a ciA s _).trans ci
 have tq1:(run a (m.take (measurementCount a)) s).basis 4758=false:=(PairedWritesResearch.preserved 4758 a B95FactsResearch.checked.2.2.2.1 s _).trans q1
 have tq2:(run a (m.take (measurementCount a)) s).basis 4759=false:=(PairedWritesResearch.preserved 4759 a q2A s _).trans q2
 have tf:(run a (m.take (measurementCount a)) s).basis 4762=false:=(PairedWritesResearch.preserved 4762 a flA s _).trans fl
 have eq:∀r,run fastWindow r (run a (m.take (measurementCount a)) s)=run (exchange 4758 4762) [] (run b0 r (run a (m.take (measurementCount a)) s)):=
  fun r=>window_eq (run a (m.take (measurementCount a)) s) r tc tq2 tq1 tf
 have off:4762∉wires b0:=fresh_fixed (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective b 4762
  (by decide) (not_wire b 4762 fbm)
 have hz:∀r,(run b0 r (run a (m.take (measurementCount a)) s)).basis 4762=false:=fun r=>(run_preserves_outside b0 r (run a (m.take (measurementCount a)) s) 4762 off).trans tf
 have h:=window_context a b0 fastWindow gap center suffix 4758 4762 (by decide)
  gap_fresh.1 gap_fresh.2 center_fresh suffix_fresh window_measurements s m eq hz
 have new_shape:program=a++fastWindow++(gap++center++suffix):=by simp only [program,List.append_assoc]
 have one:run program m s=erase 4758 (run B95Q0BaseResearch.program m s):=
  (congrArg (fun P=>run P m s) new_shape).trans
   (h.trans (congrArg (fun P=>erase 4758 (run P m s)) B95FactsResearch.old_shape.symm))
 exact one.trans (congrArg (erase 4758) (B95Q0BaseResearch.equivalent s m q0 ci))

theorem equivalent(s:State)(m:List Bool)
 (q0:s.basis 4757=false)(q1:s.basis 4758=false)(q2:s.basis 4759=false)
 (ci:s.basis 4760=false)(fl:s.basis 4762=false)
 (out:(run ReorderedBMiddlePatchesResearch.output m s).basis 4758=false):
 run program m s=run ReorderedBMiddlePatchesResearch.output m s:=
 (run_erased s m q0 q1 q2 ci fl).trans (erase_eq 4758 _ out)



end ECDSAAdd.Entrant.B95MiddleResearch

end

-- Verified B95 optimization component B95Ready
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95MiddleResearch
open ReorderedBPrefixResearch InverseCarryDevelop
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem maps:acc.getD 0 0=4757 ∧ acc.getD 1 0=4758 ∧ acc.getD 2 0=4759:=by decide +kernel

theorem ready_eq(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run ReorderedBMiddlePatchesResearch.output m s))
 (flag:s.basis 4762=false):run program m s=run ReorderedBMiddlePatchesResearch.output m s:=by
 have zero(i:Nat)(hi:i<3):s.basis (acc.getD i 0)=false:=
  LowWordRecovery.low_register_zero acc s.basis H i (by omega)
   (by have h:=acc_length;omega) before.1
 have out:(run ReorderedBMiddlePatchesResearch.output m s).basis 4758=false:=by
  have h:=LowWordRecovery.low_register_zero acc (run ReorderedBMiddlePatchesResearch.output m s).basis H 1 (by decide)
   (by have h:=acc_length;omega) after.1
  simpa only [maps.2.1] using h
 apply equivalent s m
 · simpa only [maps.1] using zero 0 (by decide)
 · simpa only [maps.2.1] using zero 1 (by decide)
 · simpa only [maps.2.2] using zero 2 (by decide)
 · exact before.2.2.2.2
 · exact flag
 · exact out

end ECDSAAdd.Entrant.B95MiddleResearch

end

-- Verified B95 optimization component B95Aliases (semantic)
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95AliasesResearch
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem equivalent(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run original m s))
 (flag:s.basis 4762=false):run program m s=run original m s:=by
 have eq:run single m s=run original m s:=B95MiddleResearch.ready_eq H s m before after flag
 have stable:∀q∈acc,(run single m s).basis q=s.basis q:=by
  apply (regValue_eq_iff acc _ _).mp
  rw [eq]
  exact after.1.trans before.1.symm
 have q4s: (run single m s).basis 4505=s.basis 4505:=stable _ (by decide +kernel)
 have q5s:(run single m s).basis 4506=s.basis 4506:=stable _ (by decide +kernel)
 have q6s: (run single m s).basis 4507=s.basis 4507:=stable _ (by decide +kernel)
 have val:regValue acc s.basis=4294968272*regValue src s.basis:=by rw [before.2.1];exact before.1
 have cp:=LowWordRecovery.copies acc src s.basis (by rw [acc_length];decide) (by rw [source_length];decide) val
 have c4:s.basis 4505=s.basis 4243:=by
  simpa only [show src.getD 0 0=4243 from by decide +kernel,
   show acc.getD 4 0=4505 from by decide +kernel] using cp.1.symm
 have c5:s.basis 4506=s.basis 4244:=by
  simpa only [show src.getD 1 0=4244 from by decide +kernel,
   show acc.getD 5 0=4506 from by decide +kernel] using cp.2.1.symm
 have c6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243):=by
  have low:s.basis 4245=(s.basis 4507 ^^ s.basis 4505):=by
   simpa only [show src.getD 2 0=4245 from by decide +kernel,
    show acc.getD 6 0=4507 from by decide +kernel,
    show acc.getD 4 0=4505 from by decide +kernel] using cp.2.2
  rw [low,←c4]
  simp [Bool.xor_assoc]
 have h0:4243∉wires single:=B95MiddleResearch.fresh _ (by decide)
 have h1:4244∉wires single:=B95MiddleResearch.fresh _ (by decide)
 have h2:4245∉wires single:=B95MiddleResearch.fresh _ (by decide)
 let t:=run prep m s
 have commute:run single m t=run prep m (run single m s):=
  FreshCXResearch.commute single 4243 4245 h0 h2 s m m
 have equal4:t.basis 4505=t.basis 4243:=by simpa [t,prep,run,writeBit] using c4
 have equal5:t.basis 4506=t.basis 4244:=by simpa [t,prep,run,writeBit] using c5
 have equal6:t.basis 4507=t.basis 4245:=by simpa [t,prep,run,writeBit] using c6
 have restore4:(run single m t).basis 4505=t.basis 4505:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q4s
 have restore5:(run single m t).basis 4506=t.basis 4506:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q5s
 have restore6:(run single m t).basis 4507=t.basis 4507:=by
  rw [commute]
  simpa [t,prep,run,writeBit] using q6s
 have e4:run first m t=run single m t:=
  EqualSourceSwapResearch.rename_swap_equal_eq single 4505 4243 h0 t m equal4 restore4
 have fresh1:4244∉wires first:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4505 4243)
  (Equiv.swap 4505 4243).injective single 4244 (by decide) h1
 have e5:run second m t=run single m t:=by
  have last:(run first m t).basis 4506=t.basis 4506:=by rw [e4];exact restore5
  exact (EqualSourceSwapResearch.rename_swap_equal_eq first 4506 4244 fresh1 t m equal5 last).trans e4
 have fresh2a:4245∉wires first:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4505 4243)
  (Equiv.swap 4505 4243).injective single 4245 (by decide) h2
 have fresh2:4245∉wires second:=BShortGhostProgramsResearch.fresh_fixed (Equiv.swap 4506 4244)
  (Equiv.swap 4506 4244).injective first 4245 (by decide) fresh2a
 have e6:run aliased m t=run single m t:=by
  have last:(run second m t).basis 4507=t.basis 4507:=by rw [e5];exact restore6
  exact (EqualSourceSwapResearch.rename_swap_equal_eq second 4507 4245 fresh2 t m equal6 last).trans e5
 have mp:measurementCount prep=0:=by simp [prep,measurementCount]
 rw [program,run_cat,run_cat]
 simp only [measurementCount_append,mp,Nat.zero_add,List.drop_zero]
 change run prep (m.drop (measurementCount aliased)) (run aliased m t)=_
 rw [e6,commute]
 exact (FreshCXResearch.twice 4243 4245 (by decide) (run single m s) m _).trans eq

end ECDSAAdd.Entrant.B95AliasesResearch

end

-- Verified B95 optimization component B95LowErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95LowEraseResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def low:List Wire:=[4505,4506,4507]
def erase(s:State):State:=EraseListProof.erase low s
def clear:Program:=[.CX 4243 4505,.CX 4244 4506,.CX 4245 4507,.CX 4243 4507]

theorem clear_eq_erase(s:State)(m:List Bool)
 (h4:s.basis 4505=s.basis 4243)(h5:s.basis 4506=s.basis 4244)
 (h6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243)):
 run clear m s=erase s:=by
 apply State.extensionality
 · simp [clear,run,erase,EraseListProof.phase]
 · funext q
   by_cases hq:q=4505
   · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h4]
   · by_cases hq5:q=4506
     · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h5]
     · by_cases hq6:q=4507
       · subst q
         cases a:s.basis 4243 <;>cases b:s.basis 4245 <;>
          simp_all [clear,run,erase,EraseListProof.basis,low,writeBit]
       · simp [clear,run,erase,EraseListProof.basis,low,writeBit,hq,hq5,hq6]

theorem restore(s:State)(m:List Bool)
 (h4:s.basis 4505=s.basis 4243)(h5:s.basis 4506=s.basis 4244)
 (h6:s.basis 4507=(s.basis 4245 ^^ s.basis 4243)):
 run clear m (erase s)=s:=by
 apply State.extensionality
 · simp [clear,run,erase,EraseListProof.phase]
 · funext q
   by_cases hq:q=4505
   · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h4]
   · by_cases hq5:q=4506
     · subst q;simp [clear,run,erase,EraseListProof.basis,low,writeBit,h5]
     · by_cases hq6:q=4507
       · subst q
         cases a:s.basis 4243 <;>cases b:s.basis 4245 <;>
          simp_all [clear,run,erase,EraseListProof.basis,low,writeBit]
       · simp [clear,run,erase,EraseListProof.basis,low,writeBit,hq,hq5,hq6]

theorem commute(P:Program)(m:List Bool)(s:State)(off:∀q∈low,q∉wires P):
 run P m (erase s)=erase (run P m s):=EraseListProof.commute low P m s off

theorem bit_same(s:State)(q:Wire)(off:q∉low):(erase s).basis q=s.basis q:=by
 simp [erase,EraseListProof.basis,off]





theorem zero(s:State)(q:Wire)(hq:q∈low):(erase s).basis q=false:=by
 simp [erase,EraseListProof.basis,hq]

theorem counts:toffoliCount clear=0 ∧ measurementCount clear=0 ∧ Challenge.gateSlots clear=4:=by decide +kernel

theorem physical:GatePhysical clear:=by simp [GatePhysical,clear,RecordedQuantum.PhysicalInstr,ProperGate]


end ECDSAAdd.Entrant.B95LowEraseResearch

end

-- Verified B95 optimization component B95LowErasedComposition
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95LowEraseResearch
open InverseCarryDevelop ReorderedBPrefixResearch ControlledBorrowResearch
set_option autoImplicit false

set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

theorem aliases_erased(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank cin src H s)
 (after:WReady acc pad bank cin src H (run ReorderedBMiddlePatchesResearch.output m s))
 (flag:s.basis 4762=false):
 run B95AliasesResearch.program m (erase s)=erase (run ReorderedBMiddlePatchesResearch.output m s):=by
 have off:∀q∈low,q∉wires B95AliasesResearch.program:=by
  intro q hq
  simp only [low,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl
  · exact B95AliasesResearch.low4_free
  · exact B95AliasesResearch.low5_free
  · exact B95AliasesResearch.low6_free
 rw [commute _ m s off,B95AliasesResearch.equivalent H s m before after flag]

theorem forward_erased(head P:Program)(s:State)(m:List Bool)
 (off:∀q∈low,q∉wires P)
 (h4:(run head m s).basis 4505=(run head m s).basis 4243)
 (h5:(run head m s).basis 4506=(run head m s).basis 4244)
 (h6:(run head m s).basis 4507=((run head m s).basis 4245 ^^ (run head m s).basis 4243)):
 run (head++clear++P) m s=erase (run (head++P) m s):=by
 have mc:measurementCount clear=0:=counts.2.1
 simp only [run_cat,measurementCount_append,mc,Nat.add_zero]
 rw [clear_eq_erase _ _ h4 h5 h6,commute P _ _ off]

theorem suffix(P:Program)(s:State)(m:List Bool)(off:∀q∈low,q∉wires P)
 (h4:(run P m s).basis 4505=(run P m s).basis 4243)
 (h5:(run P m s).basis 4506=(run P m s).basis 4244)
 (h6:(run P m s).basis 4507=((run P m s).basis 4245 ^^ (run P m s).basis 4243)):
 run (P++clear) m (erase s)=run P m s:=by
 rw [run_cat,commute P m s off]
 exact restore _ _ h4 h5 h6


end ECDSAAdd.Entrant.B95LowEraseResearch

end


end

/-! ## LT41 fitpack: 90 stair part(s) appended (topological order) -/
-- LT41 fitpack: register every namespace the appended parts `open` (empty blocks)
namespace ECDSAAdd
end ECDSAAdd
namespace ECDSAAdd.Entrant.StairOuterPlacement
end ECDSAAdd.Entrant.StairOuterPlacement
namespace ECDSAAdd.Entrant.StairPhysicalInventory
end ECDSAAdd.Entrant.StairPhysicalInventory
namespace ECDSAAdd.Entrant.StairPhysicalLayout
end ECDSAAdd.Entrant.StairPhysicalLayout
namespace ECDSAAdd.Entrant.StairPhysicalPrimitives
end ECDSAAdd.Entrant.StairPhysicalPrimitives
namespace ECDSAAdd.Entrant.InverseCarryDevelop
end ECDSAAdd.Entrant.InverseCarryDevelop
namespace ThirdSavedCarryDevelop
end ThirdSavedCarryDevelop
namespace ECDSAAdd.Entrant.ControlLoan1589BFFold
end ECDSAAdd.Entrant.ControlLoan1589BFFold
namespace ManyACarryDevelop
end ManyACarryDevelop
namespace ECDSAAdd.Entrant.FullBTemp
end ECDSAAdd.Entrant.FullBTemp
namespace ZeroReadDevelop
end ZeroReadDevelop
namespace FourthASavedCarryDevelop
end FourthASavedCarryDevelop
namespace ECDSAAdd.Entrant.LowAccCarryDevelop
end ECDSAAdd.Entrant.LowAccCarryDevelop
namespace ECDSAAdd.Entrant.CarryWindowCache
end ECDSAAdd.Entrant.CarryWindowCache
namespace ECDSAAdd.Entrant.SecondCarryLoan
end ECDSAAdd.Entrant.SecondCarryLoan
namespace ECDSAAdd.Entrant.ThirdCarryLoanDevelop
end ECDSAAdd.Entrant.ThirdCarryLoanDevelop
namespace ECDSAAdd.Entrant.FourthCarryLoanDevelop
end ECDSAAdd.Entrant.FourthCarryLoanDevelop
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
end ECDSAAdd.Entrant.LowBitCarryDevelop
namespace ECDSAAdd.Entrant.ParkCarry7Develop
end ECDSAAdd.Entrant.ParkCarry7Develop
namespace ECDSAAdd.Entrant.ParkCarry10Develop
end ECDSAAdd.Entrant.ParkCarry10Develop
namespace ECDSAAdd.Entrant
end ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSquareBMapped
end ECDSAAdd.Entrant.StairSquareBMapped
namespace ECDSAAdd.Entrant.StairSquareBEFold
end ECDSAAdd.Entrant.StairSquareBEFold
namespace ECDSAAdd.Entrant.StairSquareBChecks.LT48B
end ECDSAAdd.Entrant.StairSquareBChecks.LT48B
namespace ECDSAAdd.Entrant.StairSquareBChecks
end ECDSAAdd.Entrant.StairSquareBChecks
namespace ECDSAAdd.Entrant.StairSquareDirectFold
end ECDSAAdd.Entrant.StairSquareDirectFold
namespace ECDSAAdd.Entrant.ReorderedAFixed
end ECDSAAdd.Entrant.ReorderedAFixed
namespace ECDSAAdd.Entrant.A161Low4Ghost
end ECDSAAdd.Entrant.A161Low4Ghost
namespace ECDSAAdd.Entrant.OwnDiagAll12Square
end ECDSAAdd.Entrant.OwnDiagAll12Square
namespace ECDSAAdd.Entrant.ReorderedCFixed
end ECDSAAdd.Entrant.ReorderedCFixed
namespace ECDSAAdd.Entrant.C163Low4Middle
end ECDSAAdd.Entrant.C163Low4Middle
namespace ECDSAAdd.Entrant.C163Low4Ghost
end ECDSAAdd.Entrant.C163Low4Ghost
namespace ECDSAAdd.Entrant.ReorderedBPrefixResearch
end ECDSAAdd.Entrant.ReorderedBPrefixResearch
namespace ECDSAAdd.Entrant.StairSquareContract
end ECDSAAdd.Entrant.StairSquareContract
namespace ECDSAAdd.Entrant.W.NativeFirstDirect
end ECDSAAdd.Entrant.W.NativeFirstDirect
namespace ECDSAAdd.Entrant.E1QubitPlacement
end ECDSAAdd.Entrant.E1QubitPlacement
namespace ECDSAAdd.Entrant.E1ReflectedPlacement
end ECDSAAdd.Entrant.E1ReflectedPlacement
namespace ECDSAAdd.Entrant.StairSquareHolesCore
end ECDSAAdd.Entrant.StairSquareHolesCore
namespace ECDSAAdd.Entrant.R2SqEp760
end ECDSAAdd.Entrant.R2SqEp760
namespace ECDSAAdd.Entrant.StairSquareKernel26
end ECDSAAdd.Entrant.StairSquareKernel26
namespace ECDSAAdd.Entrant.StairSquareAssembly
end ECDSAAdd.Entrant.StairSquareAssembly
namespace ECDSAAdd.Entrant.OB5
end ECDSAAdd.Entrant.OB5
namespace ECDSAAdd.Entrant.Rolling1588.Integer
end ECDSAAdd.Entrant.Rolling1588.Integer
namespace ECDSAAdd.Entrant.StairConcreteAssembly
end ECDSAAdd.Entrant.StairConcreteAssembly
namespace ECDSAAdd.Entrant.StairField2V3Replay
end ECDSAAdd.Entrant.StairField2V3Replay
namespace ECDSAAdd.Entrant.StairField2V3Couple
end ECDSAAdd.Entrant.StairField2V3Couple
namespace ECDSAAdd.Entrant.StairField2V3Entry
end ECDSAAdd.Entrant.StairField2V3Entry
namespace ECDSAAdd.Entrant.StairField2V3ExitAlgebra
end ECDSAAdd.Entrant.StairField2V3ExitAlgebra
namespace ECDSAAdd.Entrant.StairField2V3ExitPlan
end ECDSAAdd.Entrant.StairField2V3ExitPlan
namespace ECDSAAdd.Entrant.StairField2V3Delta
end ECDSAAdd.Entrant.StairField2V3Delta
namespace ECDSAAdd.Entrant.StairField2V3Seg
end ECDSAAdd.Entrant.StairField2V3Seg
namespace ECDSAAdd.Entrant.StairField2V3ExitPlanR
end ECDSAAdd.Entrant.StairField2V3ExitPlanR
namespace ECDSAAdd.Entrant.StairField2V3End
end ECDSAAdd.Entrant.StairField2V3End
namespace ECDSAAdd.Entrant.StairField2V3Codec
end ECDSAAdd.Entrant.StairField2V3Codec
namespace ECDSAAdd.Entrant.StairField2V3Unpack
end ECDSAAdd.Entrant.StairField2V3Unpack
namespace ECDSAAdd.Entrant.StairField2V3Pack
end ECDSAAdd.Entrant.StairField2V3Pack
namespace ECDSAAdd.Entrant.StairField2V3Decode
end ECDSAAdd.Entrant.StairField2V3Decode
namespace ECDSAAdd.Entrant.StairField2V3Walk
end ECDSAAdd.Entrant.StairField2V3Walk
namespace ECDSAAdd.Entrant.StairField2V3SegFacts
end ECDSAAdd.Entrant.StairField2V3SegFacts
namespace ECDSAAdd.Entrant.StairField2V3SegFacts2
end ECDSAAdd.Entrant.StairField2V3SegFacts2
namespace ECDSAAdd.Entrant.StairField2V3ExitStepsR
end ECDSAAdd.Entrant.StairField2V3ExitStepsR
namespace ECDSAAdd.Entrant.StairField2V3RecScratch
end ECDSAAdd.Entrant.StairField2V3RecScratch
namespace ECDSAAdd.Entrant.StairField2V3Final
end ECDSAAdd.Entrant.StairField2V3Final
namespace ECDSAAdd.Entrant.StairField2V3SegSpec
end ECDSAAdd.Entrant.StairField2V3SegSpec
namespace ECDSAAdd.Entrant.StairField2V3JuncRecord
end ECDSAAdd.Entrant.StairField2V3JuncRecord
namespace ECDSAAdd.Entrant.StairField2V3JuncRefWalk
end ECDSAAdd.Entrant.StairField2V3JuncRefWalk
namespace ECDSAAdd.Entrant.StairField2V3JuncSel
end ECDSAAdd.Entrant.StairField2V3JuncSel
namespace ECDSAAdd.Entrant.StairField2V3LastStage
end ECDSAAdd.Entrant.StairField2V3LastStage
namespace ECDSAAdd.Entrant.StairField2V3EntryPlanR
end ECDSAAdd.Entrant.StairField2V3EntryPlanR
namespace ECDSAAdd.Entrant.StairField2V3ExitRec
end ECDSAAdd.Entrant.StairField2V3ExitRec
namespace ECDSAAdd.Entrant.StairField2V3LastTraj
end ECDSAAdd.Entrant.StairField2V3LastTraj
namespace ECDSAAdd.Entrant.StairField2V3LastSpec
end ECDSAAdd.Entrant.StairField2V3LastSpec
namespace ECDSAAdd.Entrant.StairField2V3LastRecXPar
end ECDSAAdd.Entrant.StairField2V3LastRecXPar
namespace ECDSAAdd.Entrant.StairLoanRecordShape
end ECDSAAdd.Entrant.StairLoanRecordShape
namespace ECDSAAdd.Entrant.StairLoanField7Values
end ECDSAAdd.Entrant.StairLoanField7Values
namespace ECDSAAdd.Entrant.StairLoanField7Transport
end ECDSAAdd.Entrant.StairLoanField7Transport
namespace ECDSAAdd.Entrant.StairRestSupport
end ECDSAAdd.Entrant.StairRestSupport
namespace ECDSAAdd.Entrant.StairField13V3
end ECDSAAdd.Entrant.StairField13V3
namespace ECDSAAdd.Entrant.StairLoanExitReachX
end ECDSAAdd.Entrant.StairLoanExitReachX
namespace ECDSAAdd.Entrant.StairSiteAvoidance
end ECDSAAdd.Entrant.StairSiteAvoidance
namespace ECDSAAdd.Entrant.E1Merge
end ECDSAAdd.Entrant.E1Merge
namespace ECDSAAdd.Entrant.E1WholeKAdd52Research
end ECDSAAdd.Entrant.E1WholeKAdd52Research
namespace ECDSAAdd.Entrant.StairPhysicalPhase
end ECDSAAdd.Entrant.StairPhysicalPhase

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField13V3ChkPhaseX_at_BOptimizations` -/
section Merge_StairField13V3ChkPhaseX_at_BOptimizations

/-!
# Field 13 on v3: kernel checks for `EntryClean` / `ExitClean` (LT29): phase pieces and packet encoders

`decide +kernel` evaluations of the static zero tracker `ztAll`
(`StairField13V3ZT`) on packet-sized programs in their own unrenamed
coordinates.  No program run is evaluated.  One small module per group of
checks, importing only the module that defines the checked programs, so the
checks run in parallel early in the build.
-/

section

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ECDSAAdd.Entrant.StairField13V3Clean

open ECDSAAdd Arithmetic Challenge MappedCompressed







set_option maxHeartbeats 0 in
theorem chk_keep_merged6 : ztAll 736 45 true (rolesL)
    (Six505.merged6) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chk_keep_packP : ztAll 736 45 true (rolesL)
    (Six505.packP false) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem chk_keep_after : ztAll 736 45 true (rolesL)
    (ForwardSixPlacement.after false) = true := by
  decide +kernel


end ECDSAAdd.Entrant.StairField13V3Clean

end
end Merge_StairField13V3ChkPhaseX_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairEarlyCore_at_BOptimizations` -/
section Merge_StairEarlyCore_at_BOptimizations

/-!
# Early core (LT27 critical-path split)

Declarations moved VERBATIM (same fully-qualified names) from late modules so that the
placement chain (StairOuterPlacement, StairPhysicalInventory, StairPhysicalLayout, StairPhysicalPrimitives, StairPhysicalPhase, StairPhysicalPrimitivesFix505) no longer waits for MainRecord.
Generated by LT27 tools/cp_split.py.
-/

section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace ECDSAAdd.Entrant.StairLoanAdapter

open ECDSAAdd Arithmetic
open MappedCompressed Secp256k1 BalancedField


end ECDSAAdd.Entrant.StairLoanAdapter

namespace ECDSAAdd.Entrant.StairGroups

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField





end ECDSAAdd.Entrant.StairGroups

namespace ECDSAAdd.Entrant.StairHoleSupport

open Arithmetic Challenge MappedCompressed










end ECDSAAdd.Entrant.StairHoleSupport

namespace ECDSAAdd.Entrant.StairSchedule

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed DirectSkywalk



end ECDSAAdd.Entrant.StairSchedule

namespace ECDSAAdd.Entrant.StairHoleSupport

open Arithmetic Challenge MappedCompressed


end ECDSAAdd.Entrant.StairHoleSupport

namespace ECDSAAdd.Entrant.StairInventory

open ECDSAAdd Arithmetic Challenge
open MappedCompressed



end ECDSAAdd.Entrant.StairInventory

namespace ECDSAAdd.Entrant.StairReplay

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField

/-- Selected placed ticks with the packet write due after each tick.  Unlike
the record block, both the tick and its packet operation use the moved map. -/
def movedForward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n + 1 =>
      (ECDSAAdd.Entrant.TickRanges.tick w i ++
        Rolling1588.Integer.packFirst w true i) ++ movedForward w (i + 1) n

/-- Receiver mirror of `movedForward`. -/
def movedReverse (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n + 1 =>
      movedReverse w (i + 1) n ++
        (Rolling1588.Integer.unpackFirst w true i ++
          W.ReverseCarry.compactReceiverTick w i)

end ECDSAAdd.Entrant.StairReplay

namespace ECDSAAdd.Entrant.StairSchedule

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed DirectSkywalk



end ECDSAAdd.Entrant.StairSchedule

end
end Merge_StairEarlyCore_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairPhysicalPrimitives_at_BOptimizations` -/
section Merge_StairPhysicalPrimitives_at_BOptimizations

/-!
# Physical primitive provider for the omittable-44 staircase

The checkpoint codec, its sign extension and rest relocation, the first
moved tick, and the moved middle segments, all placed by
`StairPhysicalLayout`.  `physicalPrimitives_good` proves that every wire of
every primitive of every row is a good site: its final placement is in the
record arena and is neither one of the 15 old omissions nor one of the 44 new
omissions.  This is the moved-segment/codec part of the final `insideArena`,
`oldFree`, and `newFree` obligations.

The packet writes inside a moved segment are bounded exactly by their ten
history wires (`MeasuredCodec5.support_exact`), not by the whole Skywalk pool.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairPhysicalPrimitives

open ECDSAAdd Arithmetic Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open StairOuterPlacement StairPhysicalInventory StairPhysicalLayout

/-! ## Exact packet support -/





/-! ## Fine support of moved segments -/

theorem tick_layout (w : Nat → Wire) (i : Nat) (hi : i < 512)
    (hn : (skywalkPoolWires w).Nodup) (q : Wire)
    (hq : q ∈ wires (TickRanges.tick w i)) :
    q ∈ (W.compactSkywalkTickLayout w i).wires :=
  List.mem_toFinset.mp
    (((TickRanges.tick_support w i hi hn).trans
      (W.repairedTick_support w i hi hn)) hq)


theorem movedForward_sub (w : Nat → Wire) (S : List Wire)
    (hn : (skywalkPoolWires w).Nodup) : ∀ n i, i + n ≤ 512 → 5 < i →
      (∀ j, i ≤ j → j < i + n →
        ∀ q ∈ (W.compactSkywalkTickLayout w j).wires, q ∈ S) →
      (∀ j, i ≤ j → j < i + n → History5.packDue j = true →
        ∀ k : Fin 10, History5.historyMap w (j - 5) k ∈ S) →
      ∀ q ∈ wires (StairReplay.movedForward w i n), q ∈ S := by
  intro n
  induction n with
  | zero =>
      intro i _ _ _ _ q hq
      simp [StairReplay.movedForward, wires] at hq
  | succ n ih =>
      intro i hb h5 ticks packs q hq
      simp only [StairReplay.movedForward, wires_append, Finset.mem_union] at hq
      rcases hq with (tick | packet) | rest
      · exact ticks i le_rfl (by omega) q (tick_layout w i (by omega) hn q tick)
      · obtain ⟨due, k, rfl⟩ := packFirst_wires w i (by omega) q packet
        exact packs i le_rfl (by omega) due k
      · exact ih (i + 1) (by omega) (by omega)
          (fun j h1 h2 => ticks j (by omega) (by omega))
          (fun j h1 h2 => packs j (by omega) (by omega)) q rest

theorem movedReverse_sub (w : Nat → Wire) (S : List Wire)
    (hn : (skywalkPoolWires w).Nodup) : ∀ n i, i + n ≤ 512 → 5 < i →
      (∀ j, i ≤ j → j < i + n →
        ∀ q ∈ (W.compactSkywalkTickLayout w j).wires, q ∈ S) →
      (∀ j, i ≤ j → j < i + n → History5.packDue j = true →
        ∀ k : Fin 10, History5.historyMap w (j - 5) k ∈ S) →
      ∀ q ∈ wires (StairReplay.movedReverse w i n), q ∈ S := by
  intro n
  induction n with
  | zero =>
      intro i _ _ _ _ q hq
      simp [StairReplay.movedReverse, wires] at hq
  | succ n ih =>
      intro i hb h5 ticks packs q hq
      simp only [StairReplay.movedReverse, wires_append, Finset.mem_union] at hq
      rcases hq with rest | (packet | tick)
      · exact ih (i + 1) (by omega) (by omega)
          (fun j h1 h2 => ticks j (by omega) (by omega))
          (fun j h1 h2 => packs j (by omega) (by omega)) q rest
      · obtain ⟨due, k, rfl⟩ := unpackFirst_wires w i (by omega) q packet
        exact packs i le_rfl (by omega) due k
      · exact ticks i le_rfl (by omega) q (receiver_layout w i (by omega) hn q tick)

/-! ## Middle-segment map

The first moved tick reads its previous letter from a zero wire (`segmentMap`).
The middle ticks never touch that id, but the record stage invariant used by
the middle replay (`Rolling1588.Integer.Stage`) locates the last record packet
through it, so the middle map sends `start - 1` to the real letter
`base (start - 1)` (LT14 audit item H). -/









/- LT6 (benchmark replay budget): the unreferenced `midSegmentMap_previous`
(`∀ B ∈ budgets, midSegmentMap B (startFor B - 1) = base (startFor B - 1)`, six
`decide +kernel`, ≈ 150 s — LT27 profile b14) is omitted; restore it from
CANON_OUT/Entrant_1823 if needed. -/





/-! ## The provider -/






def tickForward (i : Nat) : Program := TickRanges.tick (segmentMap (512 - i)) i


def middleForward (i n : Nat) : Program :=
  StairReplay.movedForward (midSegmentMap (segmentOf i)) i n

def middleReverse (i n : Nat) : Program :=
  StairReplay.movedReverse (midSegmentMap (segmentOf i)) i n

-- (LT27 cp_split: `physicalPrimitives` moved to StairPhysicalPrimitivesInst)

/-! ## Static row facts -/

/-! K4-B (replay budget): the moved ticks and packets of a row only read pool ids in four
intervals (letters, b-rail, histories, carries); the row map sends each of them to a row site
(`kbSeg_row`, structural), so no tick or packet is evaluated. -/





























/-! K4-B (replay budget): `relocate` / `unrelocate` only move rail bits `D i ↔ S i`, `i < B`,
which are declared row sites; proved structurally instead of by evaluation. -/









/-! ## Every primitive wire is a row site -/














theorem tickForward_rows : ∀ B ∈ budgets,
    ∀ q ∈ wires (tickForward (startFor B)), q ∈ rowSitesL B := by
  intro B hB q hq
  obtain ⟨s1, -, -, s4, -, s6⟩ := budget_shape B hB
  unfold tickForward at hq
  rw [s1] at hq
  apply List.mem_cons_of_mem
  exact tick_rowSites B hB (startFor B) s6 le_rfl q
    (tick_layout _ _ (by omega) (segmentMap_pool_nodup B hB) q hq)


theorem middleForward_rows : ∀ B ∈ budgets,
    ∀ q ∈ wires (middleForward (startFor B + 1) (endFor B - startFor B - 1)),
      q ∈ rowSitesL B := by
  intro B hB q hq
  obtain ⟨-, s2, s3, s4, s5, s6⟩ := budget_shape B hB
  unfold middleForward at hq
  rw [s2] at hq
  apply List.mem_cons_of_mem
  exact movedForward_sub (midSegmentMap B) (rowSites B) (midSegmentMap_pool_nodup B hB)
    _ _ (by omega) s5
    (fun j h1 h2 => midTick_rowSites B hB j (by omega) (by omega))
    (fun j h1 h2 due => midPacket_rowSites B hB j (by omega) (by omega) due) q hq

theorem middleReverse_rows : ∀ B ∈ budgets,
    ∀ q ∈ wires (middleReverse (startFor B + 1) (endFor B - startFor B - 1)),
      q ∈ rowSitesL B := by
  intro B hB q hq
  obtain ⟨-, s2, s3, s4, s5, s6⟩ := budget_shape B hB
  unfold middleReverse at hq
  rw [s2] at hq
  apply List.mem_cons_of_mem
  exact movedReverse_sub (midSegmentMap B) (rowSites B) (midSegmentMap_pool_nodup B hB)
    _ _ (by omega) s5
    (fun j h1 h2 => midTick_rowSites B hB j (by omega) (by omega))
    (fun j h1 h2 due => midPacket_rowSites B hB j (by omega) (by omega) due) q hq

/-- The wires of all placed primitives of a re-planned row. -/
def PrimitiveWire (B : Nat) (q : Wire) : Prop :=
  q ∈ wires (pack B) ∨ q ∈ wires (unpack B) ∨
    q ∈ wires (orient (startFor B)) ∨
    q ∈ wires (tickForward (startFor B)) ∨
    q ∈ wires (tickReverse (startFor B)) ∨
    q ∈ wires (middleForward (startFor B + 1) (endFor B - startFor B - 1)) ∨
    q ∈ wires (middleReverse (startFor B + 1) (endFor B - startFor B - 1))

theorem primitive_rows : ∀ B ∈ budgets, ∀ q, PrimitiveWire B q → q ∈ rowSitesL B := by
  intro B hB q hq
  rcases hq with h | h | h | h | h | h | h
  · exact pack_rows B hB q h
  · exact unpack_rows B hB q h
  · exact orient_rows B hB q h
  · exact tickForward_rows B hB q h
  · exact tickReverse_rows B hB q h
  · exact middleForward_rows B hB q h
  · exact middleReverse_rows B hB q h


/-- Field 8 / LT11 contract: the kernel label (`fieldPlace`) of every wire of
every placed primitive is in the caller domain; in particular no primitive
touches a shadow label of `segMap`. -/
theorem physicalPrimitives_caller : ∀ B ∈ budgets, ∀ q, PrimitiveWire B q →
    fieldPlace q ∈ callerList := by
  intro B hB q hq
  exact rowSitesL_caller B hB q (primitive_rows B hB q hq)



end ECDSAAdd.Entrant.StairPhysicalPrimitives

end
end Merge_StairPhysicalPrimitives_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3MidFwd_at_BOptimizations` -/
section Merge_StairField2V3MidFwd_at_BOptimizations

/-!
# Moved middle round trip (LT24; ported verbatim from LT14's
`StairNamedReplay`, built there on CANON 1319)

`movedMiddle_roundtrip`: on a genuine `Rolling1588.Integer.Stage w true x p i`
state, the moved receiver block `StairReplay.movedReverse w i n` undoes the
moved forward block `StairReplay.movedForward w i n`, for independent tapes.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3MidFwd

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField

theorem integer_tick_run_eq (w : Nat → Wire) (isA : Bool)
    (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0 < x) (hx : x < p) (hcop : x.Coprime p)
    (hi : i < 512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage w isA x p i s.basis) :
    run (TickRanges.tick w i) m s = run (W.repairedTick w i) m s := by
  obtain ⟨raw, rawStage, bits⟩ := stage
  have dis := Rolling1588.Integer.prefix_disjoint_layout w isA hn i i
    (Nat.le_refl i) hi
  have read : ∀ q ∈ (W.compactSkywalkTickLayout w i).wires.toFinset,
      s.basis q = raw.basis q := by
    intro q hq
    rw [bits]
    exact run_preserves_outside _ _ _ q
      (fun used => Finset.disjoint_left.mp dis used hq)
  have old := W.repairedTick_support w i hi hn
  have fresh := (TickRanges.tick_support w i hi hn).trans old
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (TickRanges.tick_eq w hn x i hx0 hx hcop hi raw m rawStage)

theorem integer_block_run_eq (w : Nat → Wire) (isA : Bool)
    (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hodd : p % 2 = 1)
    (hp : p < 2 ^ 256) (hgap : p + 2 ^ 32 ≤ 2 ^ 256)
    (hx : x < p) (hcop : x.Coprime p)
    (hi0 : 385 ≤ i) (hi1 : i < 512)
    (s : State) (fresh old : List Bool)
    (stage : Rolling1588.Integer.Stage w isA x p i s.basis) :
    run (TickRanges.tick w i ++ Rolling1588.Integer.packFirst w isA i)
        fresh s =
      run (W.repairedTick w i ++ Rolling1588.Integer.packAfter w isA i)
        old s := by
  have sameTape :
      run (TickRanges.tick w i ++ Rolling1588.Integer.packFirst w isA i)
          fresh s =
        run (W.repairedTick w i ++ Rolling1588.Integer.packFirst w isA i)
          fresh s := by
    rw [run_append (TickRanges.tick w i),
      run_append (W.repairedTick w i),
      run_take (TickRanges.tick w i), run_take (W.repairedTick w i),
      integer_tick_run_eq w isA hn x i hx0 hx hcop hi1 s fresh stage,
      (TickRanges.tick_counts w i hi1 hn).2]
  have firstIsRegular : Rolling1588.Integer.packFirst w isA i =
      Rolling1588.Integer.packAfter w isA i := by
    simp only [Rolling1588.Integer.packFirst, if_neg (by omega : i ≠ 5)]
  have freshCompact := Rolling1588.Integer.step_eq w isA hn x p i
    hp0 hx0 hodd hp hgap hx hcop hi1 s fresh [] stage
  have oldCompact := Rolling1588.Integer.step_eq w isA hn x p i
    hp0 hx0 hodd hp hgap hx hcop hi1 s old [] stage
  calc
    run (TickRanges.tick w i ++ Rolling1588.Integer.packFirst w isA i)
        fresh s =
        run (W.repairedTick w i ++ Rolling1588.Integer.packFirst w isA i)
          fresh s := sameTape
    _ = run (W.repairedTick w i ++ Rolling1588.Integer.packAfter w isA i)
          fresh s := by rw [firstIsRegular]
    _ = run (W.compactSkywalkTick w i ++
          Rolling1588.Integer.packAfter w isA i) [] s := freshCompact
    _ = run (W.repairedTick w i ++ Rolling1588.Integer.packAfter w isA i)
          old s := oldCompact.symm

/-- Literal selected middle block versus the record's generic unplaced
`regularForward`, with independent tapes. -/
theorem movedForward_run_eq_regular (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (history : History5.HistoryAbove w)
    (x i n : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hodd : p % 2 = 1)
    (hp : p < 2 ^ 256) (hgap : p + 2 ^ 32 ≤ 2 ^ 256)
    (hx : x < p) (hcop : x.Coprime p)
    (hi0 : 385 ≤ i) (bound : i + n ≤ 512)
    (s : State) (fresh old : List Bool)
    (stage : Rolling1588.Integer.Stage w true x p i s.basis) :
    run (StairReplay.movedForward w i n) fresh s =
      run (Rolling1588.Integer.regularForward w true i n) old s := by
  induction n generalizing i s fresh old with
  | zero => rfl
  | succ n ih =>
      let selected := TickRanges.tick w i ++
        Rolling1588.Integer.packFirst w true i
      let reference := W.repairedTick w i ++
        Rolling1588.Integer.packAfter w true i
      let next := run reference (old.take (measurementCount reference)) s
      have first :
          run selected (fresh.take (measurementCount selected)) s = next := by
        change run (TickRanges.tick w i ++
            Rolling1588.Integer.packFirst w true i)
            (fresh.take (measurementCount selected)) s =
          run (W.repairedTick w i ++
            Rolling1588.Integer.packAfter w true i)
            (old.take (measurementCount reference)) s
        exact integer_block_run_eq w true hn x i hp0 hx0 hodd hp hgap
          hx hcop hi0 (by omega) s _ _ stage
      have nextStage :
          Rolling1588.Integer.Stage w true x p (i + 1) next.basis := by
        exact (Rolling1588.Integer.step_spec w true hn history x p i
          hp0 hx0 hodd hp hgap hx hcop (by omega) s
          (old.take (measurementCount reference)) stage).2
      have rest := ih (i + 1) (by omega) (by omega) next
        (fresh.drop (measurementCount selected))
        (old.drop (measurementCount reference)) nextStage
      change run (selected ++ StairReplay.movedForward w (i + 1) n)
          fresh s =
        run (reference ++ Rolling1588.Integer.regularForward w true (i + 1) n)
          old s
      rw [run_append selected, run_append reference]
      rw [first]
      exact rest

end ECDSAAdd.Entrant.StairField2V3MidFwd

end
end Merge_StairField2V3MidFwd_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairPhysicalPrimitivesFix505_at_BOptimizations` -/
section Merge_StairPhysicalPrimitivesFix505_at_BOptimizations

/-!
# Terminal-row reverse middle segment on the extended map (s505 fix)

`StairSchedule.reverseLast` runs `middleReverse 501 5`, i.e. the moved unticks
`505 .. 501` of the terminal row (budget 12).  Its first untick, tick 505, reads
the history letter `s 505` at its moved id `1028 + 505`.  LT13's row map
`midSegmentMap 12 = segMid 500 505` covers histories only through tick 504, so
that id falls to the shadow branch `base (4000 + 1533)`; the multiplication
terminal (`StairTerminalV3.reverseTerminalV3`) leaves `s 505` on `base 1548`
(= `sLetter 505`, the record's wire).

The fix keeps every program except this one segment: the reverse middle map of
a row is `segMid (startFor B) (reverseEnd B)` with `reverseEnd 12 = 506` and
`reverseEnd B = endFor B` for every other row.  The two maps differ only at the
id `1028 + 505` (`revSegmentMap_agree`), which now goes to `base 1548`
(`revSegmentMap_s505`).  Injectivity, pool nodup, history-above, row-site and
caller-domain facts are re-proved for `e ≤ 506`; `physicalPrimitivesFix_good`
and `physicalPrimitivesFix_caller` are LT13's `physicalPrimitives_good` /
`physicalPrimitives_caller` with the terminal reverse segment at its actual
length `reverseEnd B - startFor B - 1` (= 5 for the terminal row).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairPhysicalPrimitivesFix505

open ECDSAAdd Arithmetic Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open StairOuterPlacement StairPhysicalInventory StairPhysicalLayout StairPhysicalPrimitives

/-! ## The extended reverse map -/



/-! ## K4-D (replay budget): injectivity through one left inverse

`segMap l e` and `segMid l e` are decoded by `D505.dec l` (an if-chain on the wire value); the decoding
identity needs one leaf per branch of `segMap` instead of one omega proof per pair of branches. -/
namespace D505















end D505












/-! ## The fixed reverse middle program -/

def middleReverseFix (i n : Nat) : Program :=
  StairReplay.movedReverse (revSegmentMap (segmentOf i)) i n

/-- Identical to LT13's program on every non-terminal row. -/
theorem middleReverseFix_eq (i n : Nat) (h : segmentOf i ≠ 12) :
    middleReverseFix i n = middleReverse i n := by
  simp only [middleReverseFix, middleReverse, revSegmentMap_eq_mid _ h]

-- (LT27 cp_split: `physicalPrimitivesFix` moved to StairPhysicalPrimitivesInst)

/-! ## Row facts for the extended segment -/





theorem middleReverseFix_rows : ∀ B ∈ budgets,
    ∀ q ∈ wires (middleReverseFix (startFor B + 1) (reverseEnd B - startFor B - 1)),
      q ∈ rowSitesL B := by
  intro B hB q hq
  obtain ⟨s2, s3, s4, s5⟩ := budget_shape_rev B hB
  unfold middleReverseFix at hq
  rw [s2] at hq
  apply List.mem_cons_of_mem
  exact movedReverse_sub (revSegmentMap B) (rowSites B) (revSegmentMap_pool_nodup B hB)
    _ _ (by omega) s5
    (fun j h1 h2 => revTick_rowSites B hB j (by omega) (by omega))
    (fun j h1 h2 due => revPacket_rowSites B hB j (by omega) (by omega) due) q hq

/-! ## Good sites and caller domain with the fixed segment -/

/-- LT13's `PrimitiveWire` with the reverse middle segment at its scheduled
length (5 unticks for the terminal row). -/
def PrimitiveWireFix (B : Nat) (q : Wire) : Prop :=
  q ∈ wires (pack B) ∨ q ∈ wires (unpack B) ∨
    q ∈ wires (orient (startFor B)) ∨
    q ∈ wires (tickForward (startFor B)) ∨
    q ∈ wires (tickReverse (startFor B)) ∨
    q ∈ wires (middleForward (startFor B + 1) (endFor B - startFor B - 1)) ∨
    q ∈ wires (middleReverseFix (startFor B + 1) (reverseEnd B - startFor B - 1))

theorem primitiveFix_rows : ∀ B ∈ budgets, ∀ q, PrimitiveWireFix B q → q ∈ rowSitesL B := by
  intro B hB q hq
  rcases hq with h | h | h | h | h | h | h
  · exact pack_rows B hB q h
  · exact unpack_rows B hB q h
  · exact orient_rows B hB q h
  · exact tickForward_rows B hB q h
  · exact tickReverse_rows B hB q h
  · exact middleForward_rows B hB q h
  · exact middleReverseFix_rows B hB q h

/-- Every wire of every placed primitive (fixed terminal reverse segment
included) is inside the final arena and avoids all 59 omissions. -/
theorem physicalPrimitivesFix_good : ∀ B ∈ budgets, ∀ q, PrimitiveWireFix B q →
    place q ∈ StairHoleSupport.recordArena ∧
      place q ∉ StairHoleSupport.oldHoles ∧ place q ∉ physicalHoles := by
  intro B hB q hq
  have good := rowSitesL_good B hB q (primitiveFix_rows B hB q hq)
  rw [recordArena_eq, oldHoles_eq, physicalHoles_eq_nat]
  exact good

/-- Field 8 / LT11 contract with the fixed segment: every primitive wire's kernel
label is in the caller domain; in particular `middleReverseFix 501 5` touches no
shadow label. -/
theorem physicalPrimitivesFix_caller : ∀ B ∈ budgets, ∀ q, PrimitiveWireFix B q →
    fieldPlace q ∈ callerList := by
  intro B hB q hq
  exact rowSitesL_caller B hB q (primitiveFix_rows B hB q hq)

/-- The terminal call itself, as scheduled. -/
theorem terminalReverse_sound : ∀ q ∈ wires (middleReverseFix 501 5),
    (place q ∈ StairHoleSupport.recordArena ∧
      place q ∉ StairHoleSupport.oldHoles ∧ place q ∉ physicalHoles) ∧
      fieldPlace q ∈ callerList := by
  intro q hq
  have hw : PrimitiveWireFix 12 q := by
    have e := terminal_reverse_call
    unfold PrimitiveWireFix
    rw [e.1, e.2]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq)))))
  exact ⟨physicalPrimitivesFix_good 12 (by decide) q hw,
    physicalPrimitivesFix_caller 12 (by decide) q hw⟩

end ECDSAAdd.Entrant.StairPhysicalPrimitivesFix505

end
end Merge_StairPhysicalPrimitivesFix505_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSegment_at_BOptimizations` -/
section Merge_StairSegment_at_BOptimizations

/-!
Checkpoint-local integer walk segments for the stair schedule.

Unlike the full-walk invariant, `Stage` is re-rooted at `start`.  Thus the
first predecessor can be a clean zero and no already-materialized transcript
prefix is required.  The placement map `w` is otherwise arbitrary.
-/

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairSegment

open Arithmetic Secp256k1











/-- K4-B (replay budget): the pre/post tick widths on the late ticks, evaluated once. -/
private theorem kbLateWidth : ∀ j, j < 125 →
    W.compactSkywalkTickPreWidth (385 + j) - 2 + 1 = W.compactSkywalkTickPostWidth (385 + j) := by
  decide +kernel

/-- The re-rooted encoded trajectory supplies the sign facts used by the
entrant's measured late route.  This is the checkpoint-local analogue of the
full-walk `W.compact_late_preconditions` theorem. -/
private theorem late_preconditions (w : Nat → Wire) (start i : Nat)
    (sign : Bool) (z : SkywalkNat.State) (hi0 : 385 ≤ i) (hi1 : i ≤ 509)
    (hn : (skywalkPoolWires w).Nodup) (hz : 0 < z.v) (hzo : z.v%2=1) (s : State)
    (hs : Stage w start (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) i s.basis)
    (fit : Fits i (railAt (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) (i-start))) :
    let L := W.compactSkywalkTickLayout w i
    0 < L.aMid.length ∧ ∃neg : Bool,
      s.basis L.aSign=(s.basis L.previous && neg) ∧
      s.basis L.bSign=(!s.basis L.previous && neg) ∧
      (if s.basis L.a0 then s.basis (L.aMid.getD (L.aMid.length-1) 0)
       else s.basis (L.bMid.getD (L.bMid.length-1) 0))=
      (if s.basis L.a0 then s.basis L.aSign else s.basis L.bSign) := by
  dsimp only
  let L := W.compactSkywalkTickLayout w i
  let ri := railAt (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) (i-start)
  have hlt : i<512 := by omega
  have input := local_input w start i _ hlt s.basis hs
  change SkywalkIntegerInput L ri.a ri.b ri.g s.basis at input
  have hv := W.compactSkywalkTick_valid w i hlt hn
  have width := W.compactSkywalkTick_width_bounds i hlt
  have hpos : 0<L.aMid.length := by
    change 0<(wireBlock w (i+1) (W.compactSkywalkTickPreWidth i-2)).length
    rw [wireBlock_length]
    omega
  have hposB : 0<L.bMid.length := by rw [←hv.mids]; exact hpos
  have lenA : (L.a0::L.aMid).length=W.compactSkywalkTickPostWidth i := by
    change (w i::wireBlock w (i+1) (W.compactSkywalkTickPreWidth i-2)).length=_
    simp only [List.length_cons,wireBlock_length]
    -- K4-B (replay budget): the width identity on `[385, 510)` by one small evaluation
    have hw := kbLateWidth (i - 385) (by omega)
    rw [show 385 + (i - 385) = i by omega] at hw
    omega
  have lenB : (L.b0::L.bMid).length=W.compactSkywalkTickPostWidth i := by
    simp only [List.length_cons] at lenA ⊢
    rw [←hv.mids]
    simpa only [List.length_cons] using lenA
  have sa : s.basis L.aSign=SkywalkRails.neg ri.a := by
    have v := signedRegValue_sign (L.a0::L.aMid) L.aSign s.basis
    change s.basis L.aSign=SkywalkRails.neg (signedRegValue L.a s.basis) at v
    rw [input.1] at v
    exact v
  have sb : s.basis L.bSign=SkywalkRails.neg ri.b := by
    have v := signedRegValue_sign (L.b0::L.bMid) L.bSign s.basis
    change s.basis L.bSign=SkywalkRails.neg (signedRegValue L.b s.basis) at v
    rw [input.2.1] at v
    exact v
  obtain ⟨G,S,henc⟩ := SkywalkTrace.iter_encoded (i-start) false sign z hz hzo
  change ri=SkywalkRails.encode G S
    ((SkywalkNat.step^[i-start] z).u:Int) ((SkywalkNat.step^[i-start] z).v:Int) at henc
  let zi := SkywalkNat.step^[i-start] z
  have enc := W.encoded_signs G S zi.u zi.v
  dsimp only at enc
  change ri=SkywalkRails.encode G S (zi.u:Int) (zi.v:Int) at henc
  rw [←henc] at enc
  have prev : s.basis L.previous=G := by
    rw [input.2.2.1,henc]
    cases G <;> simp [SkywalkRails.encode]
  have firstSign : s.basis L.aSign=
      (s.basis L.previous && SkywalkRails.neg (SkywalkRails.signed S (zi.u:Int))) := by
    rw [prev,sa]
    exact enc.1
  have secondSign : s.basis L.bSign=
      (!s.basis L.previous && SkywalkRails.neg (SkywalkRails.signed S (zi.u:Int))) := by
    rw [prev,sb]
    exact enc.2
  have parity : s.basis L.a0=SkywalkRails.odd ri.a := by
    have v := input.1
    change signedRegValue (L.a0::L.ah) s.basis=ri.a at v
    rw [signedRegValue_cons _ _ _ (by simp [SkywalkIntegerLayout.ah])] at v
    cases h : s.basis L.a0 with
    | false =>
      have e : ri.a%2=0 := by simp [h] at v; omega
      simp [SkywalkRails.odd,e,h]
    | true =>
      have e : ri.a%2≠0 := by simp [h] at v; omega
      simp [SkywalkRails.odd,e,h]
  have lower := fit.otherMin
  have upper := fit.otherMax
  rw [SkywalkRails.route,←parity] at lower upper
  have selected : (if s.basis L.a0 then s.basis (L.aMid.getD (L.aMid.length-1) 0)
      else s.basis (L.bMid.getD (L.bMid.length-1) 0))=
      (if s.basis L.a0 then s.basis L.aSign else s.basis L.bSign) := by
    cases h : s.basis L.a0 with
    | false =>
      simp only [h,Bool.false_eq_true,if_false] at lower upper ⊢
      have v : signedRegValue ((L.b0::L.bMid)++[L.bSign]) s.basis=ri.b := input.2.1
      have ff := W.fitted_sign L.b0 L.bSign L.bMid s.basis ri.b hposB v
        (by simpa only [lenB] using lower) (by simpa only [lenB] using upper)
      exact ff.symm
    | true =>
      simp only [h,if_true] at lower upper ⊢
      have v : signedRegValue ((L.a0::L.aMid)++[L.aSign]) s.basis=ri.a := input.1
      have ff := W.fitted_sign L.a0 L.aSign L.aMid s.basis ri.a hpos v
        (by simpa only [lenA] using lower) (by simpa only [lenA] using upper)
      exact ff.symm
  exact ⟨hpos,⟨SkywalkRails.neg (SkywalkRails.signed S (zi.u:Int)),
    firstSign,secondSign,selected⟩⟩

/-- In the stair range the selected entrant tick is state-equal to the
reference compact tick, for every measurement record. -/
theorem tick_run_eq (w : Nat → Wire) (start i : Nat) (sign : Bool)
    (z : SkywalkNat.State) (hi0 : 385 ≤ i) (hi1 : i ≤ 509)
    (hn : (skywalkPoolWires w).Nodup) (hz : 0 < z.v) (hzo : z.v%2=1)
    (s : State) (m : List Bool)
    (hs : Stage w start (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) i s.basis)
    (fit : Fits i (railAt (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) (i-start))) :
    run (ECDSAAdd.Entrant.TickRanges.tick w i) m s=
      run (W.compactSkywalkTick w i) [] s := by
  let L := W.compactSkywalkTickLayout w i
  have hlt : i<512 := by omega
  have hv := W.compactSkywalkTick_valid w i hlt hn
  obtain ⟨hpos,neg,ha,hb,hf⟩ :=
    late_preconditions w start i sign z hi0 hi1 hn hz hzo s hs fit
  have em := (W.repairedRoute_counts L hv).2
  have om := (skywalkRoute_counts L.a0 L.b0 L.ah L.bh
    (L.high_lengths hv) (L.route_nodup hv)).2
  change measurementCount (W.repairedRoute (W.compactSkywalkTickLayout w i))=1 at em
  change measurementCount (skywalkRoute (W.compactSkywalkTickLayout w i).a0
    (W.compactSkywalkTickLayout w i).b0 (W.compactSkywalkTickLayout w i).ah
    (W.compactSkywalkTickLayout w i).bh)=0 at om
  have band : ¬(225 ≤ i ∧ i ≤ 254) := by omega
  have gap : ¬(255 ≤ i ∧ i ≤ 286) := by omega
  have late : i=224 ∨ (255 ≤ i ∧ i ≤ 509) := by omega
  have trim : ¬W.fwdTrim i := by unfold W.fwdTrim; omega
  have measured : run (ECDSAAdd.Entrant.TickRanges.tick w i) m s=
      run (W.compactSkywalkTick w i) (m.drop 1) s := by
    simp only [ECDSAAdd.Entrant.TickRanges.tick,if_neg band,
      ECDSAAdd.Entrant.TickGap.tick,if_neg gap,
      W.repairedTick,if_neg trim,W.repairedTick0,if_pos late,
      W.compactSkywalkTick,narrowSkywalkTick,List.append_assoc]
    conv_lhs => rw [run_append]
    conv_rhs => rw [run_append]
    simp only [em,om,List.take_zero,List.drop_zero]
    rw [W.repairedRoute_eq L hv hpos s (m.take 1) neg ha hb hf]
  rw [measured]
  have one := compact_step w start i _ (by omega) hn s (m.drop 1) hs fit
  have zero := compact_step w start i _ (by omega) hn s [] hs fit
  apply State.extensionality
  · exact one.1.trans zero.1.symm
  · exact run_basis_records (W.compactSkywalkTick w i) s s (m.drop 1) [] rfl

/-- The selected one-CCX-cheaper tick advances the local exact stage. -/
theorem tick_step (w : Nat → Wire) (start i : Nat) (sign : Bool)
    (z : SkywalkNat.State) (hi0 : 385 ≤ i) (hi1 : i ≤ 509)
    (hn : (skywalkPoolWires w).Nodup) (hz : 0 < z.v) (hzo : z.v%2=1)
    (s : State) (m : List Bool)
    (hs : Stage w start (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) i s.basis)
    (fit : Fits i (railAt (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) (i-start))) :
    (run (ECDSAAdd.Entrant.TickRanges.tick w i) m s).phase=s.phase ∧
      Stage w start (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) (i+1)
        (run (ECDSAAdd.Entrant.TickRanges.tick w i) m s).basis := by
  rw [tick_run_eq w start i sign z hi0 hi1 hn hz hzo s m hs fit]
  exact compact_step w start i _ (by omega) hn s [] hs fit

/-- Forward and reverse stair segments contain arithmetic ticks only: packet
packing is deliberately left to the caller at checkpoint boundaries. -/
def forward (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => ECDSAAdd.Entrant.TickRanges.tick w i++forward w (i+1) n

def reverse (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => reverse w (i+1) n++W.ReverseCarry.compactReceiverTick w i



private theorem roundtrip_from (w : Nat → Wire) (start : Nat) (sign : Bool)
    (z : SkywalkNat.State) (hn : (skywalkPoolWires w).Nodup)
    (hz : 0 < z.v) (hzo : z.v%2=1) (i n : Nat) (hi : 385 ≤ i)
    (hb : i+n ≤ 510)
    (fits : ∀j, i ≤ j → j < i+n →
      Fits j (railAt (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) (j-start)))
    (s : State) (mf mr : List Bool)
    (hs : Stage w start (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) i s.basis) :
    run (reverse w i n) mr (run (forward w i n) mf s)=s := by
  induction n generalizing i s mf mr with
  | zero => rfl
  | succ n ih =>
    let P := ECDSAAdd.Entrant.TickRanges.tick w i
    let F := forward w (i+1) n
    let R := reverse w (i+1) n
    let U := W.ReverseCarry.compactReceiverTick w i
    have f0 := fits i (Nat.le_refl _) (by omega)
    let s1 := run P (mf.take (measurementCount P)) s
    have hs1 : Stage w start (SkywalkRails.encode false sign (z.u:Int) (z.v:Int))
        (i+1) s1.basis :=
      (tick_step w start i sign z hi (by omega) hn hz hzo s
        (mf.take (measurementCount P)) hs f0).2
    have back := ih (i+1) (by omega) (by omega) (by
      intro j hj0 hj1
      exact fits j (by omega) (by omega)) s1 (mf.drop (measurementCount P))
        (mr.take (measurementCount R)) hs1
    have input := local_input w start i _ (by omega) s.basis hs
    have top : W.trimTick i →
        s.basis (w (i+W.compactSkywalkTickPreWidth i-1))=
          s.basis (w (i+W.compactSkywalkTickPreWidth i-2)) ∧
        s.basis (w (770+W.compactSkywalkTickPreWidth i-1))=
          s.basis (w (770+W.compactSkywalkTickPreWidth i-2)) := by
      intro ht
      unfold W.trimTick at ht
      omega
    have one := W.ReverseCarry.compactReceiverTick_roundtrip w i (by omega) hn s []
      (mr.drop (measurementCount R)) input.2.2.2.2.1 input.2.2.2.2.2 top
    have tickEq := tick_run_eq w start i sign z hi (by omega) hn hz hzo s
      (mf.take (measurementCount P)) hs f0
    have one' : run U (mr.drop (measurementCount R)) (run P
        (mf.take (measurementCount P)) s)=s := by
      rw [tickEq]
      exact one
    simp only [forward,reverse,run_append]
    change run U (mr.drop (measurementCount R))
      (run R (mr.take (measurementCount R))
        (run F (mf.drop (measurementCount P)) s1))=s
    rw [back]
    exact one'

/-- The receiver segment is the exact mirror of the forward stair segment,
with independent measurement records in both directions. -/
theorem roundtrip (w : Nat → Wire) (start n : Nat) (sign : Bool)
    (z : SkywalkNat.State) (hn : (skywalkPoolWires w).Nodup)
    (hz : 0 < z.v) (hzo : z.v%2=1) (hi : 385 ≤ start) (hb : start+n ≤ 510)
    (fits : FitsThrough start n
      (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)))
    (s : State) (mf mr : List Bool)
    (hs : Stage w start (SkywalkRails.encode false sign (z.u:Int) (z.v:Int)) start s.basis) :
    run (reverse w start n) mr (run (forward w start n) mf s)=s := by
  apply roundtrip_from w start sign z hn hz hzo start n hi hb
  · intro j hj0 hj1
    have e : j=start+(j-start) := by omega
    rw [e]
    simpa only [Nat.add_sub_cancel_left] using fits (j-start) (by omega)
  · exact hs

/-- Total scheduled saving against the reference compact forward tick. -/
def forwardDue (i : Nat) : Nat :=
  ECDSAAdd.Entrant.TickRanges.due i + W.repairDue i + W.fwdDue i






/-- Every tick strictly between stair checkpoints saves exactly one CCX. -/
theorem forwardDue_eq_one (i : Nat) (hi0 : 385 ≤ i) (hi1 : i ≤ 509) :
    forwardDue i=1 := by
  have band : ¬(225 ≤ i ∧ i ≤ 254) := by omega
  have gap : ¬(255 ≤ i ∧ i ≤ 286) := by omega
  have late : i=224 ∨ (255 ≤ i ∧ i ≤ 509) := by omega
  have nf : ¬W.fwdTrim i := by unfold W.fwdTrim; omega
  simp only [forwardDue,ECDSAAdd.Entrant.TickRanges.due,if_neg band,
    ECDSAAdd.Entrant.TickGap.due,if_neg gap,W.repairDue,if_pos late,
    W.fwdDue,if_neg nf]


theorem forward_tick_counts (w : Nat → Wire) (i : Nat)
    (hi0 : 385 ≤ i) (hi1 : i ≤ 509) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (ECDSAAdd.Entrant.TickRanges.tick w i)=
        (W.compactSkywalkTickPreWidth i-1)+
          (W.compactSkywalkTickPostWidth i-1)-forwardDue i ∧
    measurementCount (ECDSAAdd.Entrant.TickRanges.tick w i)=
        W.compactSkywalkTickPostWidth i-1+W.repairDue i := by
  have a := ECDSAAdd.Entrant.TickRanges.tick_counts w i (by omega) hn
  have b := W.repairedTick_counts w i (by omega) hn
  have c := W.compactSkywalkTick_counts w i (by omega) hn
  have widths := W.compactSkywalkTick_width_bounds i (by omega)
  have due := forwardDue_eq_one i hi0 hi1
  have band : ¬(225 ≤ i ∧ i ≤ 254) := by omega
  have gap : ¬(255 ≤ i ∧ i ≤ 286) := by omega
  have late : i=224 ∨ (255 ≤ i ∧ i ≤ 509) := by omega
  have nf : ¬W.fwdTrim i := by unfold W.fwdTrim; omega
  have td : ECDSAAdd.Entrant.TickRanges.due i=0 := by
    simp only [ECDSAAdd.Entrant.TickRanges.due,if_neg band,
      ECDSAAdd.Entrant.TickGap.due,if_neg gap]
  have rd : W.repairDue i=1 := by simp only [W.repairDue,if_pos late]
  have fd : W.fwdDue i=0 := by simp only [W.fwdDue,if_neg nf]
  rw [td] at a
  rw [rd,fd] at b
  rw [due,rd]
  constructor <;> omega












end ECDSAAdd.Entrant.StairSegment
end Merge_StairSegment_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairFirstTickV3_at_BOptimizations` -/
section Merge_StairFirstTickV3_at_BOptimizations

/-!
# First moved tick on the decoded, oriented checkpoint (LT30)

At each checkpoint row `B` (start `s = startFor B` ∈ {425, 450, 465, 480, 490, 500})
the first moved tick `tickForward s = TickRanges.tick (segmentMap B) s` runs on the
decoded, ORIENTED checkpoint: the previous letter sits on the clean spare 717, and
the two rails are `orientRails (realRails x p s)`, not the record's canonical
stage.  This file proves, for every row:

* `tick_trip` — `tickReverse s ∘ tickForward s = id` on such a checkpoint
  (exit side: LT24 `rowPieces_chain.tick`, `termPieces` link `tick 500`);
* `tick_forward` — the tick advances the re-rooted local stage to `s + 1`;
* `virtual_stage` (naturality) — a local stage at `s + 1` yields a VIRTUAL state
  that agrees with the physical one outside the virtual sites (images under
  `midSegmentMap B` of the past ids `< s`, `1028 + j (j < s)` and `1797`) and
  satisfies the record's `Rolling1588.Integer.Stage (midSegmentMap B) … (s + 1)`;
* `middle_virtual` — the exact `virtual` premise of LT24's `middle_trip_local`
  / `terminal_middle_trip` (agreement on the moved middle programs' wires).

A genuine `Integer.Stage` on the moved map cannot hold physically (the moved
map puts the old letters on clean shadow labels), so the stage is stated on a
virtual state, generically in the row (`virtual_generic`).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairFirstTickV3

open ECDSAAdd Arithmetic
open MappedCompressed StairPhysicalLayout

/-! ## Orientation is invisible after one tick (LT14 `StairScheduleRepair`) -/






/-! ## Record hypotheses and the decoded checkpoint -/




theorem tickForward_eq (B : Nat) (hB : B ∈ budgets) :
    StairPhysicalPrimitives.tickForward (startFor B) =
      TickRanges.tick (segmentMap B) (startFor B) := by
  unfold StairPhysicalPrimitives.tickForward
  rw [(budget_range B hB).2.2.2.1]


/-! ## `Decoded` from the codec output -/



/-! ## The first moved tick: round trip and forward step -/

/-- **Round trip (exit side).** On the decoded oriented checkpoint the moved
untick inverts the moved tick, for independent measurement records. -/
theorem tick_trip (B : Nat) (hB : B ∈ budgets) (x p : Nat) (h : RealHyp x p)
    (y : State) (hy : Decoded B x p y.basis) (c a : List Bool) :
    run (StairPhysicalPrimitives.tickReverse (startFor B)) a
      (run (StairPhysicalPrimitives.tickForward (startFor B)) c y) = y := by
  obtain ⟨h0, h1, _, _, _, _⟩ := budget_range B hB
  have valid := SkywalkNat.iter_valid (startFor B) (SkywalkNat.init x p) h.p0 h.odd
  have fit := StairBridgeDomain.canonical_real_fit x p (startFor B) h.p0 h.x0 h.odd
    h.lt h.gap h.xlt h.cop (by omega)
  unfold Decoded at hy
  rw [StairBridgeDomain.orient_realRails x p _ h.p0 h.odd] at hy
  have round := StairSegment.roundtrip (segmentMap B) (startFor B) 1
    (StairBridgeDomain.realSign x p (startFor B))
    (StairBridgeDomain.realNatState x p (startFor B))
    (segmentMap_pool_nodup B hB) valid.1 valid.2.1 (by omega) (by omega)
    (by
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      simpa using fit) y c a hy
  rw [tickReverse_eq B hB, tickForward_eq B hB]
  simpa [StairSegment.forward, StairSegment.reverse] using round

/-- **Forward step (entry side).** The moved tick keeps the phase and advances
the re-rooted local stage to `s + 1`. -/
theorem tick_forward (B : Nat) (hB : B ∈ budgets) (x p : Nat) (h : RealHyp x p)
    (y : State) (hy : Decoded B x p y.basis) (c : List Bool) :
    (run (StairPhysicalPrimitives.tickForward (startFor B)) c y).phase = y.phase ∧
      StairSegment.Stage (segmentMap B) (startFor B)
        (StairBridgeDomain.orientRails (StairBridgeDomain.realRails x p (startFor B)))
        (startFor B + 1)
        (run (StairPhysicalPrimitives.tickForward (startFor B)) c y).basis := by
  obtain ⟨h0, h1, _, _, _, _⟩ := budget_range B hB
  have valid := SkywalkNat.iter_valid (startFor B) (SkywalkNat.init x p) h.p0 h.odd
  have fit := StairBridgeDomain.canonical_real_fit x p (startFor B) h.p0 h.x0 h.odd
    h.lt h.gap h.xlt h.cop (by omega)
  unfold Decoded at hy
  rw [StairBridgeDomain.orient_realRails x p _ h.p0 h.odd] at hy ⊢
  rw [tickForward_eq B hB]
  exact StairSegment.tick_step (segmentMap B) (startFor B) (startFor B)
    (StairBridgeDomain.realSign x p (startFor B))
    (StairBridgeDomain.realNatState x p (startFor B)) (by omega) (by omega)
    (segmentMap_pool_nodup B hB) valid.1 valid.2.1 y c hy (by simpa using fit)

/-! ## Virtual sites and the virtual raw state -/












/-! ## Naturality: the local stage at `l + 1` is a record stage on a virtual state -/

/-! K4-D (replay budget): the non-virtual-id facts used by `raw_stage`, as standalone lemmas (an `omega` inside
`raw_stage` works over its whole context). -/
namespace K4DF
end K4DF




/-! ## Moved middle programs avoid the virtual sites -/



theorem movedForward_clean (wm : Nat → Wire) (hinj : Function.Injective wm)
    (l : Nat) (hl5 : l % 5 = 0) :
    ∀ n i, i + n ≤ 512 → l + 1 ≤ i → 5 < i →
      ∀ q ∈ wires (StairReplay.movedForward wm i n), ¬ VWire wm l q := by
  have hn : (skywalkPoolWires wm).Nodup := by
    unfold skywalkPoolWires wireBlock
    exact List.Nodup.map hinj List.nodup_range'
  intro n
  induction n with
  | zero =>
      intro i _ _ _ q hq
      simp [StairReplay.movedForward, wires] at hq
  | succ n ih =>
      intro i hb hi h5 q hq
      simp only [StairReplay.movedForward, wires_append, Finset.mem_union] at hq
      rcases hq with (tick | packet) | rest
      · exact layout_clean wm hinj l i hi (by omega) q
          (StairPhysicalPrimitives.tick_layout wm i (by omega) hn q tick)
      · obtain ⟨due, k, rfl⟩ := StairPhysicalPrimitives.packFirst_wires wm i (by omega) q packet
        exact packet_clean wm hinj l i hl5 hi (by omega) due k
      · exact ih (i + 1) (by omega) (by omega) (by omega) q rest

theorem movedReverse_clean (wm : Nat → Wire) (hinj : Function.Injective wm)
    (l : Nat) (hl5 : l % 5 = 0) :
    ∀ n i, i + n ≤ 512 → l + 1 ≤ i → 5 < i →
      ∀ q ∈ wires (StairReplay.movedReverse wm i n), ¬ VWire wm l q := by
  have hn : (skywalkPoolWires wm).Nodup := by
    unfold skywalkPoolWires wireBlock
    exact List.Nodup.map hinj List.nodup_range'
  intro n
  induction n with
  | zero =>
      intro i _ _ _ q hq
      simp [StairReplay.movedReverse, wires] at hq
  | succ n ih =>
      intro i hb hi h5 q hq
      simp only [StairReplay.movedReverse, wires_append, Finset.mem_union] at hq
      rcases hq with rest | (packet | tick)
      · exact ih (i + 1) (by omega) (by omega) (by omega) q rest
      · obtain ⟨due, k, rfl⟩ :=
          StairPhysicalPrimitives.unpackFirst_wires wm i (by omega) q packet
        exact packet_clean wm hinj l i hl5 hi (by omega) due k
      · exact layout_clean wm hinj l i hi (by omega) q
          (StairPhysicalPrimitives.receiver_layout wm i (by omega) hn q tick)

/-! ## The six rows -/





/-- The moved middle programs of row `B` never touch a virtual site. -/
theorem middle_wires_clean (B : Nat) (hB : B ∈ budgets) (n : Nat)
    (hn : startFor B + 1 + n ≤ 512) (q : Wire)
    (hq : q ∈ wires (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B)
        (startFor B + 1) n) ∨
      q ∈ wires (StairReplay.movedReverse (StairPhysicalPrimitives.midSegmentMap B)
        (startFor B + 1) n)) :
    ¬ virtualSites B q := by
  obtain ⟨h0, h1, h5, _, _, _⟩ := budget_range B hB
  rcases hq with hq | hq
  · exact movedForward_clean _ (midSegmentMap_injective B hB) (startFor B) h5 n
      (startFor B + 1) hn le_rfl (by omega) q hq
  · exact movedReverse_clean _ (midSegmentMap_injective B hB) (startFor B) h5 n
      (startFor B + 1) hn le_rfl (by omega) q hq

/-- **The `virtual` premise of LT24's `middle_trip_local` / `terminal_middle_trip`
(and of LT21's middle steps)**, from the decoded oriented checkpoint. -/
theorem middle_virtual (B : Nat) (hB : B ∈ budgets) (x p : Nat) (h : RealHyp x p)
    (y : State) (hy : Decoded B x p y.basis) (c : List Bool) (n : Nat)
    (hn : startFor B + 1 + n ≤ 512) :
    ∃ t' : State,
      (run (StairPhysicalPrimitives.tickForward (startFor B)) c y).phase = t'.phase ∧
      (∀ q, q ∈ wires (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B)
            (startFor B + 1) n) ∨
          q ∈ wires (StairReplay.movedReverse (StairPhysicalPrimitives.midSegmentMap B)
            (startFor B + 1) n) →
        (run (StairPhysicalPrimitives.tickForward (startFor B)) c y).basis q = t'.basis q) ∧
      Rolling1588.Integer.Stage (StairPhysicalPrimitives.midSegmentMap B) true x p
        (startFor B + 1) t'.basis := by
  obtain ⟨t', hph, hag, st⟩ := virtual_stage B hB x p h true _ (tick_forward B hB x p h y hy c).2
  exact ⟨t', hph, fun q hq => hag q (middle_wires_clean B hB n hn q hq), st⟩

/-- `middle_virtual` with the provider's names (`middleForward`, and the
non-terminal `middleReverse`). -/
theorem middle_virtual_provider (B : Nat) (hB : B ∈ budgets) (x p : Nat) (h : RealHyp x p)
    (y : State) (hy : Decoded B x p y.basis) (c : List Bool) (n : Nat)
    (hn : startFor B + 1 + n ≤ 512) :
    ∃ t' : State,
      (run (StairPhysicalPrimitives.tickForward (startFor B)) c y).phase = t'.phase ∧
      (∀ q, q ∈ wires (StairPhysicalPrimitives.middleForward (startFor B + 1) n) ∨
          q ∈ wires (StairPhysicalPrimitives.middleReverse (startFor B + 1) n) →
        (run (StairPhysicalPrimitives.tickForward (startFor B)) c y).basis q = t'.basis q) ∧
      Rolling1588.Integer.Stage (StairPhysicalPrimitives.midSegmentMap B) true x p
        (startFor B + 1) t'.basis := by
  have hs := (budget_range B hB).2.2.2.2.2
  have eF : StairPhysicalPrimitives.middleForward (startFor B + 1) n =
      StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1) n := by
    unfold StairPhysicalPrimitives.middleForward
    rw [hs]
  have eR : StairPhysicalPrimitives.middleReverse (startFor B + 1) n =
      StairReplay.movedReverse (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1) n := by
    unfold StairPhysicalPrimitives.middleReverse
    rw [hs]
  rw [eF, eR]
  exact middle_virtual B hB x p h y hy c n hn

end ECDSAAdd.Entrant.StairFirstTickV3

end
end Merge_StairFirstTickV3_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairReplay_at_BOptimizations` -/
section Merge_StairReplay_at_BOptimizations

/-!
Replay handoff for the staircase schedule.

The moved arithmetic tick is concrete: it is the one-step specialization of
`StairSegment.forward`/`reverse`.  The codec predicates below deliberately keep
the placed layout abstract, since placement is chosen by the integration layer.
The final two fields of `LoanSpec` are the schedule-level composition facts that
remain after the local codec, segment, and carry-loan results have been applied.
-/

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairReplay

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField

-- (LT27 cp_split: `StairReplay` decl moved to StairEarlyCore)

-- (LT27 cp_split: `StairReplay` decl moved to StairEarlyCore)



@[simp] theorem forward_one (w : Nat → Wire) (i : Nat) :
    StairSegment.forward w i 1 = ECDSAAdd.Entrant.TickRanges.tick w i := by
  simp [StairSegment.forward]

@[simp] theorem reverse_one (w : Nat → Wire) (i : Nat) :
    StairSegment.reverse w i 1 =
      W.ReverseCarry.compactReceiverTick w i := by
  simp [StairSegment.reverse]




/-! ## Rich checkpoint placement

`StairSchedule.StairPrimitives` intentionally contains programs only.  The
following wrapper retains the data needed by the semantic composition: the
budget-indexed codec layout, the moved walk map, the checkpoint state and sign,
and the exact relation between LT1's expanded rails and LT2's local stage. -/


















/-! ## Carry-loan boundary

This is the exact interface promised by LT4 for the still-unpublished
`half760Loan`: the same `PairFrame` and clean-work precondition as the record
half, exact `4*d` resource deltas, omission of the retired logical roles, and
physicality. -/



/-! ## The four record rename layers -/









/-! ## Exact selected-prefix equality -/















end ECDSAAdd.Entrant.StairReplay
end Merge_StairReplay_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3Replay_at_BOptimizations` -/
section Merge_StairField2V3Replay_at_BOptimizations

/-!
# LT21: generic replay composition for field 2 (CANON v3)

The generic part of `StairCheckpointReplay` (from `RunEqOn` to
`checkpoint_composition`, verbatim) — that module's old eight-row section no
longer builds on v3 (`row_budget_mem` names the old budgets) — together with
LT14's placement-independent tape algebra (`StairChainAlgebra`) and
relational steps (`StairChainSteps`), in one namespace.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3Replay

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField







def entryReferenceArithmetic : Program :=
  renameProgram Rolling1588Lifetime.phaseHost
      (Rolling1588TickGap.firstPhase true) ++
    Rolling1588.entryFieldHosted




def exitReferenceOpening : Program :=
  renameProgram Rolling1588Lifetime.phaseHost
    (Rolling1588TickGap.firstPhase false)










/-! ## Measurement tapes -/
















end ECDSAAdd.Entrant.StairField2V3Replay

end
end Merge_StairField2V3Replay_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairRestSupportBase_at_BOptimizations` -/
section Merge_StairRestSupportBase_at_BOptimizations

/-!
# Support of the hosted rests, part 1: the label domain and its maps

`InDom q` says that `q` is one of the 2,326 raw labels on which the record
placement `wireFn2` is injective (`StairPlacedDomain.placedDomain`).  Every
rename that occurs inside the hosted rests maps this domain into itself, so
support is propagated compositionally; raw pieces are checked once.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairRestSupport

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
















/-! ## Domain-preserving maps -/


































/-! ## Moved first-tick map -/














/-! ## Extraction from record walks and packet sequences -/

theorem forward_append (isA : Bool) (n : Nat) :
    ∀ i m, Rolling1588TickGap.forward isA i (n + m) =
      Rolling1588TickGap.forward isA i n ++
        Rolling1588TickGap.forward isA (i + n) m := by
  induction n with
  | zero =>
    intro i m
    simp [Rolling1588TickGap.forward]
  | succ n ih =>
    intro i m
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [Rolling1588TickGap.forward, ih (i + 1) m, List.append_assoc]
    all_goals rw [show i + 1 + n = i + (n + 1) by omega]




end ECDSAAdd.Entrant.StairRestSupport

end
end Merge_StairRestSupportBase_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSlotsLib_at_BOptimizations` -/
section Merge_StairSlotsLib_at_BOptimizations

/-!
# Plan-independent gate-slot lemmas

The reusable part of the field-11 slot ledger (`StairSlots`), separated from
the eight-row schedule so that it survives re-plans of the checkpoint table:
loan and group slot bounds, the endpoint loan, wire-blind tick and moved-walk
slot equalities, and additivity of the record walks and packet groups.
Every statement is about generic programs or record programs; nothing here
refers to a checkpoint table, a host plan, or a concrete assembly.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairSlotsLib

open ECDSAAdd Arithmetic Challenge
open MappedCompressed Secp256k1 BalancedField Baselines

attribute [local irreducible] Rolling1588Lifetime.endHalf Rolling1588Lifetime.rawEnd Rolling1588Lifetime.endPacket R2SqEp760.endPacket760






























/-! ## The four loaned tops in each balanced half -/









/-! ## Packet groups and the multiplication endpoint -/























theorem tick_slots_formula (w : Nat → Wire) (i : Nat)
    (h0 : 385 ≤ i) (h1 : i ≤ 509)
    (hn : (skywalkPoolWires w).Nodup) :
    gateSlots (TickRanges.tick w i) =
      6 * W.compactSkywalkTickPreWidth i +
        11 * W.compactSkywalkTickPostWidth i := by
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have hi : i < 512 := by omega
  have hb := W.compactSkywalkTick_width_bounds i hi
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have hle : n ≤ L.half.length := by
    dsimp only [L, n]
    rw [W.compactSkywalkTick_half w i hi, wireBlock_length]
    omega
  have hw := narrowSkywalkRecord_widths L hv n (by omega) hle
  have hrec := narrowSignedRecord_slots_exact
    (narrowSkywalkRecordLayout L n) n hw (by omega)
  have hview := narrowSkywalkRecord_views L hv n (by omega) hle
  rw [hview.2.1] at hrec
  have hbLen : L.b.length = W.compactSkywalkTickPreWidth i := by
    dsimp only [L]
    rw [W.compactSkywalkTick_b w i hi, wireBlock_length]
  rw [hbLen] at hrec
  have hr := repairedRoute_slots_formula L hv
  have hmLen : L.aMid.length = W.compactSkywalkTickPreWidth i - 2 := by
    simp [L, W.compactSkywalkTickLayout, wireBlock_length]
  rw [hmLen] at hr
  have hc := compactCleanup_slots_formula w i hi
  have noCopy : ¬(225 ≤ i ∧ i ≤ 254) := by omega
  have noGap : ¬(255 ≤ i ∧ i ≤ 286) := by omega
  have noTrim : ¬W.fwdTrim i := by
    unfold W.fwdTrim
    omega
  have late : i = 224 ∨ (255 ≤ i ∧ i ≤ 509) := by omega
  simp only [TickRanges.tick, noCopy, if_false, TickGap.tick, noGap,
    W.repairedTick, noTrim, W.repairedTick0, late, if_true,
    gateSlots_append, skywalkSignedHalf, gateSlots_cons, gateSlots_nil,
    instructionSlots] at ⊢
  change gateSlots (W.repairedRoute L) + 1 +
      gateSlots (narrowSignedRecord (narrowSkywalkRecordLayout L n) n) +
      1 + gateSlots (W.compactSkywalkTickCleanup w i) = _
  omega


theorem tick_slots_map (w v : Nat → Wire) (i : Nat)
    (h0 : 385 ≤ i) (h1 : i ≤ 509)
    (hw : (skywalkPoolWires w).Nodup)
    (hv : (skywalkPoolWires v).Nodup) :
    gateSlots (TickRanges.tick w i) = gateSlots (TickRanges.tick v i) := by
  rw [tick_slots_formula w i h0 h1 hw,
    tick_slots_formula v i h0 h1 hv]




theorem movedForward_slots_eq (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (i n : Nat)
    (h0 : 385 ≤ i) (h1 : i + n ≤ 510) :
    gateSlots (StairReplay.movedForward w i n) =
      gateSlots (Rolling1588TickGap.forward true i n) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      have ht := tick_slots_map w base i h0 (by omega) hn base_pool_nodup
      have hp := packFirst_slots_map w base i (by omega)
      have tail := ih (i + 1) (by omega) (by omega)
      simp only [StairReplay.movedForward, Rolling1588TickGap.forward,
        gateSlots_append, rename_gateSlots] at tail ⊢
      omega

theorem movedReverse_slots_eq (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (i n : Nat)
    (h0 : 385 ≤ i) (h1 : i + n ≤ 510) :
    gateSlots (StairReplay.movedReverse w i n) =
      gateSlots (Rolling1588.reverse true i n) := by
  rw [← Rolling1588.Integer.reverse_eq_packets]
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      have ht := receiverTick_slots_map w base i h0 (by omega)
        hn base_pool_nodup
      have hp := unpackFirst_slots_map w base i (by omega)
      have tail := ih (i + 1) (by omega) (by omega)
      simp only [StairReplay.movedReverse, Rolling1588.Integer.reverse,
        gateSlots_append, rename_gateSlots] at tail ⊢
      omega

theorem forward_slots_add (i n m : Nat) :
    gateSlots (Rolling1588TickGap.forward true i (n + m)) =
      gateSlots (Rolling1588TickGap.forward true i n) +
        gateSlots (Rolling1588TickGap.forward true (i + n) m) := by
  induction n generalizing i with
  | zero => simp [Rolling1588TickGap.forward, gateSlots]
  | succ n ih =>
      simp only [Nat.succ_add, Nat.add_one, Rolling1588TickGap.forward,
        gateSlots_append, ih]
      rw [show (i + n).succ = i + n.succ by omega]
      omega






end ECDSAAdd.Entrant.StairSlotsLib

end
end Merge_StairSlotsLib_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSlotsShape_at_BOptimizations` -/
section Merge_StairSlotsShape_at_BOptimizations

/-!
# Slot facts and walk arithmetic, generic in the primitive provider

`WalkFacts p c` lists the slot facts a `StairSchedule.StairPrimitives`
provider must satisfy for the ledger `c`; the walk theorems themselves are in
`StairSlotsWalk`.  Every numeric index relation is passed as an explicit
hypothesis (no definitional arithmetic in statements), and `gateSlots` is
locally irreducible.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairSlotsPlan

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed DirectSkywalk Secp256k1 BalancedField Baselines

attribute [local irreducible] gateSlots


/-! ## Record-walk arithmetic -/

theorem forward_succ (s n t m : Nat) (ht : t = s + 1) (hm : m = n + 1) :
    gateSlots (Rolling1588TickGap.forward true s m) =
      gateSlots (TickRanges.tick base s) +
        gateSlots (Rolling1588.Integer.packFirst base true s) +
        gateSlots (Rolling1588TickGap.forward true t n) := by
  subst ht
  subst hm
  simp only [Rolling1588TickGap.forward, gateSlots_append, rename_gateSlots]


theorem forward_add (i n m j k : Nat) (hj : j = i + n) (hk : k = n + m) :
    gateSlots (Rolling1588TickGap.forward true i k) =
      gateSlots (Rolling1588TickGap.forward true i n) +
        gateSlots (Rolling1588TickGap.forward true j m) := by
  subst hj
  subst hk
  exact StairSlotsLib.forward_slots_add i n m




/-! ## Segment shapes -/




end ECDSAAdd.Entrant.StairSlotsPlan

end
end Merge_StairSlotsShape_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareBBody_at_BOptimizations` -/
section Merge_StairSquareBBody_at_BOptimizations

/-! # LT36 (U3b): generic B body frame

`bodyG L fold1 fold2 loop efold rebuild` is the record's `LocalSevenBody.bodyForBoth` with the two
folds and the e-fold as parameters.  `frameG` is `LocalSevenBody.frame` with the fold triples and
the e-fold triple as hypotheses (the proof is the record's, with those three steps replaced). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareBBody
open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ManyACarryDevelop FullBTemp ZeroReadDevelop FourthASavedCarryDevelop LowAccCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop
open LowBitCarryDevelop ParkCarry7Develop ParkCarry10Develop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run

def bodyG (L : CuccaroStreamedSquareWideLayout) (fold1 fold2 loop efold rebuild : Program) : Program :=
 fold1 ++ (fold2 ++ (foldFor L loop ++ (efold ++ rebuild)))

theorem frameG
 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hcw : c∉L.wires) (loopProgram : Program)
 (loopSpec : ∀ (base : BasisState) (_clean : L.PairClean base) (_hsum : base L.core.sumCarry=false)
  (O E O' : Nat) (_hE : E<2^129),
  Triple (BState L base O E (4294968272*regValue (hiReg L) base)) (FullBTemp.middle L c)
   (BState L base O' E (4294968272*regValue (hiReg L) base)) →
  Triple (BState L base O E 0) loopProgram (BState L base O' E 0))
 (efold : Program)
 (efoldSpec : ∀ (b : BasisState) (_clean : L.PairClean b) (O E : Nat) (_hO : O<SquareReduction.p),
  Triple (BState L b O E 0) efold
   (BState L b ((4294968272*flipE (b c) E+(SquareReduction.p-1-O))%SquareReduction.p) E 0))
 (rebuildProgram : Program)
 (rebuildSpec : ∀ (base outBase : BasisState) (_clean : L.PairClean base) (O E B : Nat)
  (_hb : B<2^128),
  Triple (BState L base O E 0) (ParkCarry10Develop.rebuild L) (BState L outBase O B 0) →
  Triple (BState L base O E 0) rebuildProgram (BState L outBase O B 0))
 (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false)
 (O : Nat) (hO : O<SquareReduction.p)
 (hg : base c=false → M=0) (hSource : M=if base c then regValue L.core.high base else 0)
 (fold1 fold2 : Program)
 (fold1Spec : ∀ O0, O0<SquareReduction.p → Triple (SquareFrame L.core.out base O0) fold1
   (SquareFrame L.core.out base ((M^2+(SquareReduction.p-1-O0))%SquareReduction.p)))
 (fold2Spec : ∀ O0, O0<SquareReduction.p → Triple (SquareFrame L.core.out base O0) fold2
   (SquareFrame L.core.out base (((M^2/2^128)%2^128+2^128*(M^2%2^128)+(SquareReduction.p-1-O0))%SquareReduction.p))) :
 Triple (SquareFrame L.core.out base O) (bodyG L fold1 fold2 loopProgram efold rebuildProgram)
  (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by

  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  let P := M^2
  let b0 := P%2^128
  let b1 := P/2^128
  let W := 4294968272*b1
  let g := base c
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have hb1lt : b1<2^128 := by
    show P/2^128<2^128
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc P<2^256 := hb
      _ = 2^128*2^128 := by norm_num
  have hWlt : W<2^163 := by
    show 4294968272*b1<2^163
    norm_num at hb1lt ⊢
    omega
  have t1 : Triple (SquareFrame L.core.out base O) fold1 (SquareFrame L.core.out base O1) :=
    fold1Spec O hO
  have t2 : Triple (SquareFrame L.core.out base O1) fold2 (SquareFrame L.core.out base O2) :=
    fold2Spec O1 hO1
  have e0 : regValue (eReg L) base=b0 := eReg_value L hw base P hP hb
  have a0 : regValue (accReg L) base=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hc.work q (accReg_work L q hq))
  have hb1 : regValue (hiReg L) base=b1 := by
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have conv1 : ∀s,SquareFrame L.core.out base O2 s → BState L base O2 b0 0 s := by
    intro s hs
    refine ⟨hs.1,?_,?_,fun q h1 _ _ => hs.2 q h1⟩
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (eReg_away L hn q hq).1)).trans e0
    · exact (regValue_congr _ _ _ (fun q hq => hs.2 q (accReg_out L hn q hq))).trans a0


  let u := b1/2^96
  let d := W/2^128 - u
  let H := b0/2^32
  let l' := (b0%2^32 + u)%2^32
  let K := (b0%2^32 + u)/2^32
  let O3 := ((u + 4294968273*d) + 4294968272*2^32*K + 2^128*(W%2^128) + (SquareReduction.p-1-O2)) % SquareReduction.p
  let E1 := (2^32*H + l' + 2^130 - b1) % 2^130
  let O4 := (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p
  have hO3 : O3<SquareReduction.p := Nat.mod_lt _ pmod
  have hb0 : b0<2^128 := Nat.mod_lt _ (by positivity)
  have hu32 : u < 2^32 := by
    show b1/2^96 < 2^32
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc b1<2^128 := hb1lt
      _ = 2^32*2^96 := by norm_num
  have hH : H < 2^96 := by show b0/2^32 < 2^96; omega
  have hl' : l' < 2^32 := Nat.mod_lt _ (by positivity)
  have hK : K ≤ 1 := by show (b0%2^32 + u)/2^32 ≤ 1; omega
  have hKif : (if l' < u then 1 else 0) = K := by
    show (if (b0%2^32 + u)%2^32 < u then 1 else 0) = (b0%2^32 + u)/2^32
    by_cases hc' : (b0%2^32 + u)%2^32 < u
    · rw [if_pos hc']; omega
    · rw [if_neg hc']; omega
  let kap:Bool:=decide (K=1)
  let baseK:=writeBit base L.core.sumCarry kap
  have kapNat:kap.toNat=K := by
    have kk:K=0 ∨ K=1 := by omega
    rcases kk with kk|kk <;> simp [kap,kk]
  have hcK:L.PairClean baseK := ParkCarryDevelop.base_clean L hn base hc kap
  have productOff:L.core.sumCarry∉L.core.product := by
    intro h;apply ParkCarryDevelop.sumCarry_away L hn;simp [ParkCarryDevelop.restWires,h]
  have highOff:L.core.sumCarry∉hiReg L := by
    intro h;exact productOff (List.mem_of_mem_take (List.mem_of_mem_drop h))
  have hb1K:regValue (hiReg L) baseK=b1 := by
    dsimp only [baseK]
    rw [ParkCarryDevelop.reg_update_off _ _ _ _ highOff]
    exact hb1
  have cq:c≠L.core.sumCarry := by
    intro h;apply hcw
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
  have gc:baseK c=base c := by simp [baseK,writeBit,cq]
  have resetBase:writeBit baseK L.core.sumCarry false=base := by
    funext q
    by_cases hq:q=L.core.sumCarry
    · subst q;simp [writeBit,Function.update,hsum]
    · simp [baseK,writeBit,Function.update,hq]
  -- Park the completed low-window carry instead of recomputing it.
  have k1 := eAddLo_step L hw hn base hc O2 0 b0 hb0
  rw [hb1] at k1
  have squareBit : (b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw[Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have loanFact : ((2^32*H+l'+2^128*K)/2%2==1)=
      ((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
        ((b1/2^96%2==1)&&((2^32*H+l'+2^128*K)%2==1))) := by
    have low0:(2^32*H+l'+2^128*K)%2=(b0%2^32+u)%2:=by dsimp[l'];omega
    have low1:(2^32*H+l'+2^128*K)/2%2=(b0%2^32+u)/2%2:=by dsimp[l'];omega
    rw[low0,low1]
    exact known_second_loan (b0%2^32) u squareBit
  let originalM:=regValue L.core.high base
  have source1:base (bit1 L.core.high)=digit originalM 1:=by
    simpa only[digit,pow_one]using bit1_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE:(2^32*H+l'+2^128*K)%16=lowSum (base c) originalM u%16:=by
    rw[lowSum,←hSource]
    exact folded_low_mod16 M u H l' K rfl rfl
  have loanFact2:=loan2_from_mod16 (base c) originalM u (2^32*H+l'+2^128*K) modE
  rw[←source1]at loanFact2
  have source0:base (L.core.high.headD 0)=digit originalM 0:=by
    simpa only[digit,pow_zero,Nat.div_one]using head_parity L.core.high base
      (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])
  have modE2:(2^32*H+l'+2^128*K)%2=lowSum (base c) originalM u%2:=by omega
  have loanFact0:=LowBitCarryNumbers.loan0_from_mod2 (base c) originalM u (2^32*H+l'+2^128*K)
    (by simpa only[lowSum]using modE2)
  rw[←source0]at loanFact0
  have wm := wMidFullCCC0_step L hw hn c hcw base hc O2 (2^32*H+l'+2^128*K) b1 hb1 hb1lt hO2
    H l' K hH hl' hK rfl loanFact loanFact2 loanFact0
  have wmBase : Triple (BState L base O2 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base))
      (wMidFullCCC0 L c)
      (BState L base O3 (2^32*H+l'+2^128*K) (4294968272*regValue (hiReg L) base)) := by
    simpa only [hb1] using wm
  have loopE : 2^32*H+l'+2^128*K<2^129 := by
    have h0:=hH
    have h1:=hl'
    have h2:=hK
    norm_num only at h0 h1 h2 ⊢
    omega
  have loop := loopSpec base hc hsum
    O2 (2^32*H+l'+2^128*K) O3 loopE wmBase
  have kc:=ParkCarryDevelop.park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (foldFor L loopProgram) (BState L baseK O3 E1 0) :=
    by simpa only [foldFor,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
  -- new e-fold
  have tfNew : Triple (BState L baseK O3 E1 0) efold (BState L baseK O4 E1 0) := by
    have h := efoldSpec baseK hcK O3 E1 hO3
    rw [gc] at h
    exact h
  -- wRestoreT
  have bk : (E1+b1)%2^130 = 2^32*H + l' := by show ((2^32*H + l' + 2^130 - b1) % 2^130 + b1) % 2^130 = _; omega
  have r2 := eAddB_step L hw hn baseK hcK O4 E1 0 b1 hb1K (by rw [bk]; omega)
  rw [bk] at r2
  have bit32:(b0%2^32)/2%2=0 := by
    change ((M^2%2^128)%2^32)/2%2=0
    rw [Nat.mod_mod_of_dvd _ (by decide : 2^32 ∣ 2^128)]
    exact KnownSecondSubDevelop.square_second32 M
  have total:l'+2^32*(baseK L.core.sumCarry).toNat=b0%2^32+regValue (hiReg L) baseK/2^96 := by
    have atq:baseK L.core.sumCarry=kap := by simp [baseK,writeBit]
    rw [atq,kapNat,hb1K]
    show ((b0%2^32+u)%2^32)+2^32*((b0%2^32+u)/2^32)=b0%2^32+u
    exact Nat.mod_add_div _ _
  have r3:=ParkCarryDevelop.restore_step L hw hn baseK hcK O4 0 H l' (b0%2^32) hH hl'
    (Nat.mod_lt _ (by positivity)) bit32 total
  have bb:2^32*H+b0%2^32=b0 := by dsimp [H];omega
  rw [resetBase,bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 744
  have tr : Triple (BState L baseK O4 E1 0) (ParkCarry10Develop.rebuild L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
  have trNew : Triple (BState L baseK O4 E1 0) rebuildProgram (BState L base O4 b0 0) :=
    rebuildSpec baseK base hcK O4 E1 b0 hb0 tr
  have conv0 : ∀s,BState L base O4 b0 0 s → SquareFrame L.core.out base O4 s := by
    intro s hs
    refine ⟨hs.1,fun q hq => ?_⟩
    by_cases he : q∈eReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.1.trans e0.symm) q he
    by_cases ha : q∈accReg L
    · exact (regValue_eq_iff _ _ _).mp (hs.2.2.1.trans a0.symm) q ha
    exact hs.2.2.2 q hq he ha
  have key : O4 = bO4 (M^2) (base c) O := by
    have hg' : g = false → b1 = 0 ∧ b0 = 0 := by
      intro h0
      have : M = 0 := hg h0
      subst this
      simp [b1, b0, P]
    have e3 : O3 = (((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p := by
      simp only [O3, u, d, K, W]
      congr 1; ring
    have e4 : O4 = (4294968272*flipE g ((2^32*(b0/2^32) + (b0%2^32+b1/2^96)%2^32 + 2^130 - b1) % 2^130) +
        (SquareReduction.p-1-((((b1/2^96 + 4294968273*(4294968272*b1/2^128 - b1/2^96)) + 2^128*((4294968272*b1)%2^128)) +
        4294968272*2^32*((b0%2^32+b1/2^96)/2^32) + (SquareReduction.p-1-O2)) % SquareReduction.p))) % SquareReduction.p := by
      show (4294968272*flipE g E1 + (SquareReduction.p-1-O3)) % SquareReduction.p = _
      rw [e3]
    rw [e4, o4K b0 b1 O2 _ g hb0 hb1lt hO2 hg']
    exact o4_eq b0 b1 O2 g hb0 hb1lt hO2 hg'
  have all := t1.seq (t2.seq (Triple.conseq (fun s h => h) ((Triple.conseq conv1 tw (fun s h => h)).seq
    (tfNew.seq trNew)) conv0))
  rw [key] at all
  simpa only [bodyG] using all




end ECDSAAdd.Entrant.StairSquareBBody
end Merge_StairSquareBBody_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareBChecks_at_BOptimizations` -/
section Merge_StairSquareBChecks_at_BOptimizations

/-! # LT36 (U3b): concrete kernel checks for the B body pieces (layout `LowAccCarryDevelop.L`)

Hole sites `holesB` = pool 725..759, 761..764 (same term as `StairSqLoopA.holes`).  Every check is a
single `decide +kernel` on a Boolean scan of a concrete program or list. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareBChecks
open ECDSAAdd ECDSAAdd.Entrant Arithmetic ControlLoan1589BFFold StairSquareBMapped StairSquareBEFold

abbrev LB : CuccaroStreamedSquareWideLayout := LowAccCarryDevelop.L
abbrev cB : Wire := LowAccCarryDevelop.c


/-- The 39 hole sites plus `normFlag` (pool 646, which placement sends onto old hole 718). -/
def forbidB : List Wire := holesB++[LB.core.normFlag]

theorem holes_forbid (q : Wire) (hq : q∈holesB) : q∈forbidB := List.mem_append_left _ hq
theorem normFlag_forbid : LB.core.normFlag∈forbidB := List.mem_append_right _ (by simp)

/-! ## K4-D (replay budget): the holes and the layout `LB` in closed form

`holesB` walked `List.range' 4115 5699` (`Baselines.layout.core.poolWire`) for every hole; `LB` is
`Baselines.layout.dialogStreamedSquareWide`, whose lists are `take`/`drop` slices of the 5,699-wire pool.
`K4DQ.LB_eq` rewrites `LB` into the same layout with `List.range'` fields (proved symbolically), so the
kernel checks below evaluate short intervals instead of pool slices. -/
namespace K4DQ






theorem LB_eq : LB = LBF := by
  have hp : Baselines.layout.dialogPool = List.range' 4115 2613 := List.take_range'_of_length_ge (by decide)
  have e1 : Baselines.layout.dialogPool.take 258 = List.range' 4115 258 := by
    rw [hp]; exact List.take_range'_of_length_ge (by decide)
  have e2 : (Baselines.layout.dialogPool.drop 258).take 128 = List.range' 4373 128 := by
    rw [hp, List.drop_range']; exact List.take_range'_of_length_ge (by decide)
  have e3 : (Baselines.layout.dialogPool.drop 386).take 256 = List.range' 4501 256 := by
    rw [hp, List.drop_range']; exact List.take_range'_of_length_ge (by decide)
  have e4 : (Baselines.layout.dialogPool.drop 649).take 126 = List.range' 4764 126 := by
    rw [hp, List.drop_range']; exact List.take_range'_of_length_ge (by decide)
  have ex : Baselines.layout.point.x = List.range' 2 256 := mr 2 256
  have ey : Baselines.layout.point.y = List.range' 258 256 := mr 258 256
  have p2 : Baselines.layout.core.poolWire 642 = 4757 := pw_lt 642 (by decide)
  have p3 : Baselines.layout.core.poolWire 643 = 4758 := pw_lt 643 (by decide)
  have p4 : Baselines.layout.core.poolWire 644 = 4759 := pw_lt 644 (by decide)
  have p5 : Baselines.layout.core.poolWire 645 = 4760 := pw_lt 645 (by decide)
  have p6 : Baselines.layout.core.poolWire 646 = 4761 := pw_lt 646 (by decide)
  have p7 : Baselines.layout.core.poolWire 647 = 4762 := pw_lt 647 (by decide)
  have p8 : Baselines.layout.core.poolWire 648 = 4763 := pw_lt 648 (by decide)
  show Baselines.layout.dialogStreamedSquareWide = LBF
  unfold ControlledPointLayout.dialogStreamedSquareWide ControlledPointLayout.dialogStreamedSquare LBF
  rw [e1, e2, e3, e4, ex, ey, p2, p3, p4, p5, p6, p7, p8]

end K4DQ

/-- One pass over `P`: does any instruction touch any wire of `hs`? -/
def touchedAny (P : Program) (hs : List Wire) : Bool :=
  P.any (fun i => hs.any (fun q => C163Touch.instructionTouches q i))

theorem touchedAny_spec (P : Program) (hs : List Wire) (h : touchedAny P hs=false) :
    ∀q∈hs,q∉wires P := by
  intro q hq hw
  have t := (C163Touch.touched_spec P q).mpr hw
  simp only [C163Touch.touched,List.any_eq_true] at t
  obtain ⟨i,hi,hti⟩ := t
  have : touchedAny P hs=true := by
    simp only [touchedAny,List.any_eq_true]
    exact ⟨i,hi,q,hq,hti⟩
  rw [h] at this
  exact Bool.false_ne_true this

/-! ## LT48 (replay budget): bit-mask list checks, exact slot formulas

`decide` on list membership / `Nodup` walks the unevaluated layout lists once per query; a `Nat` bit
mask is built once (`maskL`, `nodupMaskL`, as `StairLoan.maskOf` / `nodupMask`).  Gate slots do not
depend on wires: `addS`, `eltS`, `skS`, `esS`, `elS` compute the slots of `mappedAdd`,
`eraseLtChainM`, `Skip4.addSkip`, `Skip4.eraseSkip`, `eraseLtChain` by a shallow recursion, so the
kernel never walks the deep `++` nest of the 14,196 gates of `mid_slots_le`. -/
namespace LT48B
open Challenge


theorem forbidB_eq : forbidB = forbidNat := by decide +kernel







/-! ### Slots of the adder pieces (wire-independent) -/













end LT48B

theorem coreB_nodup : (coreB LB).wires.Nodup := (LT48B.nodupMaskL_sound _ 0 (by decide +kernel)).1

theorem bitsB_away : ∀q∈ECDSAAdd.Entrant.accReg LB,
    q∉(coreB LB).out++(coreB LB).carry++[(coreB LB).high,(coreB LB).cin,(coreB LB).flag] :=
  LT48B.disj_of_maskL _ _ (by decide +kernel)

theorem bitsB_ok : BitsOK (coreB LB) 256 (bitsB LB) :=
  ⟨bitsB_length LB LowAccCarryDevelop.layout_widths,by rw [bitsB_wires]; exact bitsB_away⟩

theorem mid_free : ∀q∈forbidB,q∉(coreB LB).out++(coreB LB).carry++
    [(coreB LB).high,(coreB LB).cin,(coreB LB).flag]++ECDSAAdd.Entrant.accReg LB := by
  rw [LT48B.forbidB_eq]
  exact LT48B.disj_of_maskL _ _ (by decide +kernel)

section K2HitSec
set_option maxRecDepth 100000

namespace K2Hit


theorem corr_hit (l : List Nat) (q : Nat) (hq : q∈l) (c : Correction)
    (h : C163Touch.correctionTouches q c=true) : corrHit (LT48B.maskL l) c=true := by
  cases c with
  | Z a =>
    simp only [C163Touch.correctionTouches,beq_iff_eq] at h
    subst h
    simp only [corrHit,LT48B.testBit_maskL,decide_eq_true_eq]
    exact hq
  | CZ a b =>
    simp only [C163Touch.correctionTouches,Bool.or_eq_true,beq_iff_eq] at h
    simp only [corrHit,LT48B.testBit_maskL,Bool.or_eq_true,decide_eq_true_eq]
    rcases h with rfl|rfl
    · exact Or.inl hq
    · exact Or.inr hq

theorem corrs_hit (l : List Nat) (q : Nat) (hq : q∈l) (cs : List Correction)
    (h : cs.any (C163Touch.correctionTouches q)=true) : cs.any (corrHit (LT48B.maskL l))=true := by
  obtain ⟨c,hc,ht⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨c,hc,corr_hit l q hq c ht⟩

theorem instr_hit (l : List Nat) (q : Nat) (hq : q∈l) (i : Instr)
    (h : C163Touch.instructionTouches q i=true) : instrHit (LT48B.maskL l) i=true := by
  have tb : ∀a,q=a→(LT48B.maskL l).testBit a=true := by
    intro a e
    subst e
    rw [LT48B.testBit_maskL]
    exact decide_eq_true hq
  cases i with
  | X a =>
    simp only [C163Touch.instructionTouches,beq_iff_eq] at h
    simp only [instrHit]
    exact tb a h
  | CX a b =>
    simp only [C163Touch.instructionTouches,Bool.or_eq_true,beq_iff_eq] at h
    simp only [instrHit,Bool.or_eq_true]
    rcases h with h|h
    · exact Or.inl (tb a h)
    · exact Or.inr (tb b h)
  | CCX a b d =>
    simp only [C163Touch.instructionTouches,Bool.or_eq_true,beq_iff_eq] at h
    simp only [instrHit,Bool.or_eq_true]
    rcases h with (h|h)|h
    · exact Or.inl (Or.inl (tb a h))
    · exact Or.inl (Or.inr (tb b h))
    · exact Or.inr (tb d h)
  | measureX a cs ds =>
    simp only [C163Touch.instructionTouches,Bool.or_eq_true,beq_iff_eq] at h
    simp only [instrHit,Bool.or_eq_true]
    rcases h with (h|h)|h
    · exact Or.inl (Or.inl (tb a h))
    · exact Or.inl (Or.inr (corrs_hit l q hq cs h))
    · exact Or.inr (corrs_hit l q hq ds h)

/-- One mask test per gate wire instead of one list scan per forbidden wire. -/
theorem touchedAny_of_mask (P : Program) (l : List Nat) (h : P.any (instrHit (LT48B.maskL l))=false) :
    touchedAny P l=false := by
  cases ht : touchedAny P l
  · rfl
  · exfalso
    simp only [touchedAny,List.any_eq_true] at ht
    obtain ⟨i,hi,q,hq,hti⟩ := ht
    have : P.any (instrHit (LT48B.maskL l))=true := List.any_eq_true.mpr ⟨i,hi,instr_hit l q hq i hti⟩
    rw [h] at this
    exact Bool.false_ne_true this
end K2Hit

end K2HitSec

theorem eFlip_free : touchedAny (eFlip LB cB) forbidB=false := by
  rw [LT48B.forbidB_eq]; exact K2Hit.touchedAny_of_mask _ _ (by decide +kernel)

/-! ### K2 (replay budget): the e-fill pieces by their support, not by a scan

`fillIn_free`/`fillOut_free` were one `decide +kernel` scan each (41 s / 36 s of kernel time: the kernel builds the
~3,900 gates of the early-H accumulation and tests 40 wires per gate).  The holes sit in `accZ` beyond index 29,
and the early H terms (shift 4/10/6/32 of the 130-wire `eReg`) pad with at most `accZ.take 29`, so the record's
register-level support lemma (`Acc.sbuild_support`) applied with `Z := (accZ L).take 29` already excludes them;
only the 40-wire disjointness against that support list is checked concretely (bit mask). -/
section K2FillSec
set_option maxRecDepth 100000

theorem touchedAny_of_free (P : Program) (hs : List Wire) (h : ∀q∈hs,q∉wires P) : touchedAny P hs=false := by
  cases ht : touchedAny P hs
  · rfl
  · exfalso
    simp only [touchedAny,List.any_eq_true] at ht
    obtain ⟨i,hi,q,hq,hti⟩ := ht
    have t : C163Touch.touched P q=true := by
      simp only [C163Touch.touched,List.any_eq_true]
      exact ⟨i,hi,hti⟩
    exact h q hq ((C163Touch.touched_spec P q).mp t)

namespace K2Fill






end K2Fill

theorem efill_forbid : LT48B.forbidNat.all (fun q => !(LT48B.maskL (K2Fill.efillS LB)).testBit q)=true := by
  rw [K4DQ.LB_eq]
  decide +kernel

end K2FillSec

attribute [local irreducible] ECDSAAdd.wires in
theorem fillIn_free : touchedAny (OwnDiagAll12Square.fillInK LB (eItem LB)) forbidB=false := by
  apply touchedAny_of_free
  intro q hq hw
  rw [LT48B.forbidB_eq] at hq
  have h1 := (K2Fill.efill_support LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup).1 hw
  have h2 : q∈K2Fill.efillS LB := List.mem_toFinset.mp h1
  exact LT48B.disj_of_maskL _ _ efill_forbid q hq h2

attribute [local irreducible] ECDSAAdd.wires in
theorem fillOut_free : touchedAny (SourceFourPrefix130Develop.fillOutKnown LB (eItem LB)) forbidB=false := by
  apply touchedAny_of_free
  intro q hq hw
  rw [LT48B.forbidB_eq] at hq
  have h1 := (K2Fill.efill_support LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup).2 hw
  have h2 : q∈K2Fill.efillS LB := List.mem_toFinset.mp h1
  exact LT48B.disj_of_maskL _ _ efill_forbid q hq h2

/-! The other (unchanged) e-part pieces of the B body, for the assembly. -/
theorem eAddLo_free : touchedAny (eAddLo LB) forbidB=false := by
  rw [LT48B.forbidB_eq]; exact K2Hit.touchedAny_of_mask _ _ (by decide +kernel)
theorem park_free : touchedAny (ParkCarryDevelop.program (eU LB) LB.core.sumCarry) forbidB=false := by
  rw [LT48B.forbidB_eq]; exact K2Hit.touchedAny_of_mask _ _ (by decide +kernel)
-- K2 (replay budget): `eSubK_free` was a `decide +kernel` scan (13.6 s); the subtractor's support is its registers.
section K2SubSec
set_option maxRecDepth 100000

namespace K2Sub
attribute [local irreducible] ECDSAAdd.wires


end K2Sub

theorem eSubK_support : wires (eSubK LB)⊆(eKw LB::LB.core.cin::(hiReg LB++[eZ0 LB]++(eRlow LB++[eU LB])++
    (eBank LB).take 128++[eV LB])).toFinset :=
  K2Sub.subTop_support _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)

end K2SubSec

attribute [local irreducible] ECDSAAdd.wires in
theorem eSubK_free : touchedAny (eSubK LB) forbidB=false := by
  apply touchedAny_of_free
  intro q hq hw
  rw [LT48B.forbidB_eq] at hq
  exact LT48B.disj_of_maskL _ _ (by decide +kernel) q hq (List.mem_toFinset.mp (eSubK_support hw))

theorem rebuild_free : touchedAny LocalRebuild.improved forbidB=false := by
  rw [LocalRebuild.improved,LocalRebuild.literal,LT48B.forbidB_eq]
  exact K2Hit.touchedAny_of_mask _ _ (by decide +kernel)

/-- Support of the new middle inside the layout (for `c :: L.wires` support statements). -/
theorem mid_in_layout : ∀q∈(coreB LB).out++(coreB LB).carry++
    [(coreB LB).high,(coreB LB).cin,(coreB LB).flag]++ECDSAAdd.Entrant.accReg LB,q∈cB::LB.wires :=
  LT48B.sub_of_maskL _ _ (by decide +kernel)

theorem mid_slots_le : Challenge.gateSlots (midB LB)≤Challenge.gateSlots (qprog4Tq LB.measuredCore SquareReduction.p) := by
  simp only [midB, qprogM, qprog4Tq, mappedConstAdd, Challenge.gateSlots_append, LT48B.addS_eq, LT48B.eltS_eq,
    LT48B.skS_eq, LT48B.esS_eq]
  decide +kernel

end ECDSAAdd.Entrant.StairSquareBChecks
end Merge_StairSquareBChecks_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareBEFoldK_at_BOptimizations` -/
section Merge_StairSquareBEFoldK_at_BOptimizations

/-! # LT36 (U3b): the new B e-fold on the concrete layout — drop-in package

`efold = eFoldB LowAccCarryDevelop.L LowAccCarryDevelop.c` replaces the record's
`LocalEFoldOptimize.improved` (= `eFoldTq L c` with two CCX→CX patches) in the B body.
* `efold_spec`   : the e-fold triple in the shape used by the B body proof (`frameG`'s `efoldSpec`);
* `efold_avoids` : no hole site (pool 725..759, 761..764) and not `normFlag`;
* `efold_counts` : T = record + 10, M equal; `efold_slots_le` : slots ≤ record;
* `efold_support`: inside `c :: L.wires`; `efold_physical`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareBEFoldK
open ECDSAAdd ECDSAAdd.Entrant Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout RecordedQuantum
open ControlLoan1589BFFold StairSquareBMapped StairSquareBEFold StairSquareBChecks
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] LowAccCarryDevelop.L

def efold : Program := eFoldB LB cB

theorem efold_spec (b : BasisState) (hb : LB.PairClean b) (O E : Nat) (hO : O<SquareReduction.p) :
    Triple (BState LB b O E 0) efold
      (BState LB b ((4294968272*flipE (b cB) E+(SquareReduction.p-1-O))%SquareReduction.p) E 0) :=
  eFoldB_step LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup coreB_nodup bitsB_ok
    cB LowAccCarryDevelop.control_outside b hb O E hO


theorem efold_counts :
    toffoliCount efold=toffoliCount LocalEFoldOptimize.improved+10 ∧
    measurementCount efold=measurementCount LocalEFoldOptimize.improved := by
  have g := eFoldB_counts LB LowAccCarryDevelop.layout_widths cB
  have t := LocalEFoldResources.toffoli
  have mm := LocalEFoldResources.measurements
  have ha : LocalEFoldAnchor.actual=eFoldTq LB cB := rfl
  rw [ha] at t mm
  exact ⟨by unfold efold; omega,by unfold efold; omega⟩

theorem efold_avoids_forbid : ∀q∈forbidB,q∉wires efold := by
  intro q hq hw
  have h1 : q∉wires (eFlip LB cB) := touchedAny_spec _ _ eFlip_free q hq
  have h2 : q∉wires (OwnDiagAll12Square.fillInK LB (eItem LB)) := touchedAny_spec _ _ fillIn_free q hq
  have h3 : q∉wires (SourceFourPrefix130Develop.fillOutKnown LB (eItem LB)) := touchedAny_spec _ _ fillOut_free q hq
  have h4 : q∉wires (midB LB) := by
    intro h
    have hs := qprogM_support (coreB LB) (bitsB LB) SquareReduction.p h
    rw [bitsB_wires] at hs
    exact mid_free q hq (List.mem_toFinset.mp hs)
  simp only [efold,eFoldB,accFoldB,wires_append,Finset.mem_union] at hw
  tauto

theorem efold_avoids : ∀q∈holesB,q∉wires efold :=
  fun q hq => efold_avoids_forbid q (holes_forbid q hq)

theorem efold_normFlag : LB.core.normFlag∉wires efold := efold_avoids_forbid _ normFlag_forbid

/-- The shared pieces are pieces of the record e-fold, which is a piece of the record body. -/
theorem eFoldTq_support : wires (eFoldTq LB cB)⊆(cB::LB.wires).toFinset := by
  have h := ParkCarry10Develop.body_support LB LowAccCarryDevelop.layout_widths LowAccCarryDevelop.layout_nodup cB
  intro q hq
  apply h
  simp only [ParkCarry10Develop.body,wires_append,Finset.mem_union]
  tauto

theorem efold_support : wires efold⊆(cB::LB.wires).toFinset := by
  have base := eFoldTq_support
  have hm : wires (midB LB)⊆(cB::LB.wires).toFinset := by
    intro q h
    have hs := qprogM_support (coreB LB) (bitsB LB) SquareReduction.p h
    rw [bitsB_wires] at hs
    exact List.mem_toFinset.mpr (mid_in_layout q (List.mem_toFinset.mp hs))
  intro q hq
  simp only [efold,eFoldB,accFoldB,wires_append,Finset.mem_union] at hq
  have e1 : q∈wires (eFlip LB cB) → q∈(cB::LB.wires).toFinset := fun h => base (by
    simp only [eFoldTq,wires_append,Finset.mem_union]; tauto)
  have e2 : q∈wires (OwnDiagAll12Square.fillInK LB (eItem LB)) → q∈(cB::LB.wires).toFinset := fun h => base (by
    simp only [eFoldTq,accFoldQ4KTq,wires_append,Finset.mem_union]; tauto)
  have e3 : q∈wires (SourceFourPrefix130Develop.fillOutKnown LB (eItem LB)) → q∈(cB::LB.wires).toFinset :=
    fun h => base (by simp only [eFoldTq,accFoldQ4KTq,wires_append,Finset.mem_union]; tauto)
  have e4 : q∈wires (midB LB) → q∈(cB::LB.wires).toFinset := fun h => hm h
  tauto

theorem efold_physical : GatePhysical efold := by
  have nd : (cB::LB.wires).Nodup :=
    List.nodup_cons.mpr ⟨LowAccCarryDevelop.control_outside,LowAccCarryDevelop.layout_nodup⟩
  have h := ParkCarry10Develop.body_physical LB LowAccCarryDevelop.layout_widths cB nd
  have hm : GatePhysical (midB LB) := qprogM_physical (coreB LB) (bitsB LB) SquareReduction.p 256 coreB_nodup bitsB_ok
  simp only [ParkCarry10Develop.body,eFoldTq,accFoldQ4KTq,gatePhysical_append] at h
  simp only [efold,eFoldB,accFoldB,gatePhysical_append]
  tauto

theorem efold_slots_le : Challenge.gateSlots efold≤Challenge.gateSlots LocalEFoldOptimize.improved := by
  have s := LocalEFoldResources.slots
  have ha : LocalEFoldAnchor.actual=eFoldTq LB cB := rfl
  rw [ha] at s
  rw [s]
  have hm := mid_slots_le
  simp only [efold,eFoldB,eFoldTq,accFoldB,accFoldQ4KTq,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.StairSquareBEFoldK
end Merge_StairSquareBEFoldK_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareContract_at_BOptimizations` -/
section Merge_StairSquareContract_at_BOptimizations

/-! # LT40: shared shapes for the square-hosting units (LT36–LT40)

The concrete square layout, the body contracts (exactly the hypotheses the record's generic square
theorems ask of a body), the record's branch wrappers with the body as a parameter, and the state
facts that hold at every branch boundary of the record core. -/

section

set_option autoImplicit false

namespace ECDSAAdd.Entrant.StairSquareContract

open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout


/-- A body: the A-body hypotheses of `SumSavedB95Square.fastCore_correct`. -/
structure BodyAOK (A : Program) : Prop where
  support : wires A ⊆ insert D0 (G0 :: K0.wires).toFinset
  eUfree : ControlLoan1589BFFold.eU K0 ∉ wires A
  frame : ∀ (base : BasisState) (M : Nat), M < 2^128 → regValue K0.core.product base = M^2 →
    K0.PairClean base → base K0.core.sumCarry = false → ∀ O, O < SquareReduction.p →
    (base G0 = false → M = 0) → base D0 = false →
    Triple (SquareFrame K0.core.out base O) A
      (SquareFrame K0.core.out base (A161Low4Offsets.resAFlow (M^2) O (base G0)))

/-- C body: the C-body hypotheses of `SumSavedB95Square.fastCore_correct`. -/
structure BodyCOK (C : Program) : Prop where
  support : wires C ⊆ insert D0 (G0 :: K0.wires).toFinset
  frame : ∀ (base : BasisState) (M : Nat), regValue K0.core.product base = M^2 → K0.PairClean base →
    (base G0 = false → M = 0) → base D0 = false → ∀ O, O < SquareReduction.p →
    Triple (SquareFrame K0.core.out base O) C
      (SquareFrame K0.core.out base (C163Low4Offsets.resCFlow (base G0) (M^2) O))


def recBrB (B : Program) : Program :=
  ParkCopy.withLowK2P K0 E0 G0 K0.core.high (K0.core.product.take 256) (R2SqEp760.bodySwap K0 E0 B)
def recBrA (A : Program) : Program := A161Low4Branch.branch K0 E0 G0 A


end ECDSAAdd.Entrant.StairSquareContract

end
end Merge_StairSquareContract_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareDirectBodyA_at_BOptimizations` -/
section Merge_StairSquareDirectBodyA_at_BOptimizations

/-! # LT37 U3a: the A square body with direct folds, parametric in the loop adder

`A109SignResearch.directBody P = (directFold negP ++ (directFold rot128F ++ P)) ++ padding 7` is the record's
`A109SignResearch.body` with both measured folds replaced by direct folds (U1) and the loop `A109SignResearch.loop`
replaced by an arbitrary program `P` that satisfies the loop's frame (`DirectLoopFrame P`, the statement of
`A109SignResearch.frame`).  For such `P`:
* `direct_body_frame P hP` has exactly the statement of `A109SignResearch.body_frame` (the `bodyFrame` hypothesis
  of `fastCore_correct` / `SumSavedB95Entry.squareEntry_eq`);
* counts: `T(directBody P) + T(loop) = T(body) + T(P)` (same for M), i.e. the folds cost exactly what the
  record folds cost;
* wires: `wires (directBody P) ⊆ wires body ∪ wires P`; hence every record support fact transfers when
  `wires P ⊆ wires body`, and the `aSupport` / `eUfree` hypotheses follow from the loop's own;
* holes: any hole list inside `L.foldPad` avoided by `P` is avoided by `directBody P` (PARAMETRIC).
New declarations live in the record's namespaces (`A161Low4Body`, `A109SignResearch`) only so that the record's
proofs can be reused verbatim; all names are new (`direct*`). No record declaration is changed. -/

-- generic helpers (no irreducible attributes here)
section
namespace ECDSAAdd.Entrant.StairSquareDirectFold
open ECDSAAdd ECDSAAdd.Entrant Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option linter.unusedSimpArgs false

theorem padding_wires (n : Nat) (w : Wire) :
    ECDSAAdd.wires (ReorderedRecordPadding.program n w)⊆{w} := by
  induction n with
  | zero => intro x hx; simp [ReorderedRecordPadding.program,ECDSAAdd.wires] at hx
  | succ n ih =>
    intro x hx
    have e : ReorderedRecordPadding.program (n+1) w=Instr.measureX w [] []::ReorderedRecordPadding.program n w := rfl
    rw [e] at hx
    simp only [ECDSAAdd.wires,Instr.wires,correctionWires,Finset.union_empty,Finset.mem_union,
      Finset.mem_singleton] at hx
    rcases hx with hx|hx
    · exact Finset.mem_singleton.mpr hx
    · exact ih hx

theorem padding_mem (n : Nat) (w : Wire) :
    w∈ECDSAAdd.wires (ReorderedRecordPadding.program (n+1) w) := by
  have e : ReorderedRecordPadding.program (n+1) w=Instr.measureX w [] []::ReorderedRecordPadding.program n w := rfl
  rw [e]
  simp [ECDSAAdd.wires,Instr.wires]

theorem foldPad_ne_cin (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) :
    ∀q∈L.foldPad,q≠L.core.cin := by
  intro q hq e
  have h := List.nodup_iff_count.mp hn q
  have a := List.count_pos_iff.mpr hq
  have c : 0<List.count q [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag,L.core.sumCarry] := List.count_pos_iff.mpr (by simp [e])
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
    CuccaroStreamedSquareWideLayout.foldPad,List.count_append] at h a
  omega

theorem padding_holes (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (n : Nat)
    (holes : List Wire) (hh : ∀q∈holes,q∈L.foldPad) :
    ∀q∈holes,q∉ECDSAAdd.wires (ReorderedRecordPadding.program n L.core.cin) :=
  fun q hq h => foldPad_ne_cin L hn q (hh q hq) (Finset.mem_singleton.mp (padding_wires n _ h))

end ECDSAAdd.Entrant.StairSquareDirectFold
end

-- generic A body frame (copy of `A161Low4Body.body_frame` with the two direct folds)
section
namespace ECDSAAdd.Entrant.A161Low4Body
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
open ECDSAAdd.Entrant.StairSquareDirectFold

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem direct_body_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) (fold : Program)
    (foldFrame : ∀ O, O<SquareReduction.p →
      Triple (SquareFrame L.core.out base O) fold
       (SquareFrame L.core.out base
        (((if base c then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
         (SquareReduction.p-1-O))%SquareReduction.p))) :
    Triple (SquareFrame L.core.out base O) (directFoldQTq L (negP L)++(directFoldQTq L (rot128F L)++fold)) (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  let P := M^2
  let O1 := (P+(SquareReduction.p-1-O))%SquareReduction.p
  let O2 := ((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p
  have hO1 : O1<SquareReduction.p := Nat.mod_lt _ pmod
  have hO2 : O2<SquareReduction.p := Nat.mod_lt _ pmod
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
  have v3 : AccView L base (aAcc L) := views (.inr (aAcc L)) (by simp [accAMix,aAcc])
  have pay1 : measuredFoldPayload base (negP L)=P := by
    simp only [measuredFoldPayload,negP,pow_zero,Nat.mul_one]
    rw [L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb]
  have pay2 : measuredFoldPayload base (rot128F L)=(P/2^128)%2^128+2^128*(P%2^128) := by
    simp only [measuredFoldPayload,rot128F,pow_zero,Nat.mul_one]
    exact L.rotated128_value hw base (M^2) hP
  have t1 : Triple (SquareFrame L.core.out base O) (directFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := directFoldQ_frameTq L hw hn base (negP L) v1 rfl hc (negP_length L hw) rfl O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (directFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := directFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc (rot128F_length L hw) rfl O1 hO1
    rwa [pay2] at h
  have hAeq : Acc.accVal base 0 (aAcc L).spec=4294968272*regValue (hiReg L) base := by
    rw [show (aAcc L).spec=earlyHTerms (L.core.product.drop 128) from rfl,accVal_earlyH]
    congr 1
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb,hP]
  have t3 := foldFrame O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  let A := Acc.accVal base 0 (aAcc L).spec
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^161 := by
    change Acc.accVal base 0 (aAcc L).spec<2^161
    rw [hAeq]
    have bound:=A161Low4Math.accumulator_div16_bound _ hH
    norm_num at bound ⊢
    omega
  have hAM : A%16=0 := by
    change Acc.accVal base 0 (aAcc L).spec%16=0
    rw [hAeq]
    omega
  have hsum := (accA_mixSum L hw base).trans (L.measuredA_sum hw base (M^2) hP hb)
  have n1 : mixNeg (.inl (rot128F L) : MixItem)=false := rfl
  have n2 : mixNeg (.inr (aAcc L) : MixItem)=false := rfl
  have n3 : mixNeg (.inl (negP L) : MixItem)=true := rfl
  have e : accAMix L=[.inl (rot128F L),.inr (aAcc L),.inl (negP L)] := rfl
  rw [e] at hsum
  simp only [mixSignedSum,mixSignedPayload,n1,n2,n3,Bool.false_eq_true,if_false,if_true,mixPayload,add_zero,
    pay1,pay2] at hsum
  change ((((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
    (((A : Nat) : ZMod SquareReduction.p)+-((P : Nat) : ZMod SquareReduction.p)))=
      ((P : Nat) : ZMod SquareReduction.p)*2^128-(P : ZMod SquareReduction.p) at hsum
  have bound : ((if base c then A161Low4Facts.Klow-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (A161Low4Facts.Klow : ZMod SquareReduction.p) else 0)))).symm
  simp only [measuredOrientationCast,if_true,Bool.false_eq_true,if_false]
  have c0 := measuredReflection_zmod O hO
  have c1 := measuredReflection_zmod O1 hO1
  have c2 := measuredReflection_zmod O2 hO2
  have k1 : (O1 : ZMod SquareReduction.p)=(P : ZMod SquareReduction.p)+(-1-(O : ZMod SquareReduction.p)) := by
    simp only [O1,ZMod.natCast_mod,Nat.cast_add,c0]
  have k2 : (O2 : ZMod SquareReduction.p)=(((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)+
      (-1-(O1 : ZMod SquareReduction.p)) := by
    rw [show O2=((P/2^128)%2^128+2^128*(P%2^128)+(SquareReduction.p-1-O1))%SquareReduction.p from rfl,
      ZMod.natCast_mod,Nat.cast_add,c1]
  rw [ZMod.natCast_mod,Nat.cast_add,c2,k2,k1]
  cases hgv : base c
  · have M0 := hg hgv
    have P0 : P=0 := by show M^2=0; rw [M0]; norm_num
    have R0 : (((P/2^128)%2^128+2^128*(P%2^128) : Nat) : ZMod SquareReduction.p)=0 := by rw [P0]; simp
    rw [R0,P0] at hsum
    simp only [Bool.false_eq_true,if_false]
    rw [R0,P0]
    have hM2 : ((M^2 : Nat) : ZMod SquareReduction.p)=0 := by rw [M0]; simp
    rw [hM2]
    simp at hsum ⊢
    linear_combination -hsum
  · simp only [if_true]
    have hAle : A≤A161Low4Facts.Klow := by unfold A161Low4Facts.Klow;norm_num at hA ⊢;omega
    have hoff : ((A161Low4Facts.Klow-A : Nat) : ZMod SquareReduction.p)=(A161Low4Facts.Klow : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum

end ECDSAAdd.Entrant.A161Low4Body
end

-- the concrete A body (record layout), parametric in the loop
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.A109SignResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
open ECDSAAdd.Entrant.StairSquareDirectFold
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

/-- The loop interface = the statement of `A109SignResearch.frame` for an arbitrary program. -/
def DirectLoopFrame (P : Program) : Prop :=
 ∀ (base:BasisState), L.PairClean base → base ReorderedAFixed.q=false → base ReorderedAFixed.r=false →
  base ReorderedAFixed.p=false → base ReorderedAFixed.d=false → ∀ (O:Nat), O<SquareReduction.p →
  Triple (SquareFrame L.core.out base O) P
   (SquareFrame L.core.out base
    (((if base ReorderedAFixed.g then A161Low4Facts.Klow-4294968272*regValue ReorderedAFixed.src base
      else 4294968272*regValue ReorderedAFixed.src base)+(SquareReduction.p-1-O))%SquareReduction.p))


def directRawBody (P : Program) : Program :=
 directFoldQTq L (negP L)++(directFoldQTq L (rot128F L)++P)

def directBody (P : Program) : Program :=
 directRawBody P++ReorderedRecordPadding.program 7 L.core.cin

theorem direct_raw_body_frame (P : Program) (hloop : DirectLoopFrame P) (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base ReorderedAFixed.q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base ReorderedAFixed.g=false → M=0) (hd:base ReorderedAFixed.d=false) :
 Triple (SquareFrame L.core.out base O) (directRawBody P)
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base ReorderedAFixed.g))) := by
 have hb:M^2<2^256:=by simpa using square_bound M 128 hM
 have vZero:base (eV L)=false:=eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
 have pZero:base (spare L)=false:=spare_zero L hw base M hP
 have ff : ∀ O, O<SquareReduction.p →
  Triple (SquareFrame L.core.out base O) P
   (SquareFrame L.core.out base (((if base ReorderedAFixed.g then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base
    else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) :=
  fun O hO=>hloop base hc hzero vZero pZero hd O hO
 exact A161Low4Body.direct_body_frame L hw hn ReorderedAFixed.g A161Low4FixedFold.ready.1 base M hM hP hc hzero O hO hg P ff

/-- Exactly the statement of `A109SignResearch.body_frame`, for `directBody P`. -/
theorem direct_body_frame (P : Program) (hloop : DirectLoopFrame P) (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base ReorderedAFixed.q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base ReorderedAFixed.g=false → M=0) (hd:base ReorderedAFixed.d=false) :
 Triple (SquareFrame L.core.out base O) (directBody P)
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base ReorderedAFixed.g))) := by
 intro s m hf
 have f:=direct_raw_body_frame P hloop base M hM hP hc hzero O hO hg hd s (m.take (measurementCount (directRawBody P))) hf
 have hz:(run (directRawBody P) (m.take (measurementCount (directRawBody P))) s).basis L.core.cin=false:=
  (f.2.2 L.core.cin (by decide)).trans hc.cin
 have eq:run (directBody P) m s=run (directRawBody P) (m.take (measurementCount (directRawBody P))) s:=by
  rw [directBody,run_append,ReorderedRecordPadding.run_zero 7 L.core.cin _ _ hz]
 exact ReorderedAFixed.transport _ s _ _ eq f

/-- The record body itself is `directBody` minus nothing but the two folds: counts move only with the loop. -/
theorem direct_body_counts (P : Program) :
 toffoliCount (directBody P)+toffoliCount A109SignResearch.loop=toffoliCount A109SignResearch.body+toffoliCount P ∧
 measurementCount (directBody P)+measurementCount A109SignResearch.loop=
  measurementCount A109SignResearch.body+measurementCount P := by
 have a:=directFoldQ_counts_eq L hw (negP L) (negP_length L hw)
 have b:=directFoldQ_counts_eq L hw (rot128F L) (rot128F_length L hw)
 simp only [directBody,directRawBody,A109SignResearch.body,A109SignResearch.rawBody,A109SignResearch.fold,
  toffoliCount_append,measurementCount_append]
 omega

theorem direct_body_wires (P : Program) :
 wires (directBody P)⊆wires A109SignResearch.body∪wires P := by
 have s1:=directFoldQ_sub_measured L hw (negP L) (negP_length L hw) rfl
 have s2:=directFoldQ_sub_measured L hw (rot128F L) (rot128F_length L hw) rfl
 have cinIn:L.core.cin∈wires (ReorderedRecordPadding.program 7 L.core.cin):=padding_mem 6 L.core.cin
 intro x hx
 have h1:x∈wires (directFoldQTq L (negP L))→x=L.core.cin ∨ x∈wires (measuredFoldQTq L (negP L)):=
  fun h=>Finset.mem_insert.mp (s1 h)
 have h2:x∈wires (directFoldQTq L (rot128F L))→x=L.core.cin ∨ x∈wires (measuredFoldQTq L (rot128F L)):=
  fun h=>Finset.mem_insert.mp (s2 h)
 have h3:x=L.core.cin→x∈wires (ReorderedRecordPadding.program 7 L.core.cin):=by
  intro e; rw [e]; exact cinIn
 simp only [directBody,directRawBody,wires_append,Finset.mem_union] at hx
 simp only [A109SignResearch.body,A109SignResearch.rawBody,A109SignResearch.fold,wires_append,Finset.mem_union]
 tauto




/-- PARAMETRIC hole avoidance: holes inside `foldPad` (e.g. the 39 = `overflowPad[76..115]`) avoided by the loop
are avoided by the whole body. -/
theorem direct_body_holes (P : Program) (holes : List Wire) (hh : ∀q∈holes,q∈L.foldPad)
 (hl : ∀q∈holes,q∉wires P) : ∀q∈holes,q∉wires (directBody P) := by
 have f1:=directFoldQ_holes L hn (negP L) (negP_count L) holes hh
 have f2:=directFoldQ_holes L hn (rot128F L) (rot128F_count L) holes hh
 have f3:=padding_holes L hn 7 holes hh
 intro x hx bad
 simp only [directBody,directRawBody,wires_append,Finset.mem_union] at bad
 rcases bad with (b|b|b)|b
 · exact f1 x hx b
 · exact f2 x hx b
 · exact hl x hx b
 · exact f3 x hx b

theorem direct_body_physical (P : Program) (hl : GatePhysical P) : GatePhysical (directBody P) := by
 have f1:=directFoldQ_physicalTq L hn (negP L) (negP_count L)
 have f2:=directFoldQ_physicalTq L hn (rot128F L) (rot128F_count L)
 have pad:GatePhysical (ReorderedRecordPadding.program 7 L.core.cin):=ReorderedPhysical.padding 7 L.core.cin
 simp only [directBody,directRawBody,gatePhysical_append]
 exact ⟨⟨f1,f2,hl⟩,pad⟩

end ECDSAAdd.Entrant.A109SignResearch
end
end Merge_StairSquareDirectBodyA_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareDirectBodyC_at_BOptimizations` -/
section Merge_StairSquareDirectBodyC_at_BOptimizations

/-! # LT37 U3c: the C square body with a direct fold, parametric in the loop adder

`C105SignResearch.directBody P = (directFold negRot ++ P) ++ padding 7` is the record's `C105SignResearch.body`
(`C163Low4Body.bodyProgram L loop ++ padding 7`, whose single fold is `measuredFoldQTq L (negRot L)`) with the fold
replaced by the direct fold (U1) and the loop replaced by any `P` satisfying `DirectLoopFrame P` (the statement of
`C105SignResearch.frame`).  Same deliverables as U3a: exact `body_frame` statement, counts moving only with the loop,
`wires ⊆ wires body ∪ wires P`, the `cSupport` hypothesis, parametric hole avoidance, physicality. -/

-- generic C body output (copy of `C163Low4Body.body_output` with the direct fold)
section
namespace ECDSAAdd.Entrant.C163Low4Body
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout OwnDiagAll12Square
 InverseCarryDevelop ThirdSavedCarryDevelop
open ECDSAAdd.Entrant.StairSquareDirectFold
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def directBodyProgram(L:CuccaroStreamedSquareWideLayout)(F:Program):Program:=directFoldQTq L (negRot L)++F

/-- The record's single C fold is the plain measured fold of `negRot`. -/
theorem mix_negRot (L : CuccaroStreamedSquareWideLayout) :
    mixFoldsQTq L false [.inl (negRot L)]=measuredFoldQTq L (negRot L) := by
  simp only [mixFoldsQTq,List.append_nil]
  rfl

theorem direct_body_output (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (control : Wire) (hn : (control::L.wires).Nodup)
    (loan:Wire) (newFold:Program) (mask:Nat)
    (cap:∀(base:BasisState)(M:Nat),regValue L.core.product base=M^2 → Acc.accVal base 0 (accCItem L).spec≤mask)
    (foldFrame:∀(base:BasisState),AccView L base (accCItem L) → L.PairClean base →
      ∀(M:Nat),regValue L.core.product base=M^2 → base loan=false →
      ∀(O:Nat),O<SquareReduction.p →
      Triple (SquareFrame L.core.out base O) newFold
        (SquareFrame L.core.out base
         (((if base control then mask-Acc.accVal base 0 (accCItem L).spec else Acc.accVal base 0 (accCItem L).spec)+
           (SquareReduction.p-1-O))%SquareReduction.p))) (M O : Nat) (hO : O<SquareReduction.p)
    (t : State) (m : List Bool) (pv : regValue L.core.product t.basis=M^2)
    (hM : t.basis control=false → M=0)
    (clean : L.PairClean t.basis) (outO : regValue L.core.out t.basis=O) (hd:t.basis loan=false) :
    (run (directBodyProgram L newFold) m t).phase=t.phase ∧
    regValue L.core.out (run (directBodyProgram L newFold) m t).basis=resCFK mask (t.basis control) (M^2) O ∧
    ∀q,q∉L.core.out → (run (directBodyProgram L newFold) m t).basis q=t.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have gW : control∉L.wires := (List.nodup_cons.mp hn).1
  have views := accC_views L hw t.basis M pv
  rw [accCMix_eq] at views
  have v1 : L.MeasuredFoldView t.basis (negRot L) := views (.inl (negRot L)) (by simp)
  have va : AccView L t.basis (accCItem L) := views (.inr (accCItem L)) (by simp)
  let mm := measurementCount (directFoldQTq L (negRot L))
  let r1 := run (directFoldQTq L (negRot L)) (m.take mm) t
  have e1' := directFoldQ_frameTq L hw nd t.basis (negRot L) v1 rfl clean (negRot_length L hw) rfl O hO
    t (m.take mm) ⟨outO,fun _ _ => rfl⟩
  have hmv : (measuredFoldPayload t.basis (negRot L)+(SquareReduction.p-1-O))%SquareReduction.p=
      mixValue t.basis false O [.inl (negRot L)] := by
    simp [mixValue,mixNeg,mixPayload,negRot]
  rw [hmv] at e1'
  have e1 : r1.phase=t.phase ∧ SquareFrame L.core.out t.basis (mixValue t.basis false O [.inl (negRot L)]) r1.basis := e1'
  let O1 := mixValue t.basis false O [.inl (negRot L)]
  have hO1 : O1<SquareReduction.p := mixValue_lt _ _ _ _ hO
  have e2 := foldFrame t.basis va clean M pv hd O1 hO1 r1 (m.drop mm) e1.2
  rw [directBodyProgram,run_append]
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
  have target : ((((if t.basis control then mask-A else A)+(SquareReduction.p-1-O1)) : Nat) : ZMod SquareReduction.p)=
      measuredOrientationCast false O+(-((M^2 : Nat) : ZMod SquareReduction.p)*2^128)+
        ((if t.basis control then mask else 0 : Nat) : ZMod SquareReduction.p) := by
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
    · have hAK : A≤mask := cap t.basis M pv
      simp only [↓reduceIte]
      rw [Nat.cast_add,Nat.cast_sub hAK,e3]
      linear_combination cast1+sum
  unfold resCFK ofCast
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [←target,ZMod.val_natCast]

end ECDSAAdd.Entrant.C163Low4Body
end

-- the concrete C body (record layout), parametric in the loop
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.C105SignResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
open ECDSAAdd.Entrant.StairSquareDirectFold
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

/-- The loop interface = the statement of `C105SignResearch.frame` for an arbitrary program. -/
def DirectLoopFrame (P : Program) : Prop :=
 ∀ (base:BasisState), L.PairClean base → base C163Low4Middle.p=false → base d=false →
  ∀ (O:Nat), O<SquareReduction.p →
  Triple (SquareFrame L.core.out base O) P
   (SquareFrame L.core.out base
    (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
     (SquareReduction.p-1-O))%SquareReduction.p))


theorem direct_fold_frame (P : Program) (hloop : DirectLoopFrame P)
 (base:BasisState)(hv:AccView L base (OwnDiagAll12Square.accCItem L))(hc:L.PairClean base)
 (M:Nat)(pv:regValue L.core.product base=M^2)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) P
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-Acc.accVal base 0 (OwnDiagAll12Square.accCItem L).spec else Acc.accVal base 0 (OwnDiagAll12Square.accCItem L).spec)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have f:=hloop base hc (spare_zero L hw base M pv) hd O hO s m hf
 have e:=congrArg (fun A:Nat=>((if base g then C163Low4Facts.Klow-A else A)+(SquareReduction.p-1-O))%SquareReduction.p)
  (C163Fold.payload_spec L base)
 exact ⟨f.1,Eq.mp (congrArg (fun n:Nat=>SquareFrame L.core.out base n (run P m s).basis) e) f.2⟩

def directRawBody (P : Program) : Program := C163Low4Body.directBodyProgram L P

def directBody (P : Program) : Program := directRawBody P++ReorderedRecordPadding.program 7 L.core.cin

theorem direct_raw_body_frame (P : Program) (hloop : DirectLoopFrame P)
 (base:BasisState)(M:Nat)(pv:regValue L.core.product base=M^2)
 (clean:L.PairClean base)(disabled:base g=false→M=0)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (directRawBody P)
  (SquareFrame L.core.out base (C163Low4Body.resCFK C163Low4Facts.Klow (base g) (M^2) O)):=by
 intro s m hf
 have away(q:Wire)(hq:q∈L.core.product):q∉L.core.out:=
  fun ho=>List.disjoint_left.mp (L.product_out_disjoint hn) hq ho
 have prod:regValue L.core.product s.basis=M^2:=
  (regValue_congr _ _ _ (fun q hq=>hf.2 q (away q hq))).trans pv
 have cs:=L.squareFrame_clean hn base s.basis O hf clean
 have gs:s.basis g=base g:=hf.2 g (by decide)
 have ds:s.basis d=false:=(hf.2 d (by decide)).trans hd
 have dm:s.basis g=false→M=0:=by rw [gs];exact disabled
 have out:=C163Low4Body.direct_body_output L hw g (List.nodup_cons.mpr ⟨geometry.1,hn⟩)
  d P C163Low4Facts.Klow cap (direct_fold_frame P hloop) M O hO s m prod dm cs hf.1 ds
 rw [gs] at out
 exact ⟨out.1,out.2.1,fun q hq=>(out.2.2 q hq).trans (hf.2 q hq)⟩

/-- Exactly the statement of `C105SignResearch.body_frame`, for `directBody P`. -/
theorem direct_body_frame (P : Program) (hloop : DirectLoopFrame P)
 (base:BasisState)(M:Nat)(pv:regValue L.core.product base=M^2)
 (clean:L.PairClean base)(disabled:base g=false→M=0)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (directBody P)
  (SquareFrame L.core.out base (C163Low4Body.resCFK C163Low4Facts.Klow (base g) (M^2) O)):=by
 intro s m hf
 have f:=direct_raw_body_frame P hloop base M pv clean disabled hd O hO s (m.take (measurementCount (directRawBody P))) hf
 have hz:(run (directRawBody P) (m.take (measurementCount (directRawBody P))) s).basis L.core.cin=false:=
  (f.2.2 L.core.cin (by decide)).trans clean.cin
 have eq:run (directBody P) m s=run (directRawBody P) (m.take (measurementCount (directRawBody P))) s:=by
  rw [directBody,run_append,ReorderedRecordPadding.run_zero 7 L.core.cin _ _ hz]
 exact ReorderedCFixed.transport _ s _ _ eq f

theorem direct_body_counts (P : Program) :
 toffoliCount (directBody P)+toffoliCount C105SignResearch.loop=toffoliCount C105SignResearch.body+toffoliCount P ∧
 measurementCount (directBody P)+measurementCount C105SignResearch.loop=
  measurementCount C105SignResearch.body+measurementCount P := by
 have a:=directFoldQ_counts_eq L hw (negRot L) (negRot_length L hw)
 have e:=C163Low4Body.mix_negRot L
 simp only [directBody,directRawBody,C163Low4Body.directBodyProgram,C105SignResearch.body,C105SignResearch.rawBody,
  C163Low4Body.bodyProgram,e,toffoliCount_append,measurementCount_append]
 omega

theorem direct_body_wires (P : Program) :
 wires (directBody P)⊆wires C105SignResearch.body∪wires P := by
 have s1:=directFoldQ_sub_measured L hw (negRot L) (negRot_length L hw) rfl
 have cinIn:L.core.cin∈wires (ReorderedRecordPadding.program 7 L.core.cin):=padding_mem 6 L.core.cin
 have e:=C163Low4Body.mix_negRot L
 intro x hx
 have h1:x∈wires (directFoldQTq L (negRot L))→x=L.core.cin ∨ x∈wires (measuredFoldQTq L (negRot L)):=
  fun h=>Finset.mem_insert.mp (s1 h)
 have h3:x=L.core.cin→x∈wires (ReorderedRecordPadding.program 7 L.core.cin):=by
  intro e'; rw [e']; exact cinIn
 simp only [directBody,directRawBody,C163Low4Body.directBodyProgram,wires_append,Finset.mem_union] at hx
 simp only [C105SignResearch.body,C105SignResearch.rawBody,C163Low4Body.bodyProgram,e,wires_append,Finset.mem_union]
 rcases hx with (hx|hx)|hx
 · rcases h1 hx with h|h
   · exact Or.inl (Or.inr (h3 h))
   · exact Or.inl (Or.inl (Or.inl h))
 · exact Or.inr hx
 · exact Or.inl (Or.inr hx)



/-- PARAMETRIC hole avoidance (holes inside `foldPad`). -/
theorem direct_body_holes (P : Program) (holes : List Wire) (hh : ∀q∈holes,q∈L.foldPad)
 (hl : ∀q∈holes,q∉wires P) : ∀q∈holes,q∉wires (directBody P) := by
 have f1:=directFoldQ_holes L hn (negRot L) (negRot_count L) holes hh
 have f3:=padding_holes L hn 7 holes hh
 intro x hx bad
 simp only [directBody,directRawBody,C163Low4Body.directBodyProgram,wires_append,Finset.mem_union] at bad
 rcases bad with (b|b)|b
 · exact f1 x hx b
 · exact hl x hx b
 · exact f3 x hx b

theorem direct_body_physical (P : Program) (hl : GatePhysical P) : GatePhysical (directBody P) := by
 have f1:=directFoldQ_physicalTq L hn (negRot L) (negRot_count L)
 have pad:GatePhysical (ReorderedRecordPadding.program 7 L.core.cin):=ReorderedPhysical.padding 7 L.core.cin
 simp only [directBody,directRawBody,C163Low4Body.directBodyProgram,gatePhysical_append]
 exact ⟨⟨f1,hl⟩,pad⟩

end ECDSAAdd.Entrant.C105SignResearch
end
end Merge_StairSquareDirectBodyC_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSqLoopA_at_BOptimizations` -/
section Merge_StairSqLoopA_at_BOptimizations

/-! # LT38 / U2a: hole-free A loop

The record's A loop `A109SignResearch.loop` keeps 109 cached carries on the cache hosts.  The record also proves
that its NON-cached form `F ++ M ++ (I ++ clear ++ tail)` is run-equal to the plain loop
(`A109Research.plain_loop`).  The non-cached loop never touches the 103 hosts `ReorderedAFixed.hosts`, which are zero
at loop entry, so the hole sites can be renamed onto them for the whole loop (`StairSquareHolesCore.hostRename`).
Cost: +112 Toffoli (the cache saves 109 + 3), same measurements. -/

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked

/-- The record's non-cached A core (`F ++ M ++ (I ++ clear ++ tail)`). -/
def ncCore:Program:=A109Research.F++A109Research.M++(A109Research.I++A109LowEraseResearch.clear++A109Research.tail)

theorem hosts_of_hs(u:Wire)(hu:u∈ReorderedAFixed.hs):u∈ReorderedAFixed.hosts:=by
 simp only [ReorderedAFixed.hosts,List.mem_cons]
 exact Or.inr (Or.inr (Or.inr hu))

/-- Copy of `A109Research.core_frame` with `core_plain` replaced by `plain_loop`. -/
theorem ncCore_frame(base:BasisState)(hc:L.PairClean base)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) ncCore
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hzFull:∀u∈accZ L,s.basis u=false:=by
  intro u hu
  rcases accZ_mem L u hu with hu|hu
  · exact (regValue_zero _ _).mp clean.pad u hu
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>hzFull u ((FullPadDevelop.pad_sublist L).subset hu)
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue acc s.basis=0:=ghostAcc_zero L s.basis clean
 have zeroU:∀u∈ReorderedAFixed.hs,s.basis u=false:=fun u hu=>
  (hf.2 u (A161Low4FixedFold.hostClean base hc hd u hu).1).trans (A161Low4FixedFold.hostClean base hc hd u hu).2
 have offHs:∀u∈ReorderedAFixed.hs,u∉wires (ReorderedAPlain.build acc pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (hosts_of_hs u hu)).1
 have goodOriginal:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) (A161Low4Fold.aMiddle L g) s m):=by
  rw [ReorderedARetape.a_middle_eq acc pad bank L.core.cin src (A161Low4Fold.aMiddle L g)
   lengths.1 lengths.2.2.2 fits s m hz hb clean.cin ha]
  exact good_old base hc O hO s _ hf
 have middleEq:=A161Low4FixedFold.cert100.middle_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle L g)
  A161Low4FixedFold.checked.out (ReorderedAPlain.build acc pad bank L.core.cin src) s m zeroU offHs
 have good:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out s m):=by
  rw [middleEq]
  exact goodOriginal
 have knownEq:=AKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
 have goodKnown:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) KnownAMidStaged.body s m):=by
  rw [knownEq]
  exact good
 have buildFrame:=ReorderedAPlain.build_triple acc pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
  s.basis hz hb clean.cin s (m.take (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  ⟨ha,fun _ _=>rfl⟩
 have flag:(run (ReorderedAPlain.build acc pad bank L.core.cin src)
  (m.take (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src))) s).basis 4762=false:=
  (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
 have plainNew:=A109Research.plain_loop s m hz hb clean.cin ha goodKnown flag
 have midEq:run KnownAMidStaged.body (m.drop (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s)=
  run A161Low4FixedFold.checked.out (m.drop (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using knownEq
 have ctxt:=ReorderedKnownA.context_eq
  (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out KnownAMidStaged.body
  (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m AKnownMiddleResearch.measurements midEq
 have plain:=plainNew.trans ctxt
 have middleReplace:=A161Low4FixedFold.cert100.surround_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle L g)
  A161Low4FixedFold.checked.out (ReorderedAPlain.build acc pad bank L.core.cin src)
  (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m zeroU offHs
 have eq:run ncCore m s=run (ReorderedAPlain.build acc pad bank L.core.cin src++A161Low4Fold.aMiddle L g++
  ReorderedAPlain.unbuild acc pad bank L.core.cin src) m s:=plain.trans middleReplace
 exact transport _ s _ _ eq (plain_frame base hc O hO s m hf)

/-- The non-cached loop with the record's sign head. -/
def suffixNC:Program:=A109LowEraseResearch.clear++A109Research.rawF++A109Research.top++A109Research.M++
 A109Research.I++A109LowEraseResearch.clear++A109Research.tail

def loopNC:Program:=SignAHead.head++suffixNC

end ECDSAAdd.Entrant.StairSqLoopA

end

-- The non-cached loop never touches the 103 hosts.
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem clear_wires:wires A109LowEraseResearch.clear=([4243,4505,4244,4506,4245,4507]:List Wire).toFinset:=by
 ext q
 simp [A109LowEraseResearch.clear,wires,Instr.wires,correctionWires]
 tauto

theorem tail_eq:A109Research.tail=ReorderedAUnbuild.after acc pad bank L.core.cin src:=by
 have aa:ReorderedAFixed.acc=ReorderedBPrefixResearch.acc:=by decide +kernel
 have ap:ReorderedAFixed.pad=ReorderedBPrefixResearch.pad:=by decide +kernel
 have ab:ReorderedAFixed.bank=ReorderedBPrefixResearch.bank:=by decide +kernel
 have ax:ReorderedAFixed.src=ReorderedBPrefixResearch.src:=by decide +kernel
 have ai:ReorderedAFixed.L.core.cin=ReorderedBPrefixResearch.cin:=by decide +kernel
 rw [aa,ap,ab,ax,ai]

theorem loopNC_off(h:Wire)(hh:h∈ReorderedAFixed.hosts):h∉wires loopNC:=by
 have hA:h∈A109Research.hosts:=by
  simp only [A109Research.hosts,List.mem_append]
  exact Or.inl hh
 have op:=off_plain h hh
 have hb:=op.1
 rw [ReorderedABuild.plain_split acc pad bank L.core.cin src lengths.2.2.2] at hb
 simp only [wires_append,Finset.mem_union,not_or] at hb
 have headOff:h∉wires SignAHead.head:=fun bad=>hb.1.1 (SignAHeadSupport.support bad)
 have clearOff:h∉wires A109LowEraseResearch.clear:=by
  rw [clear_wires]
  intro bad
  have sub:([4243,4505,4244,4506,4245,4507]:List Wire)⊆A109Research.ports:=by decide
  exact A109Research.old_away h hh (sub (List.mem_toFinset.mp bad))
 have ht:=op.2
 rw [ReorderedAUnbuild.plain_split acc pad bank L.core.cin src lengths.2.2.2] at ht
 simp only [wires_append,Finset.mem_union,not_or] at ht
 have tailOff:h∉wires A109Research.tail:=by
  rw [tail_eq]
  exact ht.2
 simp only [loopNC,suffixNC,wires_append,Finset.mem_union,not_or,and_assoc]
 exact ⟨headOff,clearOff,A109Research.rawF_off h hA,A109Research.top_off h hA,A109Research.middle_fresh h hA,
  A109Research.I_off h hA,clearOff,tailOff⟩

end ECDSAAdd.Entrant.StairSqLoopA

end

-- Counts, slots, physical, support of the non-cached loop.
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.StairSqLoopA
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

section counts
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem loopNC_counts:toffoliCount loopNC=toffoliCount A109SignResearch.loop+112 ∧
 measurementCount loopNC=measurementCount A109SignResearch.loop:=by
 have ai:ReorderedAFixed.L.core.cin=ReorderedBPrefixResearch.L.core.cin:=by decide +kernel
 have nc:=ReorderedGenericCache.count_balance 109 A109Research.xs A109Research.ys A109Research.cs
  A109Research.hosts ReorderedBPrefixResearch.cin
  (by rw [A109Research.raw_lengths.1];decide) (by rw [A109Research.raw_lengths.2.1];decide)
  (by rw [A109Research.raw_lengths.2.2];decide)
 have ni:=HighConsumedA109Research.sub_toffoli
 have nm:=HighConsumedA109Research.sub_measurements
 simp only [ReorderedConsumedSub.consumed,toffoliCount_append,measurementCount_append] at ni nm
 -- LT50 (replay budget): definitions unfolded by `rw` and the omega atoms aligned by explicit program
 -- equalities (`simp only [defs] at *` cast the sums: the kernel evaluated both Toffoli counts, 49 s)
 rw [loopNC,suffixNC,A109SignResearch.loop,A109SignResearch.suffix,A109Research.I,A109Research.newI,
  A109Research.rawI,A109Research.rawF,ReorderedConsumedSub.plain]
 simp only [toffoliCount_append,measurementCount_append]
 have P1:ReorderedGenericCache.cachedAdd 109 A109Research.xs A109Research.ys A109Research.cs
   A109SignResearch.hosts ReorderedAFixed.L.core.cin=
  ReorderedGenericCache.cachedAdd 109 A109Research.xs A109Research.ys A109Research.cs
   A109Research.hosts ReorderedBPrefixResearch.cin:=by
  simp only [A109SignResearch.hosts,ReorderedBPrefixResearch.cin,ai]
 have P2:notRegister HighConsumedA109Research.ys=notRegister A109Research.ys:=by
  simp only [HighConsumedA109Research.ys,A109Research.ys]
 have P3:ReorderedGenericCache.consumedAdd 109 HighConsumedA109Research.xs HighConsumedA109Research.ys
   HighConsumedA109Research.cs HighConsumedA109Research.hs HighConsumedA109Research.cin=
  ReorderedGenericCache.consumedAdd 109 A109Research.xs A109Research.ys A109Research.cs
   A109Research.hosts ReorderedBPrefixResearch.cin:=by
  simp only [A109Research.xs,A109Research.ys,A109Research.cs,HighConsumedA109Research.xs,
   HighConsumedA109Research.ys,HighConsumedA109Research.cs,HighConsumedA109Research.cin,
   HighConsumedA109Research.hs,ReorderedBPrefixResearch.cin,A109SignResearch.hosts,ai]
 rw [P1]
 rw [P2,P3] at ni nm
 exact ⟨by omega,by omega⟩

theorem loopNC_slots:Challenge.gateSlots loopNC=Challenge.gateSlots A109SignResearch.loop+330:=by
 have ai:ReorderedAFixed.L.core.cin=ReorderedBPrefixResearch.L.core.cin:=by decide +kernel
 have nc:=ReorderedSlots.cache 109 A109Research.xs A109Research.ys A109Research.cs
  A109Research.hosts ReorderedBPrefixResearch.cin
  (by rw [A109Research.raw_lengths.1];decide) (by rw [A109Research.raw_lengths.2.1];decide)
  (by rw [A109Research.raw_lengths.2.2];decide) A109Research.geometry.2.1
 have ni:=HighConsumedA109Research.sub_slots
 simp only [ReorderedConsumedSub.consumed,Challenge.gateSlots_append] at ni
 -- LT50 (replay budget): as in `loopNC_counts` (46 s → ≈ 0)
 rw [loopNC,suffixNC,A109SignResearch.loop,A109SignResearch.suffix,A109Research.I,A109Research.newI,
  A109Research.rawI,A109Research.rawF,ReorderedConsumedSub.plain]
 simp only [Challenge.gateSlots_append]
 have P1:ReorderedGenericCache.cachedAdd 109 A109Research.xs A109Research.ys A109Research.cs
   A109SignResearch.hosts ReorderedAFixed.L.core.cin=
  ReorderedGenericCache.cachedAdd 109 A109Research.xs A109Research.ys A109Research.cs
   A109Research.hosts ReorderedBPrefixResearch.cin:=by
  simp only [A109SignResearch.hosts,ReorderedBPrefixResearch.cin,ai]
 have P2:notRegister HighConsumedA109Research.ys=notRegister A109Research.ys:=by
  simp only [HighConsumedA109Research.ys,A109Research.ys]
 have P3:ReorderedGenericCache.consumedAdd 109 HighConsumedA109Research.xs HighConsumedA109Research.ys
   HighConsumedA109Research.cs HighConsumedA109Research.hs HighConsumedA109Research.cin=
  ReorderedGenericCache.consumedAdd 109 A109Research.xs A109Research.ys A109Research.cs
   A109Research.hosts ReorderedBPrefixResearch.cin:=by
  simp only [A109Research.xs,A109Research.ys,A109Research.cs,HighConsumedA109Research.xs,
   HighConsumedA109Research.ys,HighConsumedA109Research.cs,HighConsumedA109Research.cin,
   HighConsumedA109Research.hs,ReorderedBPrefixResearch.cin,A109SignResearch.hosts,ai]
 rw [P1]
 rw [P2,P3] at ni
 omega

end counts

section physical
attribute [local irreducible] GatePhysical ECDSAAdd.wires

end physical

section support
attribute [local irreducible] ECDSAAdd.wires

theorem rawI_support:wires A109Research.rawI⊆A109Research.domain.toFinset:=by
 have ysSub:A109Research.ys.toFinset⊆A109Research.domain.toFinset:=by
  intro w hw
  apply List.mem_toFinset.mpr
  have hy:w∈A109Research.ys:=List.mem_toFinset.mp hw
  simp only [A109Research.domain,List.mem_cons,List.mem_append]
  tauto
 simp only [A109Research.rawI,ReorderedConsumedSub.plain,wires_append,notRegister_wires]
 change (A109Research.ys.toFinset∪wires A109Research.rawF)∪A109Research.ys.toFinset⊆A109Research.domain.toFinset
 rw [A109Research.raw_wires]
 exact Finset.union_subset (Finset.union_subset ysSub (Finset.Subset.refl _)) ysSub

theorem loopNC_support:wires loopNC⊆A109Research.S:=by
 have hh:wires SignAHead.head⊆A109Research.S:=by
  apply Finset.Subset.trans ?_ A109Research.old_prefix_support
  rw [A109Research.oldPrefix,wires_append]
  exact Finset.subset_union_left
 have dom:A109Research.domain.toFinset⊆A109Research.S:=Finset.subset_union_left.trans A109Research.raw_domain_in
 have rf:wires A109Research.rawF⊆A109Research.S:=by
  rw [A109Research.raw_wires]
  exact dom
 have ii:wires A109Research.I⊆A109Research.S:=by
  simp only [A109Research.I,wires_append]
  exact Finset.union_subset A109Research.endpoint_support.2.1 (rawI_support.trans dom)
 simp only [loopNC,suffixNC,wires_append,Finset.union_subset_iff]
 exact ⟨hh,⟨⟨⟨⟨⟨⟨A109Research.clear_support,rf⟩,A109Research.endpoint_support.1⟩,A109Research.middle_support⟩,ii⟩,
  A109Research.clear_support⟩,A109Research.endpoint_support.2.2⟩⟩

end support

end ECDSAAdd.Entrant.StairSqLoopA

end

-- PSQ-A: partial carry cache in the hole-free A square loop.
-- The 44 hole hosts `ReorderedAFixed.hs.take 44` stay out of the cache; the other 65 of the 109 cache hosts,
-- the three status hosts `ReorderedAFixed.hosts.take 3` included (clean at loop entry), keep their carries (65 T saved).
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.A109Research
open ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def keepK:List Wire:=hosts.filter (fun q=>!((ReorderedAFixed.hs.take 44).contains q))

theorem keepK_geometry:keepK.Nodup ∧ keepK.length=65 ∧
 (∀i,i<44→ReorderedAFixed.hs.getD i 0∉keepK):=by decide +kernel

theorem keepK_sub(q:Wire)(hq:q∈keepK):q∈hosts:=(List.mem_filter.mp hq).1

def rawFK:Program:=ReorderedGenericCache.cachedAdd 65 xs ys cs keepK cin
def newFK:Program:=head++A109LowEraseResearch.clear++ReorderedGenericCache.cachedAdd 65 xs ys cs keepK cin++top
def newIK:Program:=preInv++ReorderedConsumedSub.consumed 65 xs ys cs keepK cin

theorem inverse_frameK(s:State)(m:List Bool)(H:Nat)(hH:H<2^128)
 (hz:∀q∈cs,(run preInv m s).basis q=false)(hi:(run preInv m s).basis cin=false)
 (source:regValue xs (run preInv m s).basis=H)
 (target:regValue ys (run preInv m s).basis=976*H/1024)
 (saved:keepK.map s.basis=ReorderedCacheBits.values 4 65 H (976*H/1024)):
 run newIK m s=scatterState keepK (List.replicate keepK.length false) (run I m s):=by
 have same:keepK.map (run preInv m s).basis=keepK.map s.basis:=by
  apply List.map_congr_left
  intro q hq
  exact run_preserves_outside preInv m s q (preInv_off q (keepK_sub q hq))
 simp only [newIK,I,ControlledBorrowResearch.run_cat]
 exact ReorderedConsumedSub.frame 65 xs ys cs keepK cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
  raw_nd keepK_geometry.1 keepK_geometry.2.1 (fun q hq=>geometry.2.2 q (keepK_sub q hq))
  (run preInv m s) _ hz hi H (976*H/1024) source target (same.trans saved)

theorem forward_frameK(s:State)(m:List Bool)(H:Nat)
 (zero:∀q∈keepK,(run (head++A109LowEraseResearch.clear) (m.take (measurementCount (head++A109LowEraseResearch.clear))) s).basis q=false)
 (values:(((cs.drop 4).take 65).map (run (carryPrefix (4+65) xs ys cs cin) []
  (run (head++A109LowEraseResearch.clear) (m.take (measurementCount (head++A109LowEraseResearch.clear))) s)).basis)=
   ReorderedCacheBits.values 4 65 H (976*H/1024)):
 run newFK m s=scatterState keepK (ReorderedCacheBits.values 4 65 H (976*H/1024)) (run F m s):=by
 have h:=CacheBetweenFrameResearch.forward (head++A109LowEraseResearch.clear) top 65 xs ys cs keepK cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  keepK_geometry.1 (fun q hq bad=>geometry.2.2 q (keepK_sub q hq) (by simp only [List.mem_cons,List.mem_append];tauto))
  (fun q hq=>rawF_off q (keepK_sub q hq)) (fun q hq=>top_off q (keepK_sub q hq)) s m zero
 rw [values] at h
 exact h

theorem forward_measurementsK:measurementCount newFK=measurementCount F:=by
 have h:=(ReorderedGenericCache.count_balance 65 xs ys cs keepK cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)).2.1
 simp only [newFK,F,rawF,measurementCount_append]
 rw [h]

theorem forward_zeroK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedAFixed.hosts,s.basis q=false):
 ∀q∈keepK,(run F m s).basis q=false:=by
 rw [forward_erased s m hz hb hi ha]
 let u:=run (ReorderedAPlain.build acc pad bank cin src) m s
 have ready:WReady acc pad bank cin src (regValue src s.basis) u:=
  BRelocatedReadyResearch.plain_before s m hz hb hi ha
 intro q hk
 have hq:=keepK_sub q hk
 rcases List.mem_append.mp hq with hq|hq
 · rw [A109LowEraseResearch.bit_same _ q (by
    have away:=old_away q hq
    intro bad
    apply away
    simp only [A109LowEraseResearch.low,List.mem_cons,List.not_mem_nil,or_false] at bad
    rcases bad with rfl|rfl|rfl <;>decide)]
   exact (run_preserves_outside _ m s q (old_plain_off398 q hq)).trans (zero q hq)
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
   · rw [A109LowEraseResearch.bit_same _ _ (by decide)]
     simpa only [show acc.getD 0 0=4757 from by decide +kernel] using
      (LowWordRecovery.low_register_zero acc u.basis _ 0 (by decide)
       (by rw [acc_length];decide) ready.1)
   · rw [A109LowEraseResearch.bit_same _ _ (by decide)]
     simpa only [show acc.getD 1 0=4758 from by decide +kernel] using
      (LowWordRecovery.low_register_zero acc u.basis _ 1 (by decide)
       (by rw [acc_length];decide) ready.1)
   · rw [A109LowEraseResearch.bit_same _ _ (by decide)]
     simpa only [show acc.getD 2 0=4759 from by decide +kernel] using
      (LowWordRecovery.low_register_zero acc u.basis _ 2 (by decide)
       (by rw [acc_length];decide) ready.1)
   · exact A109LowEraseResearch.zero _ _ (by decide)
   · exact A109LowEraseResearch.zero _ _ (by decide)
   · exact A109LowEraseResearch.zero _ _ (by decide)

theorem prefix_zeroK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedAFixed.hosts,s.basis q=false):
 ∀q∈keepK,(run (head++A109LowEraseResearch.clear) m s).basis q=false:=by
 have clean:=forward_zeroK s m hz hb hi ha zero
 intro q hq
 have off:q∉wires (rawF++top):=by
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨rawF_off q (keepK_sub q hq),top_off q (keepK_sub q hq)⟩
 have eq:(run F m s).basis q=(run (head++A109LowEraseResearch.clear) m s).basis q:=by
  have partition:F=(head++A109LowEraseResearch.clear)++(rawF++top):=by simp only [F,List.append_assoc]
  rw [partition,run_cat]
  exact run_preserves_outside _ _ _ q off
 exact eq.symm.trans (clean q hq)

theorem forward_valuesK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 (((cs.drop 4).take 65).map (run (carryPrefix (4+65) xs ys cs cin) []
  (run (head++A109LowEraseResearch.clear) m s)).basis)=
 ReorderedCacheBits.values 4 65 (regValue src s.basis) (976*regValue src s.basis/1024):=by
 let H:=regValue src s.basis
 let u:=run head m s
 let t:=run (head++A109LowEraseResearch.clear) m s
 have te:t=A109LowEraseResearch.erase u:=prefix_erased s m hz hb hi ha
 have hH:H<2^128:=by simpa only [H,source_length] using regValue_lt src s.basis
 have ready:(∀q∈cs,u.basis q=false) ∧ u.basis cin=false ∧ regValue xs u.basis=H ∧
  regValue ys u.basis=((2^138-48*H)%2^138)/1024:=by
  simpa only [cs,xs,ys,u,head,H] using
   ReorderedHeadArithmeticResearch.ready acc pad bank cin src acc_length source_length fits s m hz hb hi ha
 have eraseBit(q:Wire)(hq:q∈domain):t.basis q=u.basis q:=by
  rw [te]
  exact A109LowEraseResearch.bit_same _ q (domain_away_low q hq)
 have eraseReg(r:List Wire)(sub:∀q∈r,q∈domain):regValue r t.basis=regValue r u.basis:=
  regValue_congr _ _ _ (fun q hq=>eraseBit q (sub q hq))
 have sy:regValue ys t.basis=((2^138-48*H)%2^138)/1024:=
  (eraseReg ys y_in).trans ready.2.2.2
 have sh:regValue xs t.basis=H:=
  (eraseReg xs x_in).trans ready.2.2.1
 have sb:∀q∈cs,t.basis q=false:=by
  intro q hq
  exact (eraseBit q (c_in q hq)).trans (ready.1 q hq)
 have si:t.basis cin=false:=
  (eraseBit cin cin_in).trans ready.2.1
 exact ReorderedCacheBits.forward_values 4 65 H (((2^138-48*H)%2^138)/1024) (976*H/1024)
  xs ys cs cin t (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide) raw_nd sb si sh sy (fun j hj=>by
   simpa only [show 128+10=138 by decide] using
    ReorderedCacheArithmetic.high_add_low 128 (4+j+1) H (by omega) hH)

theorem scattered_erased_domainK(s:State)(vs:List Bool)(q:Wire)(hq:q∈domain):
 (scatterState keepK vs (A109LowEraseResearch.erase s)).basis q=s.basis q:=by
 rw [scatter_outside keepK vs _ q (by intro bad;exact geometry.2.2 q (keepK_sub q bad) hq)]
 exact A109LowEraseResearch.bit_same s q (domain_away_low q hq)

theorem inverse_readyK(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 let vs:=ReorderedCacheBits.values 4 65 H (976*H/1024)
 let t:=scatterState keepK vs (A109LowEraseResearch.erase s)
 run newIK m t=scatterState keepK (List.replicate keepK.length false) (run I m t):=by
 dsimp only
 let vs:=ReorderedCacheBits.values 4 65 H (976*H/1024)
 let t:=scatterState keepK vs (A109LowEraseResearch.erase s)
 have hH:H<2^128:=by rw [←ready.2.1];simpa only [source_length] using regValue_lt src s.basis
 have commute:run preInv m t=scatterState keepK vs (A109LowEraseResearch.erase (run preInv m s)):=by
  rw [show t=scatterState keepK vs (A109LowEraseResearch.erase s) from rfl,
   run_scatter preInv keepK vs _ _ (fun q hq=>preInv_off q (keepK_sub q hq)),
   A109LowEraseResearch.commute preInv m s (fun q hq=>preInv_off q (low_hosts q hq))]
 have bits(q:Wire)(hq:q∈domain):(run preInv m t).basis q=(run preInv m s).basis q:=by
  rw [commute]
  exact scattered_erased_domainK _ vs q hq
 have regs(r:List Wire)(sub:∀q∈r,q∈domain):regValue r (run preInv m t).basis=regValue r (run preInv m s).basis:=
  regValue_congr _ _ _ (fun q hq=>bits q (sub q hq))
 have rr:=pre_raw_ready H s m ready
 have saved:keepK.map t.basis=vs:=scatter_saved_map keepK vs _ keepK_geometry.1
  (by simp only [vs,ReorderedCacheBits.values,List.length_map,keepK_geometry.2.1,List.length_range])
 apply inverse_frameK t m H hH
 · intro q hq
   rw [bits q (c_in q hq)]
   exact rr.1 q hq
 · rw [bits cin cin_in]
   exact rr.2.1
 · rw [regs xs x_in]
   exact rr.2.2.1
 · rw [regs ys y_in]
   exact rr.2.2.2
 · exact saved

theorem cache_loopK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedAFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run (newFK++M++newIK) m s=run (F++M++I) m s:=by
 let H:=regValue src s.basis
 let vs:=ReorderedCacheBits.values 4 65 H (976*H/1024)
 have mid:=middle_erased s m hz hb hi ha after flag
 have forward:=forward_frameK s (m.take (measurementCount F)) H
  (prefix_zeroK s _ hz hb hi ha zero) (forward_valuesK s _ hz hb hi ha)
 apply CacheFromCleanForwardResearch.equivalent F newFK M I newIK keepK vs
  forward_measurementsK (fun q hq=>middle_fresh q (keepK_sub q hq)) (fun q hq=>I_off q (keepK_sub q hq))
  keepK_geometry.1 s m (forward_zeroK s _ hz hb hi ha zero) forward
 rw [mid]
 exact inverse_readyK H (middleState oldF oldM s m) _ after

def coreK:Program:=(newFK++M++newIK)++(A109LowEraseResearch.clear++tail)

theorem inverse_measurementsK:measurementCount newIK=measurementCount I:=by
 have h:=ReorderedConsumedSub.measurement_eq 65 xs ys cs keepK cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide)
 have eq:measurementCount (ReorderedConsumedSub.consumed 65 xs ys cs keepK cin)=measurementCount rawI:=h
 simp only [newIK,I,measurementCount_append,eq]

theorem prefix_measurementsK:measurementCount (newFK++M++newIK)=measurementCount (F++M++I):=by
 simp only [measurementCount_append,forward_measurementsK,inverse_measurementsK]

theorem core_plainK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedAFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run coreK m s=run (oldF++oldM++ReorderedAPlain.unbuild acc pad bank cin src) m s:=by
 have eq:=ClearContextResearch.append_at (newFK++M++newIK) (F++M++I) (A109LowEraseResearch.clear++tail)
  s m prefix_measurementsK (cache_loopK s m hz hb hi ha zero after flag)
 have shape:(F++M++I)++(A109LowEraseResearch.clear++tail)=F++M++(I++A109LowEraseResearch.clear++tail):=by
  have g(A B C D E:Program):(A++B++C)++(D++E)=A++B++(C++D++E):=by simp only [List.append_assoc]
  exact g F M I A109LowEraseResearch.clear tail
 exact eq.trans ((congrArg (fun P=>run P m s) shape).trans (plain_loop s m hz hb hi ha after flag))

end ECDSAAdd.Entrant.A109Research
end

-- PSQ-A: the partial-cache A loop (`loopPC`) and its frame, host avoidance, counts, slots, physicality, support.
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked

def pcCore:Program:=A109Research.coreK

theorem pcCore_frame(base:BasisState)(hc:L.PairClean base)
 (hsum:base A161Low4FixedFold.q=false)(hV:base A161Low4FixedFold.r=false)(hP:base A161Low4FixedFold.p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) pcCore
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hzFull:∀u∈accZ L,s.basis u=false:=by
  intro u hu
  rcases accZ_mem L u hu with hu|hu
  · exact (regValue_zero _ _).mp clean.pad u hu
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>hzFull u ((FullPadDevelop.pad_sublist L).subset hu)
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue acc s.basis=0:=ghostAcc_zero L s.basis clean
 have zeroU:∀u∈ReorderedAFixed.hs,s.basis u=false:=fun u hu=>
  (hf.2 u (A161Low4FixedFold.hostClean base hc hd u hu).1).trans (A161Low4FixedFold.hostClean base hc hd u hu).2
 -- the three status hosts are clean at loop entry (as in `A109Research.core_frame`)
 have zeroOld:∀u∈ReorderedAFixed.hosts,s.basis u=false:=by
  have qz:s.basis ReorderedAFixed.q=false:=(hf.2 ReorderedAFixed.q (by decide)).trans hsum
  have rz:s.basis ReorderedAFixed.r=false:=(hf.2 ReorderedAFixed.r (by decide)).trans hV
  have pz:s.basis ReorderedAFixed.p=false:=(hf.2 ReorderedAFixed.p (by decide)).trans hP
  change ∀u∈ReorderedAFixed.q::ReorderedAFixed.r::ReorderedAFixed.p::ReorderedAFixed.hs,s.basis u=false
  rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons]
  exact ⟨qz,rz,pz,zeroU⟩
 have offHs:∀u∈ReorderedAFixed.hs,u∉wires (ReorderedAPlain.build acc pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (hosts_of_hs u hu)).1
 have goodOriginal:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) (A161Low4Fold.aMiddle L g) s m):=by
  rw [ReorderedARetape.a_middle_eq acc pad bank L.core.cin src (A161Low4Fold.aMiddle L g)
   lengths.1 lengths.2.2.2 fits s m hz hb clean.cin ha]
  exact good_old base hc O hO s _ hf
 have middleEq:=A161Low4FixedFold.cert100.middle_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle L g)
  A161Low4FixedFold.checked.out (ReorderedAPlain.build acc pad bank L.core.cin src) s m zeroU offHs
 have good:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out s m):=by
  rw [middleEq]
  exact goodOriginal
 have knownEq:=AKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
 have goodKnown:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) KnownAMidStaged.body s m):=by
  rw [knownEq]
  exact good
 have buildFrame:=ReorderedAPlain.build_triple acc pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
  s.basis hz hb clean.cin s (m.take (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  ⟨ha,fun _ _=>rfl⟩
 have flag:(run (ReorderedAPlain.build acc pad bank L.core.cin src)
  (m.take (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src))) s).basis 4762=false:=
  (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
 have plainNew:=A109Research.core_plainK s m hz hb clean.cin ha zeroOld goodKnown flag
 have midEq:run KnownAMidStaged.body (m.drop (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s)=
  run A161Low4FixedFold.checked.out (m.drop (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using knownEq
 have ctxt:=ReorderedKnownA.context_eq
  (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out KnownAMidStaged.body
  (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m AKnownMiddleResearch.measurements midEq
 have plain:=plainNew.trans ctxt
 have middleReplace:=A161Low4FixedFold.cert100.surround_eq ReorderedAFixed.hs (A161Low4Fold.aMiddle L g)
  A161Low4FixedFold.checked.out (ReorderedAPlain.build acc pad bank L.core.cin src)
  (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m zeroU offHs
 have eq:run pcCore m s=run (ReorderedAPlain.build acc pad bank L.core.cin src++A161Low4Fold.aMiddle L g++
  ReorderedAPlain.unbuild acc pad bank L.core.cin src) m s:=plain.trans middleReplace
 exact transport _ s _ _ eq (plain_frame base hc O hO s m hf)

/-- The partial-cache loop with the record's sign head. -/
def suffixPC:Program:=A109LowEraseResearch.clear++A109Research.rawFK++A109Research.top++A109Research.M++
 A109Research.newIK++A109LowEraseResearch.clear++A109Research.tail

def loopPC:Program:=SignAHead.head++suffixPC

theorem loopPC_eq(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p)
 (s:State)(m:List Bool)(hf:SquareFrame L.core.out base O s.basis):
 run loopPC m s=run pcCore
  (SignRetape.tape SignAHead.head (ReorderedAHead.head acc pad bank L.core.cin src) m) s:=by
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=by
  intro u hu
  have hu':u∈accZ L:=(FullPadDevelop.pad_sublist L).subset hu
  rcases accZ_mem L u hu' with hu'|hu'
  · exact (regValue_zero _ _).mp clean.pad u hu'
  · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu')
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue acc s.basis=0:=ghostAcc_zero L s.basis clean
 have h:∀a b:List Bool,run SignAHead.head a s=run (ReorderedAHead.head acc pad bank L.core.cin src) b s:=by
  intro a b
  exact ReorderedFrameUnique.program_eq acc s.basis 0 ((2^138-48*regValue src s.basis)%2^138) _ _
   (SignAHead.frame s.basis hz hb clean.cin)
   (ReorderedAHead.head_triple acc pad bank L.core.cin src lengths.1 (by decide) fits s.basis hz hb clean.cin)
   s a b ⟨ha,fun _ _=>rfl⟩
 have eq:=SignRetape.replace SignAHead.head (ReorderedAHead.head acc pad bank L.core.cin src) suffixPC s m h
 simpa only [loopPC,suffixPC,pcCore,A109Research.coreK,A109Research.newFK,A109Research.rawFK,
  A109Research.head,List.append_assoc] using eq

theorem loopPC_frame(base:BasisState)(hc:L.PairClean base)
 (hsum:base A161Low4FixedFold.q=false)(hV:base A161Low4FixedFold.r=false)(hP:base A161Low4FixedFold.p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loopPC
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have e:=loopPC_eq base hc O hO s m hf
 have old:=pcCore_frame base hc hsum hV hP hd O hO s
  (SignRetape.tape SignAHead.head (ReorderedAHead.head acc pad bank L.core.cin src) m) hf
 exact ReorderedAFixed.transport _ s _ _ e old

end ECDSAAdd.Entrant.StairSqLoopA
end

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem keepK_cached_wires:wires A109Research.rawFK⊆A109Research.domain.toFinset∪A109Research.keepK.toFinset:=
 (ReorderedSupport.cached 65 A109Research.xs A109Research.ys A109Research.cs A109Research.keepK ReorderedBPrefixResearch.cin
  (by rw [A109Research.raw_lengths.1];decide) (by rw [A109Research.raw_lengths.2.1];decide)
  (by rw [A109Research.raw_lengths.2.2];decide)
  (by rw [A109Research.raw_lengths.1,A109Research.raw_lengths.2.1])
  (by rw [A109Research.raw_lengths.2.1,A109Research.raw_lengths.2.2])).1

theorem keepK_consumed_wires:
 wires (ReorderedConsumedSub.consumed 65 A109Research.xs A109Research.ys A109Research.cs A109Research.keepK ReorderedBPrefixResearch.cin)⊆
  A109Research.domain.toFinset∪A109Research.keepK.toFinset:=
 ReorderedSupport.consumed 65 A109Research.xs A109Research.ys A109Research.cs A109Research.keepK ReorderedBPrefixResearch.cin
  (by rw [A109Research.raw_lengths.1];decide) (by rw [A109Research.raw_lengths.2.1];decide)
  (by rw [A109Research.raw_lengths.2.2];decide)
  (by rw [A109Research.raw_lengths.1,A109Research.raw_lengths.2.1])
  (by rw [A109Research.raw_lengths.2.1,A109Research.raw_lengths.2.2])

theorem keepK_out(h:Wire)(hA:h∈A109Research.hosts)(hk:h∉A109Research.keepK):
 h∉A109Research.domain.toFinset∪A109Research.keepK.toFinset:=by
 simp only [Finset.mem_union,List.mem_toFinset,not_or]
 exact ⟨A109Research.geometry.2.2 h hA,hk⟩

theorem loopPC_off(h:Wire)(hh:h∈ReorderedAFixed.hosts)(hk:h∉A109Research.keepK):h∉wires loopPC:=by
 have hA:h∈A109Research.hosts:=by
  simp only [A109Research.hosts,List.mem_append]
  exact Or.inl hh
 have op:=off_plain h hh
 have hb:=op.1
 rw [ReorderedABuild.plain_split acc pad bank L.core.cin src lengths.2.2.2] at hb
 simp only [wires_append,Finset.mem_union,not_or] at hb
 have headOff:h∉wires SignAHead.head:=fun bad=>hb.1.1 (SignAHeadSupport.support bad)
 have clearOff:h∉wires A109LowEraseResearch.clear:=by
  rw [clear_wires]
  intro bad
  have sub:([4243,4505,4244,4506,4245,4507]:List Wire)⊆A109Research.ports:=by decide
  exact A109Research.old_away h hh (sub (List.mem_toFinset.mp bad))
 have ht:=op.2
 rw [ReorderedAUnbuild.plain_split acc pad bank L.core.cin src lengths.2.2.2] at ht
 simp only [wires_append,Finset.mem_union,not_or] at ht
 have tailOff:h∉wires A109Research.tail:=by
  rw [tail_eq]
  exact ht.2
 have out:=keepK_out h hA hk
 have rfOff:h∉wires A109Research.rawFK:=fun bad=>out (keepK_cached_wires bad)
 have iOff:h∉wires A109Research.newIK:=by
  simp only [A109Research.newIK,wires_append,Finset.mem_union,not_or]
  exact ⟨A109Research.preInv_off h hA,fun bad=>out (keepK_consumed_wires bad)⟩
 simp only [loopPC,suffixPC,wires_append,Finset.mem_union,not_or,and_assoc]
 exact ⟨headOff,clearOff,rfOff,A109Research.top_off h hA,A109Research.middle_fresh h hA,
  iOff,clearOff,tailOff⟩

end ECDSAAdd.Entrant.StairSqLoopA
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.StairSqLoopA
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

section counts
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem loopPC_counts_rel:toffoliCount loopPC+65=toffoliCount loopNC ∧
 measurementCount loopPC=measurementCount loopNC:=by
 have cb:=ReorderedGenericCache.count_balance 65 A109Research.xs A109Research.ys A109Research.cs
  A109Research.keepK ReorderedBPrefixResearch.cin
  (by rw [A109Research.raw_lengths.1];decide) (by rw [A109Research.raw_lengths.2.1];decide)
  (by rw [A109Research.raw_lengths.2.2];decide)
 rw [loopPC,suffixPC,loopNC,suffixNC,A109Research.newIK,A109Research.I,A109Research.rawFK,
  A109Research.rawI,A109Research.rawF,ReorderedConsumedSub.consumed,ReorderedConsumedSub.plain]
 simp only [toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩

theorem loopPC_counts:toffoliCount loopPC=toffoliCount A109SignResearch.loop+47 ∧
 measurementCount loopPC=measurementCount A109SignResearch.loop:=by
 have r:=loopPC_counts_rel
 have o:=loopNC_counts
 exact ⟨by omega,by omega⟩

theorem loopPC_slots_rel:Challenge.gateSlots loopPC+195=Challenge.gateSlots loopNC:=by
 have sc:=ReorderedSlots.cache 65 A109Research.xs A109Research.ys A109Research.cs
  A109Research.keepK ReorderedBPrefixResearch.cin
  (by rw [A109Research.raw_lengths.1];decide) (by rw [A109Research.raw_lengths.2.1];decide)
  (by rw [A109Research.raw_lengths.2.2];decide) A109Research.keepK_geometry.2.1
 rw [loopPC,suffixPC,loopNC,suffixNC,A109Research.newIK,A109Research.I,A109Research.rawFK,
  A109Research.rawI,A109Research.rawF,ReorderedConsumedSub.consumed,ReorderedConsumedSub.plain]
 simp only [Challenge.gateSlots_append]
 omega

theorem loopPC_slots:Challenge.gateSlots loopPC=Challenge.gateSlots A109SignResearch.loop+135:=by
 have r:=loopPC_slots_rel
 have o:=loopNC_slots
 omega

end counts

section physical
attribute [local irreducible] GatePhysical ECDSAAdd.wires

theorem loopPC_physical:GatePhysical loopPC:=by
 have f:=ReorderedPhysical.cached 65 A109Research.xs A109Research.ys A109Research.cs A109Research.keepK
  ReorderedBPrefixResearch.cin
  (by rw [A109Research.raw_lengths.1];decide) (by rw [A109Research.raw_lengths.2.1];decide)
  (by rw [A109Research.raw_lengths.2.2];decide)
  A109Research.raw_nd (fun q hq bad=>A109Research.geometry.2.2 q (A109Research.keepK_sub q hq) (A109Research.c_in q bad))
 have n:=notRegister_physical A109Research.ys
 have hi:GatePhysical A109Research.newIK:=by
  simp only [A109Research.newIK,ReorderedConsumedSub.consumed,gatePhysical_append]
  exact ⟨A109Research.endpoint_physical.2.2.1,⟨⟨n,f.2⟩,n⟩⟩
 have hf:GatePhysical A109Research.rawFK:=f.1
 simp only [loopPC,suffixPC,gatePhysical_append]
 exact ⟨SignAHeadResources.physical,⟨⟨⟨⟨⟨⟨A109LowEraseResearch.physical,hf⟩,
  A109Research.endpoint_physical.2.1⟩,AAliasesResearch.physical⟩,hi⟩,A109LowEraseResearch.physical⟩,
  A109Research.endpoint_physical.2.2.2⟩⟩

end physical

section support
attribute [local irreducible] ECDSAAdd.wires

theorem loopPC_support:wires loopPC⊆A109Research.S:=by
 have hh:wires SignAHead.head⊆A109Research.S:=by
  apply Finset.Subset.trans ?_ A109Research.old_prefix_support
  rw [A109Research.oldPrefix,wires_append]
  exact Finset.subset_union_left
 have ks:A109Research.domain.toFinset∪A109Research.keepK.toFinset⊆A109Research.S:=by
  intro q hq
  apply A109Research.raw_domain_in
  simp only [Finset.mem_union,List.mem_toFinset] at hq ⊢
  rcases hq with h|h
  · exact Or.inl h
  · exact Or.inr (A109Research.keepK_sub q h)
 have rf:wires A109Research.rawFK⊆A109Research.S:=keepK_cached_wires.trans ks
 have ii:wires A109Research.newIK⊆A109Research.S:=by
  simp only [A109Research.newIK,wires_append]
  exact Finset.union_subset A109Research.endpoint_support.2.1 (keepK_consumed_wires.trans ks)
 simp only [loopPC,suffixPC,wires_append,Finset.union_subset_iff]
 exact ⟨hh,⟨⟨⟨⟨⟨⟨A109Research.clear_support,rf⟩,A109Research.endpoint_support.1⟩,A109Research.middle_support⟩,ii⟩,
  A109Research.clear_support⟩,A109Research.endpoint_support.2.2⟩⟩

end support

end ECDSAAdd.Entrant.StairSqLoopA
end

-- Hole -> host assignment and the renamed loop.
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires


/-- Host of a hole: the hole's index into `ReorderedAFixed.hs` (= `hs100`, work wires and pool 1540). -/
def hostOf(q:Wire):Wire:=ReorderedAFixed.hs.getD (StairSqLoopA.hostDomain.idxOf q) 0

def pairs(hl:List Wire):List (Wire×Wire):=hl.map (fun q=>(q,hostOf q))

/-- The hole-free A loop for any sublist `hl` of the 39 holes. -/
def loopA(hl:List Wire):Program:=StairSquareHolesCore.hostRename (pairs hl) loopPC

theorem holes_geometry:(holes++holes.map hostOf).Nodup ∧ (∀q∈holes,q∈L.foldPad ∧ q∉L.core.out) ∧
 (∀q∈holes,hostOf q∈ReorderedAFixed.hs):=by decide +kernel


theorem holes_geometry44:(StairSqLoopA.hostDomain++StairSqLoopA.hostDomain.map hostOf).Nodup ∧ (∀q∈StairSqLoopA.hostDomain,q∈L.foldPad ∧ q∉L.core.out) ∧
 (∀q∈StairSqLoopA.hostDomain,hostOf q∈ReorderedAFixed.hs):=by decide +kernel

theorem pairs_fst(hl:List Wire):StairSquareHolesCore.holesOf (pairs hl)=hl:=by
 induction hl with
 | nil => rfl
 | cons a t ih =>
   simp only [StairSquareHolesCore.holesOf,pairs,List.map_cons] at ih ⊢
   rw [ih]

theorem pairs_snd(hl:List Wire):StairSquareHolesCore.hostsOf (pairs hl)=hl.map hostOf:=by
 induction hl with
 | nil => rfl
 | cons a t ih =>
   simp only [StairSquareHolesCore.hostsOf,pairs,List.map_cons] at ih ⊢
   rw [ih]

theorem pairs_nodup(hl:List Wire)(hsub:hl.Sublist holes):
 (StairSquareHolesCore.holesOf (pairs hl)++StairSquareHolesCore.hostsOf (pairs hl)).Nodup:=by
 rw [pairs_fst,pairs_snd]
 exact (hsub.append (hsub.map hostOf)).nodup holes_geometry.1


theorem pairs_nodup44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):
 (StairSquareHolesCore.holesOf (pairs hl)++StairSquareHolesCore.hostsOf (pairs hl)).Nodup:=by
 rw [pairs_fst,pairs_snd]
 exact (hsub.append (hsub.map hostOf)).nodup holes_geometry44.1

theorem hostDomain_length44:hostDomain.length=44:=by decide +kernel

theorem holes_mem_hostDomain(q:Wire)(hq:q∈holes):q∈hostDomain:=by
 unfold hostDomain
 exact List.mem_append_left _ hq

/-- PSQ: a hole's host is one of the 44 hole hosts `hs.take 44`, never a kept cache host. -/
theorem hostOf_not_keep44(q:Wire)(hq:q∈hostDomain):hostOf q∉A109Research.keepK:=by
 unfold hostOf
 apply A109Research.keepK_geometry.2.2
 have h:=List.idxOf_lt_length_of_mem hq
 rw [hostDomain_length44] at h
 exact h

theorem hostOf_not_keep(q:Wire)(hq:q∈holes):hostOf q∉A109Research.keepK:=
 hostOf_not_keep44 q (holes_mem_hostDomain q hq)

theorem pairs_hostFree(hl:List Wire)(hsub:hl.Sublist holes):∀ab∈pairs hl,ab.2∉wires loopPC:=by
 intro ab hab
 obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
 exact loopPC_off _ (hosts_of_hs _ (holes_geometry.2.2 y (hsub.subset hy))) (hostOf_not_keep y (hsub.subset hy))


theorem pairs_hostFree44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):∀ab∈pairs hl,ab.2∉wires loopPC:=by
 intro ab hab
 obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
 exact loopPC_off _ (hosts_of_hs _ (holes_geometry44.2.2 y (hsub.subset hy))) (hostOf_not_keep44 y (hsub.subset hy))

theorem loopA_frame(hl:List Wire)(hsub:hl.Sublist holes)(base:BasisState)(hc:L.PairClean base)
 (hsum:base A161Low4FixedFold.q=false)(hV:base A161Low4FixedFold.r=false)(hP:base A161Low4FixedFold.p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (loopA hl)
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have f:=loopPC_frame base hc hsum hV hP hd O hO s m hf
 have holeBase:∀q∈holes,base q=false:=fun q hq=>(regValue_zero _ _).mp hc.pad q (holes_geometry.2.1 q hq).1
 have eq:run (loopA hl) m s=run loopPC m s:=by
  rw [loopA]
  apply StairSquareHolesCore.hostRename_run_eq
  · intro ab hab
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
    have hyH:=hsub.subset hy
    exact (hf.2 y (holes_geometry.2.1 y hyH).2).trans (holeBase y hyH)
  · intro ab hab
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
    have hcl:=A161Low4FixedFold.hostClean base hc hd (hostOf y) (holes_geometry.2.2 y (hsub.subset hy))
    exact (hf.2 _ hcl.1).trans hcl.2
  · intro ab hab
    -- LT50: no defeq `ab.1 =?= y` under `(run loopPC m s).basis` (the kernel would evaluate `run loopPC`)
    obtain ⟨y,hy,e⟩:=List.mem_map.mp hab
    have h1:ab.1=y:=by rw [← e]
    rw [h1]
    have hyH:=hsub.subset hy
    exact (f.2.2 y (holes_geometry.2.1 y hyH).2).trans (holeBase y hyH)
  · exact pairs_hostFree hl hsub
 exact ReorderedAFixed.transport _ s _ _ eq f


theorem loopA_frame44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain)(base:BasisState)(hc:L.PairClean base)
 (hsum:base A161Low4FixedFold.q=false)(hV:base A161Low4FixedFold.r=false)(hP:base A161Low4FixedFold.p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (loopA hl)
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have f:=loopPC_frame base hc hsum hV hP hd O hO s m hf
 have holeBase:∀q∈StairSqLoopA.hostDomain,base q=false:=fun q hq=>(regValue_zero _ _).mp hc.pad q (holes_geometry44.2.1 q hq).1
 have eq:run (loopA hl) m s=run loopPC m s:=by
  rw [loopA]
  apply StairSquareHolesCore.hostRename_run_eq
  · intro ab hab
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
    have hyH:=hsub.subset hy
    exact (hf.2 y (holes_geometry44.2.1 y hyH).2).trans (holeBase y hyH)
  · intro ab hab
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
    have hcl:=A161Low4FixedFold.hostClean base hc hd (hostOf y) (holes_geometry44.2.2 y (hsub.subset hy))
    exact (hf.2 _ hcl.1).trans hcl.2
  · intro ab hab
    -- LT50: no defeq `ab.1 =?= y` under `(run loopPC m s).basis` (the kernel would evaluate `run loopPC`)
    obtain ⟨y,hy,e⟩:=List.mem_map.mp hab
    have h1:ab.1=y:=by rw [← e]
    rw [h1]
    have hyH:=hsub.subset hy
    exact (f.2.2 y (holes_geometry44.2.1 y hyH).2).trans (holeBase y hyH)
  · exact pairs_hostFree44 hl hsub
 exact ReorderedAFixed.transport _ s _ _ eq f

/-- Drop-in with the exact hypothesis list of `A109SignResearch.frame`. -/
theorem loopA_frame_rec(hl:List Wire)(hsub:hl.Sublist holes)(base:BasisState)(hc:L.PairClean base)
 (hsum:base A161Low4FixedFold.q=false)(hV:base A161Low4FixedFold.r=false)(hP:base A161Low4FixedFold.p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (loopA hl)
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=
 loopA_frame hl hsub base hc hsum hV hP hd O hO


theorem loopA_frame_rec44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain)(base:BasisState)(hc:L.PairClean base)
 (hsum:base A161Low4FixedFold.q=false)(hV:base A161Low4FixedFold.r=false)(hP:base A161Low4FixedFold.p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (loopA hl)
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=
 loopA_frame44 hl hsub base hc hsum hV hP hd O hO

theorem loopA_avoids(hl:List Wire)(hsub:hl.Sublist holes):∀q∈hl,q∉wires (loopA hl):=by
 have h:=StairSquareHolesCore.hostRename_avoids (pairs hl) loopPC (pairs_nodup hl hsub) (pairs_hostFree hl hsub)
 rw [pairs_fst] at h
 exact h


theorem loopA_avoids44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):∀q∈hl,q∉wires (loopA hl):=by
 have h:=StairSquareHolesCore.hostRename_avoids (pairs hl) loopPC (pairs_nodup44 hl hsub) (pairs_hostFree44 hl hsub)
 rw [pairs_fst] at h
 exact h

theorem loopA_support(hl:List Wire)(hsub:hl.Sublist holes):wires (loopA hl)⊆A109Research.S:=by
 have hs:=StairSquareHolesCore.hostRename_support (pairs hl) loopPC (pairs_nodup hl hsub) (pairs_hostFree hl hsub)
 rw [pairs_snd] at hs
 intro x hx
 rcases Finset.mem_union.mp (hs hx) with h|h
 · exact loopPC_support (Finset.mem_sdiff.mp h).1
 · obtain ⟨y,hy,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
   have hm:hostOf y∈A109Research.hosts:=by
    simp only [A109Research.hosts,List.mem_append]
    exact Or.inl (hosts_of_hs _ (holes_geometry.2.2 y (hsub.subset hy)))
   apply A109Research.raw_domain_in
   exact Finset.mem_union_right _ (List.mem_toFinset.mpr hm)


theorem loopA_support44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):wires (loopA hl)⊆A109Research.S:=by
 have hs:=StairSquareHolesCore.hostRename_support (pairs hl) loopPC (pairs_nodup44 hl hsub) (pairs_hostFree44 hl hsub)
 rw [pairs_snd] at hs
 intro x hx
 rcases Finset.mem_union.mp (hs hx) with h|h
 · exact loopPC_support (Finset.mem_sdiff.mp h).1
 · obtain ⟨y,hy,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
   have hm:hostOf y∈A109Research.hosts:=by
    simp only [A109Research.hosts,List.mem_append]
    exact Or.inl (hosts_of_hs _ (holes_geometry44.2.2 y (hsub.subset hy)))
   apply A109Research.raw_domain_in
   exact Finset.mem_union_right _ (List.mem_toFinset.mpr hm)

theorem loopA_counts(hl:List Wire):toffoliCount (loopA hl)=toffoliCount A109SignResearch.loop+47 ∧
 measurementCount (loopA hl)=measurementCount A109SignResearch.loop:=by
 have h:=StairSquareHolesCore.hostRename_counts (pairs hl) loopPC
 rw [loopA,h.1,h.2]
 exact loopPC_counts

theorem loopA_slots(hl:List Wire):Challenge.gateSlots (loopA hl)=Challenge.gateSlots A109SignResearch.loop+135:=by
 rw [loopA,StairSquareHolesCore.hostRename_slots]
 exact loopPC_slots

theorem loopA_physical(hl:List Wire):GatePhysical (loopA hl):=
 StairSquareHolesCore.hostRename_physical (pairs hl) loopPC loopPC_physical

end ECDSAAdd.Entrant.StairSqLoopA

end
end Merge_StairSqLoopA_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSqBodyBChecks_at_BOptimizations` -/
section Merge_StairSqBodyBChecks_at_BOptimizations

/-! # LT38 / U3b (assembly): concrete hole checks for the unchanged B-body pieces (eAddLo, ParkCarry, eSubK, rebuild) -/

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqBodyBChecks
open Arithmetic ControlLoan1589BFFold
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

abbrev LB : CuccaroStreamedSquareWideLayout := LowAccCarryDevelop.L

/-- One pass over `P`: does any instruction touch any wire of `hs`? (as LT36's `StairSquareBChecks.touchedAny`) -/
def touchedAny (P : Program) (hs : List Wire) : Bool :=
  P.any (fun i => hs.any (fun q => C163Touch.instructionTouches q i))

theorem touchedAny_spec (P : Program) (hs : List Wire) (h : touchedAny P hs=false) :
    ∀q∈hs,q∉wires P := by
  intro q hq hw
  have t := (C163Touch.touched_spec P q).mpr hw
  simp only [C163Touch.touched,List.any_eq_true] at t
  obtain ⟨i,hi,hti⟩ := t
  have : touchedAny P hs=true := by
    simp only [touchedAny,List.any_eq_true]
    exact ⟨i,hi,q,hq,hti⟩
  rw [h] at this
  exact Bool.false_ne_true this

/-! K4-D (replay budget): the holes and the layout `LB` in closed form (as `StairSquareBChecks.K4DQ`): `holes`
walked `List.range' 4115 5699` per hole; `K4DE.LB_eq` rewrites `LB` into the same layout with `List.range'`
fields (proved symbolically) so the scans below evaluate short intervals instead of pool slices. -/
namespace K4DE





end K4DE

/-! K2 (replay budget): the four scans were `decide +kernel` over `hs.any` per gate (16.2 s eSubK, 16.0 s rebuild,
3.4 s eAddLo, 1.6 s park).  Now: one bit-mask test per gate wire (`K2.touchedAny_of_mask`, a copy of
`StairSquareBChecks.K2Hit`), the record's literal copy of the rebuild (`LocalRebuild.literal`), and the
subtractor's register support for `eSubK`. -/
namespace K2
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false






theorem corr_hit (l : List Nat) (q : Nat) (hq : q∈l) (c : Correction)
    (h : C163Touch.correctionTouches q c=true) : corrHit (maskL l) c=true := by
  cases c with
  | Z a =>
    simp only [C163Touch.correctionTouches,beq_iff_eq] at h
    subst h
    simp only [corrHit,testBit_maskL,decide_eq_true_eq]
    exact hq
  | CZ a b =>
    simp only [C163Touch.correctionTouches,Bool.or_eq_true,beq_iff_eq] at h
    simp only [corrHit,testBit_maskL,Bool.or_eq_true,decide_eq_true_eq]
    rcases h with rfl|rfl
    · exact Or.inl hq
    · exact Or.inr hq

theorem corrs_hit (l : List Nat) (q : Nat) (hq : q∈l) (cs : List Correction)
    (h : cs.any (C163Touch.correctionTouches q)=true) : cs.any (corrHit (maskL l))=true := by
  obtain ⟨c,hc,ht⟩ := List.any_eq_true.mp h
  exact List.any_eq_true.mpr ⟨c,hc,corr_hit l q hq c ht⟩

theorem instr_hit (l : List Nat) (q : Nat) (hq : q∈l) (i : Instr)
    (h : C163Touch.instructionTouches q i=true) : instrHit (maskL l) i=true := by
  have tb : ∀a,q=a→(maskL l).testBit a=true := by
    intro a e
    subst e
    rw [testBit_maskL]
    exact decide_eq_true hq
  cases i with
  | X a =>
    simp only [C163Touch.instructionTouches,beq_iff_eq] at h
    simp only [instrHit]
    exact tb a h
  | CX a b =>
    simp only [C163Touch.instructionTouches,Bool.or_eq_true,beq_iff_eq] at h
    simp only [instrHit,Bool.or_eq_true]
    rcases h with h|h
    · exact Or.inl (tb a h)
    · exact Or.inr (tb b h)
  | CCX a b d =>
    simp only [C163Touch.instructionTouches,Bool.or_eq_true,beq_iff_eq] at h
    simp only [instrHit,Bool.or_eq_true]
    rcases h with (h|h)|h
    · exact Or.inl (Or.inl (tb a h))
    · exact Or.inl (Or.inr (tb b h))
    · exact Or.inr (tb d h)
  | measureX a cs ds =>
    simp only [C163Touch.instructionTouches,Bool.or_eq_true,beq_iff_eq] at h
    simp only [instrHit,Bool.or_eq_true]
    rcases h with (h|h)|h
    · exact Or.inl (Or.inl (tb a h))
    · exact Or.inl (Or.inr (corrs_hit l q hq cs h))
    · exact Or.inr (corrs_hit l q hq ds h)

/-- One mask test per gate wire instead of one list scan per forbidden wire. -/
theorem touchedAny_of_mask (P : Program) (l : List Nat) (h : P.any (instrHit (maskL l))=false) :
    touchedAny P l=false := by
  cases ht : touchedAny P l
  · rfl
  · exfalso
    simp only [touchedAny,List.any_eq_true] at ht
    obtain ⟨i,hi,q,hq,hti⟩ := ht
    have : P.any (instrHit (maskL l))=true := List.any_eq_true.mpr ⟨i,hi,instr_hit l q hq i hti⟩
    rw [h] at this
    exact Bool.false_ne_true this

theorem touchedAny_of_free (P : Program) (hs : List Wire) (h : ∀q∈hs,q∉wires P) : touchedAny P hs=false := by
  cases ht : touchedAny P hs
  · rfl
  · exfalso
    simp only [touchedAny,List.any_eq_true] at ht
    obtain ⟨i,hi,q,hq,hti⟩ := ht
    have t : C163Touch.touched P q=true := by
      simp only [C163Touch.touched,List.any_eq_true]
      exact ⟨i,hi,hti⟩
    exact h q hq ((C163Touch.touched_spec P q).mp t)

section
attribute [local irreducible] ECDSAAdd.wires


end


theorem eSubK_support : wires (eSubK LB)⊆(eKw LB::LB.core.cin::(hiReg LB++[eZ0 LB]++(eRlow LB++[eU LB])++
    (eBank LB).take 128++[eV LB])).toFinset :=
  subTop_support _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)

end K2

theorem eAddLo_free : touchedAny (eAddLo LB) holes=false := by
  rw [K2.holes_nat]
  exact K2.touchedAny_of_mask _ _ (by decide +kernel)
theorem park_free : touchedAny (ParkCarryDevelop.program (eU LB) LB.core.sumCarry) holes=false := by
  rw [K2.holes_nat]
  exact K2.touchedAny_of_mask _ _ (by decide +kernel)
attribute [local irreducible] ECDSAAdd.wires in
theorem eSubK_free : touchedAny (eSubK LB) holes=false := by
  apply K2.touchedAny_of_free
  intro q hq hw
  rw [K2.holes_nat] at hq
  exact K2.disj_of_maskL _ _ (by decide +kernel) q hq (List.mem_toFinset.mp (K2.eSubK_support hw))
theorem rebuild_free : touchedAny LocalRebuild.improved holes=false := by
  rw [LocalRebuild.improved,LocalRebuild.literal,K2.holes_nat]
  exact K2.touchedAny_of_mask _ _ (by decide +kernel)

end ECDSAAdd.Entrant.StairSqBodyBChecks
end
end Merge_StairSqBodyBChecks_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSqLoopB_at_BOptimizations` -/
section Merge_StairSqLoopB_at_BOptimizations

/-! # LT38 / U2b: hole-free B95 loop

Same construction as `StairSqLoopA` for the B loop `B95Research.loop`: the record's non-cached B loop
(`B95Research.plain_loop`) never touches the 89 hosts `ReorderedBSupportResearch.hosts`; the hole sites are renamed
onto the first 39 of `LowAccCarryDevelop.hosts88` for the whole loop.  The frame is the record's B-state frame
(`B95Research.frame`).  Cost: +98 Toffoli (= 95 + 3), same measurements. -/

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.StairSqLoopB
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires









end ECDSAAdd.Entrant.StairSqLoopB

end

-- The non-cached loop never touches the 89 hosts.
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.StairSqLoopB
open ReorderedBPrefixResearch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem clear_wires:wires B95LowEraseResearch.clear=([4243,4505,4244,4506,4245,4507]:List Wire).toFinset:=by
 ext q
 simp [B95LowEraseResearch.clear,wires,Instr.wires,correctionWires]
 tauto


end ECDSAAdd.Entrant.StairSqLoopB

end

-- Counts, slots, physical, support of the non-cached loop.
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.StairSqLoopB
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

section counts
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots



end counts

section physical
attribute [local irreducible] GatePhysical ECDSAAdd.wires




end physical

section support
attribute [local irreducible] ECDSAAdd.wires



end support

end ECDSAAdd.Entrant.StairSqLoopB

end

-- Hole -> host assignment and the renamed loop.
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.StairSqLoopB
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ReorderedBPrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires


/-- Host of a hole: the hole's index into `LowAccCarryDevelop.hosts88` (work wires). -/
def hostOf(q:Wire):Wire:=LowAccCarryDevelop.hosts88.getD (StairSqLoopA.hostDomain.idxOf q) 0

def pairs(hl:List Wire):List (Wire×Wire):=hl.map (fun q=>(q,hostOf q))


theorem holes_geometry:(holes++holes.map hostOf).Nodup ∧ (∀q∈holes,q∈L.foldPad) ∧
 (∀q∈holes,hostOf q∈LowAccCarryDevelop.hosts88):=by decide +kernel



theorem holes_geometry44:(StairSqLoopA.hostDomain++StairSqLoopA.hostDomain.map hostOf).Nodup ∧ (∀q∈StairSqLoopA.hostDomain,q∈L.foldPad) ∧
 (∀q∈StairSqLoopA.hostDomain,hostOf q∈LowAccCarryDevelop.hosts88):=by decide +kernel

theorem pairs_fst(hl:List Wire):StairSquareHolesCore.holesOf (pairs hl)=hl:=by
 induction hl with
 | nil => rfl
 | cons a t ih =>
   simp only [StairSquareHolesCore.holesOf,pairs,List.map_cons] at ih ⊢
   rw [ih]

theorem pairs_snd(hl:List Wire):StairSquareHolesCore.hostsOf (pairs hl)=hl.map hostOf:=by
 induction hl with
 | nil => rfl
 | cons a t ih =>
   simp only [StairSquareHolesCore.hostsOf,pairs,List.map_cons] at ih ⊢
   rw [ih]

theorem pairs_nodup(hl:List Wire)(hsub:hl.Sublist holes):
 (StairSquareHolesCore.holesOf (pairs hl)++StairSquareHolesCore.hostsOf (pairs hl)).Nodup:=by
 rw [pairs_fst,pairs_snd]
 exact (hsub.append (hsub.map hostOf)).nodup holes_geometry.1









theorem pairs_nodup44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):
 (StairSquareHolesCore.holesOf (pairs hl)++StairSquareHolesCore.hostsOf (pairs hl)).Nodup:=by
 rw [pairs_fst,pairs_snd]
 exact (hsub.append (hsub.map hostOf)).nodup holes_geometry44.1

end ECDSAAdd.Entrant.StairSqLoopB

end
end Merge_StairSqLoopB_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSqBodyB_at_BOptimizations` -/
section Merge_StairSqBodyB_at_BOptimizations

/-! # LT38 / U3b (assembly): the hole-free B body, generic in the e-fold

`bodyBG hl EF` is the record's B body `B95PaddedResearch.body`
(`LocalSevenBody.bodyForBoth L B95Research.loop LocalEFoldOptimize.improved LocalRebuild.improved ++ padding 4`)
with
* the two measured folds replaced by LT37's direct folds (`directFoldQTq`, U1),
* the loop replaced by LT38's renamed non-cached loop `StairSqLoopB.loopB hl` (U2b),
* the e-fold replaced by an arbitrary program `EF` satisfying `EFoldOK EF` (LT36's mapped-source e-fold).
The frame goes through LT36's generic `StairSquareBBody.frameG`.  Everything else (eAddLo, ParkCarry, eSubK,
rebuild, padding) is the record's program. -/

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqBodyB
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ManyACarryDevelop FullBTemp ZeroReadDevelop
open ECDSAAdd.Entrant.StairSquareDirectFold
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

abbrev LB : CuccaroStreamedSquareWideLayout := LowAccCarryDevelop.L
abbrev cB : Wire := LowAccCarryDevelop.c

/-- What the assembly needs of the new e-fold (LT36): frame, support, hole avoidance, physicality. -/
def EFoldFrame (EF : Program) : Prop :=
  ∀ (b : BasisState), LB.PairClean b → ∀ (O E : Nat), O<SquareReduction.p →
    Triple (BState LB b O E 0) EF
      (BState LB b ((4294968272*flipE (b cB) E+(SquareReduction.p-1-O))%SquareReduction.p) E 0)

def EFoldOK (EF : Program) : Prop :=
  EFoldFrame EF ∧ wires EF ⊆ (cB::LB.wires).toFinset ∧ (∀ q ∈ holes, q ∉ wires EF) ∧ GatePhysical EF

def dF1 : Program := directFoldQTq LB (negP LB)
def dF2 : Program := directFoldQTq LB (rot128F LB)




end ECDSAAdd.Entrant.StairSqBodyB
end
end Merge_StairSqBodyB_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSqBodyBInst_at_BOptimizations` -/
section Merge_StairSqBodyBInst_at_BOptimizations

/-! # LT38 / U3b (assembly): the concrete hole-free B body

`bodyB hl = bodyBG hl StairSquareBEFoldK.efold`: the record's B body `B95PaddedResearch.body` with LT37's direct folds,
LT38's renamed non-cached loop `StairSqLoopB.loopB hl` and LT36's mapped-source e-fold.  For every sublist `hl` of the
39 holes: LT40's `BodyBOK`, avoidance of `hl`, T = record + 108 (loop +98, e-fold +10), M = record, slots ≤ record − 736,
physical. -/

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqBodyB
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run

/-- LT36's e-fold satisfies the assembly interface. -/
theorem efold_ok : EFoldOK StairSquareBEFoldK.efold :=
  ⟨fun b hb O E hO => StairSquareBEFoldK.efold_spec b hb O E hO,
   StairSquareBEFoldK.efold_support,
   fun q hq => StairSquareBEFoldK.efold_avoids q (List.mem_append_left _ hq),
   StairSquareBEFoldK.efold_physical⟩








section counts
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots



end counts

end ECDSAAdd.Entrant.StairSqBodyB
end
end Merge_StairSqBodyBInst_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSqBodyBNorm_at_BOptimizations` -/
section Merge_StairSqBodyBNorm_at_BOptimizations

/-! # LT38 / U3b (assembly): normFlag (pre-place pool 646 ↦ old hole 718) is avoided by the new B body,
given that the record's B middle `B95AliasesResearch.program` avoids it.  (normFlag is a GHOST bit of the
accumulator register `acc`, so the register-level bound does not suffice; the build/unbuild programs are checked
by a kernel scan.) -/

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqBodyB
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
open InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
open ECDSAAdd.Entrant.StairSquareDirectFold
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run

/-! K2 (replay budget): `build_norm`/`unbuild_norm` were `decide +kernel` scans (21.8 s + 21.4 s of kernel time).
normFlag is accumulator wire 3 of `ReorderedBPrefixResearch.acc`, and every early-H term has shift ≥ 4, so the
exact `Acc.op_wires` shapes of the pieces (as in `Ghost3CacheA.plain_support`) put both programs inside
`cin :: (src ++ acc.drop 4 ++ pad ++ bank)`; only that list's membership is decided. -/
section K2PlainSec
set_option linter.unusedVariables false

namespace K2Plain
attribute [local irreducible] List.toFinset



/-- The A-shape plain build/unbuild (`ReorderedAPlain`) never touches the first four accumulator wires: every term
has shift ≥ 4.  Same proof as `Ghost3CacheA.plain_support` with the exact `Acc.op_wires` shapes. -/
theorem plain_fine (A Z bank src : List Wire) (cin : Wire) (len : A.length=161) (hsrc : src.length=128)
    (fit : ∀f∈earlyHTerms src,Acc.Fits A Z bank cin 161 f) :
    wires (ReorderedAPlain.build A Z bank cin src)⊆(cin::(src++A.drop 4++Z++bank)).toFinset ∧
    wires (ReorderedAPlain.unbuild A Z bank cin src)⊆(cin::(src++A.drop 4++Z++bank)).toFinset := by
  have tm := A161NarrowAcc.terms_mem src
  -- membership in the target from the exact op shapes
  have opS (A' : List Wire) (w : Nat) (f : MeasuredSquareFold) (hA : ∀q∈Acc.ty A' f,q∈A.drop 4)
      (hz : ∀q∈Acc.tx Z w f,q∈src∨q∈Z) (hb : ∀q∈Acc.tc bank w f,q∈bank) :
      (cin::(Acc.tx Z w f++Acc.ty A' f++Acc.tc bank w f)).toFinset⊆(cin::(src++A.drop 4++Z++bank)).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_cons,List.mem_append] at h ⊢
    rcases h with h|(h|h)|h
    · exact Or.inl h
    · rcases hz q h with h'|h'
      · exact Or.inr (Or.inl (Or.inl (Or.inl h')))
      · exact Or.inr (Or.inl (Or.inr h'))
    · exact Or.inr (Or.inl (Or.inl (Or.inr (hA q h))))
    · exact Or.inr (Or.inr (hb q h))
  have txS (w : Nat) (f : MeasuredSquareFold) (hf : f.src=src) : ∀q∈Acc.tx Z w f,q∈src∨q∈Z := by
    intro q hq
    simp only [Acc.tx,List.mem_append,hf] at hq
    rcases hq with h|h
    · exact Or.inl h
    · exact Or.inr (List.mem_of_mem_take h)
  have tcS (w : Nat) (f : MeasuredSquareFold) : ∀q∈Acc.tc bank w f,q∈bank := fun q hq => List.mem_of_mem_take hq
  -- seed (shift 4)
  have f4 := fit _ tm.1
  have L4 := Acc.fits_lengths A Z bank cin 161 (Acc.earlyTerm src false 4) len f4.toFitsLen
  have seed : wires (Acc.seedOp A Z 161 (Acc.earlyTerm src false 4))⊆(cin::(src++A.drop 4++Z++bank)).toFinset := by
    refine (copyRegister_wires_subset none _ _).trans ?_
    intro q hq
    have h := List.mem_toFinset.mp hq
    simp only [Option.toList_none,List.nil_append,List.mem_append] at h
    apply List.mem_toFinset.mpr
    simp only [List.mem_cons,List.mem_append]
    rcases h with h|h
    · rcases txS 161 _ rfl q h with h'|h'
      · exact Or.inr (Or.inl (Or.inl (Or.inl h')))
      · exact Or.inr (Or.inl (Or.inr h'))
    · exact Or.inr (Or.inl (Or.inl (Or.inr (by simpa only [Acc.ty,Acc.earlyTerm] using h))))
  -- shift 6 / 10 at width 138, shift 32 at width 161
  have op6 (neg : Bool) : wires (Acc.op (A.take 138) Z bank cin 138 neg (Acc.earlyTerm src true 6))⊆
      (cin::(src++A.drop 4++Z++bank)).toFinset := by
    have ff := Acc.fits_prefix A Z bank cin 161 138 (Acc.earlyTerm src true 6) (by decide) (fit _ tm.2.2.1)
      (by simp only [Acc.earlyTerm,hsrc]; omega)
    rw [Acc.op_wires (A.take 138) Z bank cin 138 neg _ (by simp [len]) ff]
    exact opS _ _ _ (fun q h => drop4_of_take_drop A 138 6 (by decide) q (by simpa only [Acc.ty,Acc.earlyTerm] using h))
      (txS _ _ rfl) (tcS _ _)
  have op10 (neg : Bool) : wires (Acc.op (A.take 138) Z bank cin 138 neg (Acc.earlyTerm src false 10))⊆
      (cin::(src++A.drop 4++Z++bank)).toFinset := by
    have ff := ReorderedAcc.fits_prefix A Z bank cin 161 138 (Acc.earlyTerm src false 10) (by decide)
      (fit _ tm.2.1) (by simp only [Acc.earlyTerm,hsrc]; omega) (by simp only [Acc.earlyTerm]; omega)
    rw [ReorderedAcc.op_wires (A.take 138) Z bank cin 138 neg _ (by simp [len]) ff]
    exact opS _ _ _ (fun q h => drop4_of_take_drop A 138 10 (by decide) q (by simpa only [Acc.ty,Acc.earlyTerm] using h))
      (txS _ _ rfl) (tcS _ _)
  have f32 := Acc.fits_prefix A Z bank cin 161 161 (Acc.earlyTerm src false 32) (by decide) (fit _ tm.2.2.2)
    (by simp only [Acc.earlyTerm,hsrc]; omega)
  have top (neg : Bool) : wires (Acc.op (A.take 161) Z bank cin 161 neg (Acc.earlyTerm src false 32))⊆
      (cin::(src++A.drop 4++Z++bank)).toFinset := by
    rw [Acc.op_wires (A.take 161) Z bank cin 161 neg _ (by simp [len]) f32]
    exact opS _ _ _ (fun q h => drop4_of_take_drop A 161 32 (by decide) q (by simpa only [Acc.ty,Acc.earlyTerm] using h))
      (txS _ _ rfl) (tcS _ _)
  have preInv : wires (A161Carry.unbuildPre A Z bank cin src)⊆(cin::(src++A.drop 4++Z++bank)).toFinset :=
    (CodexNarrowTailResource.accSub_support 106 (A.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)
     (by simp [len]) f32.toFitsLen (by simp only [Acc.earlyTerm]; omega)).trans (top true)
  have tail := KnownOutputAdder.program_support (mappedRead (src++Z.take 4) false) (ReorderedKnownTail.desired src)
    ((A.take 138).drop 6) (bank.take 131) cin
  rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tail
  have td : ((src++Z.take 4)++src.drop 2++(A.take 138).drop 6++bank.take 131++[cin]).toFinset⊆
      (cin::(src++A.drop 4++Z++bank)).toFinset := by
    intro q hq
    have h := List.mem_toFinset.mp hq
    apply List.mem_toFinset.mpr
    simp only [List.mem_append,List.mem_singleton] at h
    have pp:q∈Z.take 4→q∈Z:=List.mem_of_mem_take
    have ss:q∈src.drop 2→q∈src:=List.mem_of_mem_drop
    have aa:q∈(A.take 138).drop 6→q∈A.drop 4:=drop4_of_take_drop A 138 6 (by decide) q
    have bb:q∈bank.take 131→q∈bank:=List.mem_of_mem_take
    simp only [List.mem_cons,List.mem_append]
    tauto
  have tailSupport : wires (ReorderedATail.tail A Z bank cin src)⊆(cin::(src++A.drop 4++Z++bank)).toFinset :=
    tail.trans td
  constructor
  · simp only [ReorderedAPlain.build,ReorderedAPre.pre,A161Carry.buildPost,wires_append]
    exact Finset.union_subset (Finset.union_subset (Finset.union_subset seed (op6 true)) (op10 false)) (top false)
  · simp only [ReorderedAPlain.unbuild,wires_append]
    exact Finset.union_subset (Finset.union_subset (Finset.union_subset preInv (op10 true)) tailSupport) seed

end K2Plain

theorem plain_touchedAny_of_free (P : Program) (hs : List Wire) (h : ∀q∈hs,q∉wires P) :
    StairSquareBChecks.touchedAny P hs=false := by
  cases ht : StairSquareBChecks.touchedAny P hs
  · rfl
  · exfalso
    simp only [StairSquareBChecks.touchedAny,List.any_eq_true] at ht
    obtain ⟨i,hi,q,hq,hti⟩ := ht
    have t : C163Touch.touched P q=true := by
      simp only [C163Touch.touched,List.any_eq_true]
      exact ⟨i,hi,hti⟩
    exact h q hq ((C163Touch.touched_spec P q).mp t)

theorem plain_norm_off : LB.core.normFlag∉ReorderedBPrefixResearch.cin::(ReorderedBPrefixResearch.src++
    ReorderedBPrefixResearch.acc.drop 4++ReorderedBPrefixResearch.pad++ReorderedBPrefixResearch.bank) := by
  decide +kernel

end K2PlainSec

theorem build_norm : StairSquareBChecks.touchedAny (ReorderedAPlain.build ReorderedBPrefixResearch.acc
    ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src)
    [LB.core.normFlag]=false := by
  apply plain_touchedAny_of_free
  intro q hq hw
  rw [List.mem_singleton] at hq
  subst hq
  exact plain_norm_off (List.mem_toFinset.mp ((K2Plain.plain_fine _ _ _ _ _ ReorderedBPrefixResearch.acc_length
    ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits).1 hw))

theorem unbuild_norm : StairSquareBChecks.touchedAny (ReorderedAPlain.unbuild ReorderedBPrefixResearch.acc
    ReorderedBPrefixResearch.pad ReorderedBPrefixResearch.bank ReorderedBPrefixResearch.cin ReorderedBPrefixResearch.src)
    [LB.core.normFlag]=false := by
  apply plain_touchedAny_of_free
  intro q hq hw
  rw [List.mem_singleton] at hq
  subst hq
  exact plain_norm_off (List.mem_toFinset.mp ((K2Plain.plain_fine _ _ _ _ _ ReorderedBPrefixResearch.acc_length
    ReorderedBPrefixResearch.source_length ReorderedBPrefixResearch.fits).2 hw))




end ECDSAAdd.Entrant.StairSqBodyB
end
end Merge_StairSqBodyBNorm_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSqBodyBNormM_at_BOptimizations` -/
section Merge_StairSqBodyBNormM_at_BOptimizations

/-! # LT38: the record's B middle avoids normFlag (kernel scan), hence the new B body avoids normFlag. -/

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqBodyB
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

/-! K2 (replay budget): `middle_norm` was one `decide +kernel` scan of the record B middle (66.6 s of kernel time,
almost all of it re-running the ZeroSet compiler `compileS?` inside `SixCarryLoopAnchor.output`).  The compiled
output's wires are a subset of its input `BData301.p0` (`SRewrites.support`), a literal program that is cheap to
scan; the eight repairs, the window swap and the three alias swaps are then carried over by the record's own
freshness lemmas (`patch_off`, `fresh_of_old`, `fresh_of_single`). -/

theorem norm_touchedAny_of_free (P : Program) (hs : List Wire) (h : ∀q∈hs,q∉wires P) : StairSquareBChecks.touchedAny P hs=false := by
  cases ht : StairSquareBChecks.touchedAny P hs
  · rfl
  · exfalso
    simp only [StairSquareBChecks.touchedAny,List.any_eq_true] at ht
    obtain ⟨i,hi,q,hq,hti⟩ := ht
    have t : C163Touch.touched P q=true := by
      simp only [C163Touch.touched,List.any_eq_true]
      exact ⟨i,hi,hti⟩
    exact h q hq ((C163Touch.touched_spec P q).mp t)

/-! K4-D (replay budget): `p0_norm` as one pass over the literal blocks of `BData301.p0` (split at its `++`
tree, so no block is reached through the nested appends) with a primitive `Nat.beq` test per wire. -/
namespace K4DN








end K4DN

theorem normFlag_val : LB.core.normFlag=4761 := by decide +kernel

theorem p0_norm : StairSquareBChecks.touchedAny BData301.p0 [4761]=false := by
  apply norm_touchedAny_of_free
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  apply K4DN.not_mem_of_allK
  simp only [BData301.p0, K4DN.allK, List.all_append]
  decide +kernel

theorem repairs_norm : StairSquareBChecks.touchedAny ReorderedBMiddlePatchesResearch.repairs [4761]=false := by
  decide +kernel

attribute [local irreducible] ECDSAAdd.wires ZeroSetDevelop.compileS? SixCarryLoopAnchor.output in
theorem output_norm : (4761:Wire)∉wires SixCarryLoopAnchor.output := by
  have p0f : (4761:Wire)∉wires BData301.p0 :=
    StairSquareBChecks.touchedAny_spec _ _ p0_norm _ (List.mem_singleton_self _)
  rw [LocalEightLoop.output_def]
  cases h : ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0 with
  | none => simp [wires]
  | some v =>
    intro hw
    simp only [Option.map_some,Option.getD_some] at hw
    exact p0f ((v.proof.support _ _ _).1 hw)

attribute [local irreducible] ECDSAAdd.wires SixCarryLoopAnchor.output in
theorem patched_norm : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.output := by
  have hr := StairSquareBChecks.touchedAny_spec _ _ repairs_norm _ (List.mem_singleton_self _)
  simp only [ReorderedBMiddlePatchesResearch.repairs,wires_append,Finset.mem_union,not_or] at hr
  have h0 : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.p0 := output_norm
  have h1 : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.p1 :=
    ReorderedBMiddlePatchesResearch.patch_off _ _ 7950 _ h0 (by tauto)
  have h2 : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.p2 :=
    ReorderedBMiddlePatchesResearch.patch_off _ _ 7944 _ h1 (by tauto)
  have h3 : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.p3 :=
    ReorderedBMiddlePatchesResearch.patch_off _ _ 7938 _ h2 (by tauto)
  have h4 : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.p4 :=
    ReorderedBMiddlePatchesResearch.patch_off _ _ 7932 _ h3 (by tauto)
  have h5 : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.p5 :=
    ReorderedBMiddlePatchesResearch.patch_off _ _ 7926 _ h4 (by tauto)
  have h6 : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.p6 :=
    ReorderedBMiddlePatchesResearch.patch_off _ _ 904 _ h5 (by tauto)
  have h7 : (4761:Wire)∉wires ReorderedBMiddlePatchesResearch.p7 :=
    ReorderedBMiddlePatchesResearch.patch_off _ _ 898 _ h6 (by tauto)
  exact ReorderedBMiddlePatchesResearch.patch_off _ _ 892 _ h7 (by tauto)

attribute [local irreducible] ECDSAAdd.wires in
theorem middle_norm : StairSquareBChecks.touchedAny B95AliasesResearch.program [LB.core.normFlag]=false := by
  rw [normFlag_val]
  apply norm_touchedAny_of_free
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  have s : (4761:Wire)∉wires B95AliasesResearch.single :=
    B95MiddleResearch.fresh_of_old 4761 patched_norm (B95Research.fix _ _ _ (by decide) (by decide)) (by decide)
  exact B95AliasesResearch.fresh_of_single 4761 s (B95Research.fix _ _ _ (by decide) (by decide))
    (B95Research.fix _ _ _ (by decide) (by decide)) (B95Research.fix _ _ _ (by decide) (by decide))
    (by decide) (by decide)


end ECDSAAdd.Entrant.StairSqBodyB
end
end Merge_StairSqBodyBNormM_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSqLoopC_at_BOptimizations` -/
section Merge_StairSqLoopC_at_BOptimizations

/-! # LT38 / U2c: hole-free C loop

Same construction as `StairSqLoopA` for the C loop `C105SignResearch.loop`: the record's non-cached C loop
(`C105Research.plain_loop`) never touches the 99 hosts `ReorderedCFixed.hosts`; the hole sites are renamed onto
the first 39 of `C163Low4Middle.hs` for the whole loop.  Cost: +108 Toffoli (= 105 + 3), same measurements. -/

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
 InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires C163Low4Middle.bankChecked C163Low4Middle.specialChecked
abbrev p:=C163Low4Middle.p

/-- The record's non-cached C core (`F ++ M ++ (I ++ clear ++ tail)`). -/
def ncCore:Program:=C105Research.F++C105Research.M++(C105Research.I++C105LowEraseResearch.clear++C105Research.tail)

theorem hosts_of_hs(u:Wire)(hu:u∈C163Low4Middle.hs):u∈ReorderedCFixed.hosts:=by
 simp only [ReorderedCFixed.hosts,List.mem_cons]
 exact Or.inr (Or.inr (Or.inr hu))

/-- `hs` is zero on every square-frame state (copy of `zeroU` in `C105Research.core_frame`). -/
theorem hs_zero(base:BasisState)(hc:L.PairClean base)(hd:base d=false)(O:Nat)(s:State)
 (hf:SquareFrame L.core.out base O s.basis):∀u∈C163Low4Middle.hs,s.basis u=false:=by
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have dz:s.basis d=false:=(hf.2 d (by decide)).trans hd
 intro u hu
 rcases List.mem_append.mp hu with hu|hu
 · rcases List.mem_append.mp hu with hu|hu
   · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
   · have e:u=d:=by simpa only [List.mem_singleton] using hu
     subst u
     exact dz
 · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_take hu)

/-- Copy of `C105Research.core_frame` with `core_plain` replaced by `plain_loop`. -/
theorem ncCore_frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) ncCore
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have len:=lengths
 have fit:=fits
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue ga s.basis=0:=C163Low4Ghost.ghostAcc_zero L s.basis clean
 have zeroU:∀u∈C163Low4Middle.hs,s.basis u=false:=hs_zero base hc hd O s hf
 have offHs:∀u∈C163Low4Middle.hs,u∉wires (ReorderedCPlain.build ga pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (hosts_of_hs u hu)).1
 have goodOld:=fun record=>good base hc O hO s record hf
 have goodSpecial:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) specialChecked.out s m):=by
  rw [ReorderedRetape.c_middle_eq ga pad bank L.core.cin src specialChecked.out
   len.1 len.2.2.2 fit s m hz hb clean.cin ha]
  exact goodOld _
 have middleEq:=bank_cert.middle_eq C163Low4Middle.hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) s m zeroU offHs
 have goodBank:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) bankChecked.out s m):=by
  rw [middleEq]
  exact goodSpecial
 have knownEq:=CKKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
 have goodKnown:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) KnownCMidStaged.body s m):=by
  rw [knownEq]
  exact goodBank
 have buildFrame:=ReorderedCPlain.build_triple ga pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
  s.basis hz hb clean.cin s (m.take (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  ⟨ha,fun _ _=>rfl⟩
 have flag:(run (ReorderedCPlain.build ga pad bank L.core.cin src)
  (m.take (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src))) s).basis 4762=false:=
  (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
 have plainNew:=C105Research.plain_loop s m hz hb clean.cin ha goodKnown flag
 have midEq:run KnownCMidStaged.body (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s)=
  run C163Low4Middle.bankChecked.out (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using knownEq
 have ctxt:=ReorderedKnownA.context_eq
  (ReorderedCPlain.build ga pad bank L.core.cin src) C163Low4Middle.bankChecked.out KnownCMidStaged.body
  (ReorderedCPlain.unbuild ga pad bank L.core.cin src) s m CKKnownMiddleResearch.measurements midEq
 have plainEq0:=plainNew.trans ctxt
 have middleReplace:=bank_cert.surround_eq C163Low4Middle.hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) (ReorderedCPlain.unbuild ga pad bank L.core.cin src)
  s m zeroU offHs
 have plainEq:=ReorderedRetape.c_loop_eq ga pad bank L.core.cin src specialChecked.out
  len.1 len.2.2.2 fit s m hz hb clean.cin ha goodOld
 let record:=ReorderedRetape.tape (measurementCount (C163NarrowAcc.build8 ga pad bank L.core.cin src))
  (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)) m
 have oldFrame:=C163Low4Middle.frame base hc hp hd O hO s record hf
 rw [eq_plain base hc hp hd O hO s record hf] at oldFrame
 have finalEq:run ncCore m s=run (C163NarrowAcc.build8 ga pad bank L.core.cin src++specialChecked.out++
  C163SourceAdd.unbuild ga pad bank L.core.cin src) record s:=plainEq0.trans (middleReplace.trans plainEq)
 exact ReorderedCFixed.transport (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)) s _ _ finalEq oldFrame

end ECDSAAdd.Entrant.StairSqLoopC

end

-- The non-cached loop with the record's sign head, and its frame.
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def suffixNC:Program:=C105LowEraseResearch.clear++C105Research.rawF++C105Research.top++C105Research.M++
 C105Research.I++C105LowEraseResearch.clear++C105Research.tail

def loopNC:Program:=SignCHead.head++suffixNC

end ECDSAAdd.Entrant.StairSqLoopC

end

-- The non-cached loop never touches the 99 hosts.
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem clear_wires:wires C105LowEraseResearch.clear=([4243,4505,4244,4506,4245,4507]:List Wire).toFinset:=by
 ext q
 simp [C105LowEraseResearch.clear,wires,Instr.wires,correctionWires]
 tauto

end ECDSAAdd.Entrant.StairSqLoopC

end

-- Counts, slots, physical, support of the non-cached loop.
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.StairSqLoopC
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

section counts
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem loopNC_counts:toffoliCount loopNC=toffoliCount C105SignResearch.loop+108 ∧
 measurementCount loopNC=measurementCount C105SignResearch.loop:=by
 have ai:C163Low4Middle.L.core.cin=C105PrefixResearch.L.core.cin:=by decide +kernel
 have nc:=ReorderedGenericCache.count_balance 105 C105Research.xs C105Research.ys C105Research.cs
  C105Research.hosts C105PrefixResearch.cin
  (by rw [C105Research.raw_lengths.1];decide) (by rw [C105Research.raw_lengths.2.1];decide)
  (by rw [C105Research.raw_lengths.2.2];decide)
 have ni:=HighConsumedC105Research.sub_toffoli
 have nm:=HighConsumedC105Research.sub_measurements
 simp only [ReorderedConsumedSub.consumed,toffoliCount_append,measurementCount_append] at ni nm
 -- LT50 (replay budget): definitions unfolded by `rw` and the omega atoms aligned by explicit program
 -- equalities (`simp only [defs] at *` cast the sums: the kernel evaluated both counts, 50 s)
 rw [loopNC,suffixNC,C105SignResearch.loop,C105SignResearch.suffix,C105Research.I,C105Research.newI,
  C105Research.rawI,C105Research.rawF,ReorderedConsumedSub.plain]
 simp only [toffoliCount_append,measurementCount_append]
 have P1:ReorderedGenericCache.cachedAdd 105 C105Research.xs C105Research.ys C105Research.cs
   C105SignResearch.hosts C163Low4Middle.L.core.cin=
  ReorderedGenericCache.cachedAdd 105 C105Research.xs C105Research.ys C105Research.cs
   C105Research.hosts C105PrefixResearch.cin:=by
  simp only [C105SignResearch.hosts,C105PrefixResearch.cin,ai]
 have P2:notRegister HighConsumedC105Research.ys=notRegister C105Research.ys:=by
  simp only [HighConsumedC105Research.ys,C105Research.ys]
 have P3:ReorderedGenericCache.consumedAdd 105 HighConsumedC105Research.xs HighConsumedC105Research.ys
   HighConsumedC105Research.cs HighConsumedC105Research.hs HighConsumedC105Research.cin=
  ReorderedGenericCache.consumedAdd 105 C105Research.xs C105Research.ys C105Research.cs
   C105Research.hosts C105PrefixResearch.cin:=by
  simp only [C105Research.xs,C105Research.ys,C105Research.cs,HighConsumedC105Research.xs,
   HighConsumedC105Research.ys,HighConsumedC105Research.cs,HighConsumedC105Research.cin,
   HighConsumedC105Research.hs,C105PrefixResearch.cin,C105SignResearch.hosts,ai]
 rw [P1]
 rw [P2,P3] at ni nm
 exact ⟨by omega,by omega⟩

theorem loopNC_slots:Challenge.gateSlots loopNC=Challenge.gateSlots C105SignResearch.loop+318:=by
 have ai:C163Low4Middle.L.core.cin=C105PrefixResearch.L.core.cin:=by decide +kernel
 have nc:=ReorderedSlots.cache 105 C105Research.xs C105Research.ys C105Research.cs
  C105Research.hosts C105PrefixResearch.cin
  (by rw [C105Research.raw_lengths.1];decide) (by rw [C105Research.raw_lengths.2.1];decide)
  (by rw [C105Research.raw_lengths.2.2];decide) C105Research.geometry.2.1
 have ni:=HighConsumedC105Research.sub_slots
 simp only [ReorderedConsumedSub.consumed,Challenge.gateSlots_append] at ni
 -- LT50 (replay budget): as in `loopNC_counts` (55 s → ≈ 0)
 rw [loopNC,suffixNC,C105SignResearch.loop,C105SignResearch.suffix,C105Research.I,C105Research.newI,
  C105Research.rawI,C105Research.rawF,ReorderedConsumedSub.plain]
 simp only [Challenge.gateSlots_append]
 have P1:ReorderedGenericCache.cachedAdd 105 C105Research.xs C105Research.ys C105Research.cs
   C105SignResearch.hosts C163Low4Middle.L.core.cin=
  ReorderedGenericCache.cachedAdd 105 C105Research.xs C105Research.ys C105Research.cs
   C105Research.hosts C105PrefixResearch.cin:=by
  simp only [C105SignResearch.hosts,C105PrefixResearch.cin,ai]
 have P2:notRegister HighConsumedC105Research.ys=notRegister C105Research.ys:=by
  simp only [HighConsumedC105Research.ys,C105Research.ys]
 have P3:ReorderedGenericCache.consumedAdd 105 HighConsumedC105Research.xs HighConsumedC105Research.ys
   HighConsumedC105Research.cs HighConsumedC105Research.hs HighConsumedC105Research.cin=
  ReorderedGenericCache.consumedAdd 105 C105Research.xs C105Research.ys C105Research.cs
   C105Research.hosts C105PrefixResearch.cin:=by
  simp only [C105Research.xs,C105Research.ys,C105Research.cs,HighConsumedC105Research.xs,
   HighConsumedC105Research.ys,HighConsumedC105Research.cs,HighConsumedC105Research.cin,
   HighConsumedC105Research.hs,C105PrefixResearch.cin,C105SignResearch.hosts,ai]
 rw [P1]
 rw [P2,P3] at ni
 omega

end counts

section physical
attribute [local irreducible] GatePhysical ECDSAAdd.wires

end physical

section support
attribute [local irreducible] ECDSAAdd.wires

end support

end ECDSAAdd.Entrant.StairSqLoopC

end

-- PSQ-C: partial carry cache in the hole-free C square loop.
-- The 44 hole hosts `C163Low4Middle.hs.take 44` stay out of the cache; the other 61 of the 105 cache hosts,
-- the three status hosts `ReorderedCFixed.hosts.take 3` included (clean at loop entry), keep their carries (61 T saved).
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def keepK:List Wire:=hosts.filter (fun q=>!((C163Low4Middle.hs.take 44).contains q))

theorem keepK_geometry:keepK.Nodup ∧ keepK.length=61 ∧
 (∀i,i<44→C163Low4Middle.hs.getD i 0∉keepK):=by decide +kernel

theorem keepK_sub(q:Wire)(hq:q∈keepK):q∈hosts:=(List.mem_filter.mp hq).1

def rawFK:Program:=ReorderedGenericCache.cachedAdd 61 xs ys cs keepK cin
def newFK:Program:=head++C105LowEraseResearch.clear++ReorderedGenericCache.cachedAdd 61 xs ys cs keepK cin++top
def newIK:Program:=preInv++ReorderedConsumedSub.consumed 61 xs ys cs keepK cin

theorem inverse_frameK(s:State)(m:List Bool)(H:Nat)(hH:H<2^130)
 (hz:∀q∈cs,(run preInv m s).basis q=false)(hi:(run preInv m s).basis cin=false)
 (source:regValue xs (run preInv m s).basis=H)
 (target:regValue ys (run preInv m s).basis=976*H/1024)
 (saved:keepK.map s.basis=ReorderedCacheBits.values 4 61 H (976*H/1024)):
 run newIK m s=scatterState keepK (List.replicate keepK.length false) (run I m s):=by
 have same:keepK.map (run preInv m s).basis=keepK.map s.basis:=by
  apply List.map_congr_left
  intro q hq
  exact run_preserves_outside preInv m s q (preInv_off q (keepK_sub q hq))
 simp only [newIK,I,ControlledBorrowResearch.run_cat]
 exact ReorderedConsumedSub.frame 61 xs ys cs keepK cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  (by rw [raw_lengths.1,raw_lengths.2.1]) (by rw [raw_lengths.2.1,raw_lengths.2.2])
  raw_nd keepK_geometry.1 keepK_geometry.2.1 (fun q hq=>geometry.2.2 q (keepK_sub q hq))
  (run preInv m s) _ hz hi H (976*H/1024) source target (same.trans saved)

theorem forward_frameK(s:State)(m:List Bool)(H:Nat)
 (zero:∀q∈keepK,(run (head++C105LowEraseResearch.clear) (m.take (measurementCount (head++C105LowEraseResearch.clear))) s).basis q=false)
 (values:(((cs.drop 4).take 61).map (run (carryPrefix (4+61) xs ys cs cin) []
  (run (head++C105LowEraseResearch.clear) (m.take (measurementCount (head++C105LowEraseResearch.clear))) s)).basis)=
   ReorderedCacheBits.values 4 61 H (976*H/1024)):
 run newFK m s=scatterState keepK (ReorderedCacheBits.values 4 61 H (976*H/1024)) (run F m s):=by
 have h:=CacheBetweenFrameResearch.forward (head++C105LowEraseResearch.clear) top 61 xs ys cs keepK cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)
  keepK_geometry.1 (fun q hq bad=>geometry.2.2 q (keepK_sub q hq) (by simp only [List.mem_cons,List.mem_append];tauto))
  (fun q hq=>rawF_off q (keepK_sub q hq)) (fun q hq=>top_off q (keepK_sub q hq)) s m zero
 rw [values] at h
 exact h

theorem forward_measurementsK:measurementCount newFK=measurementCount F:=by
 have h:=(ReorderedGenericCache.count_balance 61 xs ys cs keepK cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide) (by rw [raw_lengths.2.2];decide)).2.1
 simp only [newFK,F,rawF,measurementCount_append]
 rw [h]

theorem forward_zeroK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false):
 ∀q∈keepK,(run F m s).basis q=false:=by
 rw [forward_erased s m hz hb hi ha]
 let u:=run (ReorderedCPlain.build acc pad bank cin src) m s
 have ready:WReady acc pad bank cin src (regValue src s.basis) u:=
  Ghost3CacheC.plain_ready s m hz hb hi ha
 intro q hk
 have hq:=keepK_sub q hk
 rcases List.mem_append.mp hq with hq|hq
 · rw [C105LowEraseResearch.bit_same _ q (by
    have away:=old_away q hq
    intro bad
    apply away
    simp only [C105LowEraseResearch.low,List.mem_cons,List.not_mem_nil,or_false] at bad
    rcases bad with rfl|rfl|rfl <;>decide)]
   exact (run_preserves_outside _ m s q (ReorderedCFixed.off_plain q hq).1).trans (zero q hq)
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 0 (by decide)
      (by rw [acc_length];decide) ready.1
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 1 (by decide)
      (by rw [acc_length];decide) ready.1
   · rw [C105LowEraseResearch.bit_same _ _ (by decide)]
     exact LowWordRecovery.low_register_zero acc u.basis _ 2 (by decide)
      (by rw [acc_length];decide) ready.1
   · exact C105LowEraseResearch.zero _ _ (by decide)
   · exact C105LowEraseResearch.zero _ _ (by decide)
   · exact C105LowEraseResearch.zero _ _ (by decide)

theorem prefix_zeroK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false):
 ∀q∈keepK,(run (head++C105LowEraseResearch.clear) m s).basis q=false:=by
 have clean:=forward_zeroK s m hz hb hi ha zero
 intro q hq
 have off:q∉wires (rawF++top):=by
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨rawF_off q (keepK_sub q hq),top_off q (keepK_sub q hq)⟩
 have eq:(run F m s).basis q=(run (head++C105LowEraseResearch.clear) m s).basis q:=by
  have partition:F=(head++C105LowEraseResearch.clear)++(rawF++top):=by simp only [F,List.append_assoc]
  rw [partition,run_cat]
  exact run_preserves_outside _ _ _ q off
 exact eq.symm.trans (clean q hq)

theorem forward_valuesK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0):
 (((cs.drop 4).take 61).map (run (carryPrefix (4+61) xs ys cs cin) []
  (run (head++C105LowEraseResearch.clear) m s)).basis)=
 ReorderedCacheBits.values 4 61 (regValue src s.basis) (976*regValue src s.basis/1024):=by
 let H:=regValue src s.basis
 let u:=run head m s
 let t:=run (head++C105LowEraseResearch.clear) m s
 have te:t=C105LowEraseResearch.erase u:=prefix_erased s m hz hb hi ha
 have hH:H<2^130:=by simpa only [H,source_length] using regValue_lt src s.basis
 have ready:(∀q∈cs,u.basis q=false) ∧ u.basis cin=false ∧ regValue xs u.basis=H ∧
  regValue ys u.basis=((2^140-48*H)%2^140)/1024:=by
  simpa only [cs,xs,ys,u,head,H] using
   CHeadArithmeticResearch.ready acc pad bank cin src acc_length source_length fits s m hz hb hi ha
 have eraseBit(q:Wire)(hq:q∈domain):t.basis q=u.basis q:=by
  rw [te]
  exact C105LowEraseResearch.bit_same _ q (domain_away_low q hq)
 have eraseReg(r:List Wire)(sub:∀q∈r,q∈domain):regValue r t.basis=regValue r u.basis:=
  regValue_congr _ _ _ (fun q hq=>eraseBit q (sub q hq))
 have sy:regValue ys t.basis=((2^140-48*H)%2^140)/1024:=
  (eraseReg ys y_in).trans ready.2.2.2
 have sh:regValue xs t.basis=H:=
  (eraseReg xs x_in).trans ready.2.2.1
 have sb:∀q∈cs,t.basis q=false:=by
  intro q hq
  exact (eraseBit q (c_in q hq)).trans (ready.1 q hq)
 have si:t.basis cin=false:=
  (eraseBit cin cin_in).trans ready.2.1
 exact ReorderedCacheBits.forward_values 4 61 H (((2^140-48*H)%2^140)/1024) (976*H/1024)
  xs ys cs cin t (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide) raw_nd sb si sh sy (fun j hj=>by
   simpa only [show 130+10=140 by decide] using
    ReorderedCacheArithmetic.high_add_low 130 (4+j+1) H (by omega) hH)

theorem scattered_erased_domainK(s:State)(vs:List Bool)(q:Wire)(hq:q∈domain):
 (scatterState keepK vs (C105LowEraseResearch.erase s)).basis q=s.basis q:=by
 rw [scatter_outside keepK vs _ q (by intro bad;exact geometry.2.2 q (keepK_sub q bad) hq)]
 exact C105LowEraseResearch.bit_same s q (domain_away_low q hq)

theorem inverse_readyK(H:Nat)(s:State)(m:List Bool)(ready:WReady acc pad bank cin src H s):
 let vs:=ReorderedCacheBits.values 4 61 H (976*H/1024)
 let t:=scatterState keepK vs (C105LowEraseResearch.erase s)
 run newIK m t=scatterState keepK (List.replicate keepK.length false) (run I m t):=by
 dsimp only
 let vs:=ReorderedCacheBits.values 4 61 H (976*H/1024)
 let t:=scatterState keepK vs (C105LowEraseResearch.erase s)
 have hH:H<2^130:=by rw [←ready.2.1];simpa only [source_length] using regValue_lt src s.basis
 have commute:run preInv m t=scatterState keepK vs (C105LowEraseResearch.erase (run preInv m s)):=by
  rw [show t=scatterState keepK vs (C105LowEraseResearch.erase s) from rfl,
   run_scatter preInv keepK vs _ _ (fun q hq=>preInv_off q (keepK_sub q hq)),
   C105LowEraseResearch.commute preInv m s (fun q hq=>preInv_off q (low_hosts q hq))]
 have bits(q:Wire)(hq:q∈domain):(run preInv m t).basis q=(run preInv m s).basis q:=by
  rw [commute]
  exact scattered_erased_domainK _ vs q hq
 have regs(r:List Wire)(sub:∀q∈r,q∈domain):regValue r (run preInv m t).basis=regValue r (run preInv m s).basis:=
  regValue_congr _ _ _ (fun q hq=>bits q (sub q hq))
 have rr:=pre_raw_ready H s m ready
 have saved:keepK.map t.basis=vs:=scatter_saved_map keepK vs _ keepK_geometry.1
  (by simp only [vs,ReorderedCacheBits.values,List.length_map,keepK_geometry.2.1,List.length_range])
 apply inverse_frameK t m H hH
 · intro q hq
   rw [bits q (c_in q hq)]
   exact rr.1 q hq
 · rw [bits cin cin_in]
   exact rr.2.1
 · rw [regs xs x_in]
   exact rr.2.2.1
 · rw [regs ys y_in]
   exact rr.2.2.2
 · exact saved

theorem cache_loopK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run (newFK++M++newIK) m s=run (F++M++I) m s:=by
 let H:=regValue src s.basis
 let vs:=ReorderedCacheBits.values 4 61 H (976*H/1024)
 have mid:=middle_erased s m hz hb hi ha after flag
 have forward:=forward_frameK s (m.take (measurementCount F)) H
  (prefix_zeroK s _ hz hb hi ha zero) (forward_valuesK s _ hz hb hi ha)
 apply CacheFromCleanForwardResearch.equivalent F newFK M I newIK keepK vs
  forward_measurementsK (fun q hq=>middle_fresh q (keepK_sub q hq)) (fun q hq=>I_off q (keepK_sub q hq))
  keepK_geometry.1 s m (forward_zeroK s _ hz hb hi ha zero) forward
 rw [mid]
 exact inverse_readyK H (middleState oldF oldM s m) _ after

def coreK:Program:=(newFK++M++newIK)++(C105LowEraseResearch.clear++tail)

theorem inverse_measurementsK:measurementCount newIK=measurementCount I:=by
 have h:=ReorderedConsumedSub.measurement_eq 61 xs ys cs keepK cin
  (by rw [raw_lengths.1];decide) (by rw [raw_lengths.2.1];decide)
  (by rw [raw_lengths.2.2];decide)
 have eq:measurementCount (ReorderedConsumedSub.consumed 61 xs ys cs keepK cin)=measurementCount rawI:=h
 simp only [newIK,I,measurementCount_append,eq]

theorem prefix_measurementsK:measurementCount (newFK++M++newIK)=measurementCount (F++M++I):=by
 simp only [measurementCount_append,forward_measurementsK,inverse_measurementsK]

theorem core_plainK(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis cin=false)
 (ha:regValue acc s.basis=0)(zero:∀q∈ReorderedCFixed.hosts,s.basis q=false)
 (after:WReady acc pad bank cin src (regValue src s.basis) (middleState oldF oldM s m))
 (flag:(run oldF (m.take (measurementCount oldF)) s).basis 4762=false):
 run coreK m s=run (oldF++oldM++ReorderedCPlain.unbuild acc pad bank cin src) m s:=by
 have eq:=ClearContextResearch.append_at (newFK++M++newIK) (F++M++I) (C105LowEraseResearch.clear++tail)
  s m prefix_measurementsK (cache_loopK s m hz hb hi ha zero after flag)
 have shape:(F++M++I)++(C105LowEraseResearch.clear++tail)=F++M++(I++C105LowEraseResearch.clear++tail):=by
  have g(A B C D E:Program):(A++B++C)++(D++E)=A++B++(C++D++E):=by simp only [List.append_assoc]
  exact g F M I C105LowEraseResearch.clear tail
 exact eq.trans ((congrArg (fun P=>run P m s) shape).trans (plain_loop s m hz hb hi ha after flag))

end ECDSAAdd.Entrant.C105Research
end

-- PSQ-C: the partial-cache C loop (`loopPC`) and its frame, host avoidance, counts, slots, physicality, support.
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
 InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires C163Low4Middle.bankChecked C163Low4Middle.specialChecked

def pcCore:Program:=C105Research.coreK

/-- `pcCore_frame` with the partial-cache core. -/
theorem pcCore_frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) pcCore
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have len:=lengths
 have fit:=fits
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue ga s.basis=0:=C163Low4Ghost.ghostAcc_zero L s.basis clean
 have zeroU:∀u∈C163Low4Middle.hs,s.basis u=false:=hs_zero base hc hd O s hf
 -- the three status hosts are clean at loop entry (as in `C105Research.core_frame`)
 have zeroOld:∀u∈ReorderedCFixed.hosts,s.basis u=false:=by
  have qz:s.basis C163Low4Middle.q=false:=(regValue_zero _ _).mp clean.work C163Low4Middle.q (by decide)
  have rz:s.basis C163Low4Middle.r=false:=(regValue_zero _ _).mp clean.work C163Low4Middle.r (by decide)
  have pz:s.basis C163Low4Middle.p=false:=(hf.2 C163Low4Middle.p (by decide)).trans hp
  intro u hu
  simp only [ReorderedCFixed.hosts,List.mem_cons] at hu
  rcases hu with rfl|rfl|rfl|hu
  · exact qz
  · exact rz
  · exact pz
  · exact zeroU u hu
 have offHs:∀u∈C163Low4Middle.hs,u∉wires (ReorderedCPlain.build ga pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (hosts_of_hs u hu)).1
 have goodOld:=fun record=>good base hc O hO s record hf
 have goodSpecial:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) specialChecked.out s m):=by
  rw [ReorderedRetape.c_middle_eq ga pad bank L.core.cin src specialChecked.out
   len.1 len.2.2.2 fit s m hz hb clean.cin ha]
  exact goodOld _
 have middleEq:=bank_cert.middle_eq C163Low4Middle.hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) s m zeroU offHs
 have goodBank:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) bankChecked.out s m):=by
  rw [middleEq]
  exact goodSpecial
 have knownEq:=CKKnownMiddleResearch.middle_eq s m hz hb clean.cin ha
 have goodKnown:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) KnownCMidStaged.body s m):=by
  rw [knownEq]
  exact goodBank
 have buildFrame:=ReorderedCPlain.build_triple ga pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
  s.basis hz hb clean.cin s (m.take (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  ⟨ha,fun _ _=>rfl⟩
 have flag:(run (ReorderedCPlain.build ga pad bank L.core.cin src)
  (m.take (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src))) s).basis 4762=false:=
  (buildFrame.2.2 4762 (by decide +kernel)).trans clean.modFlag
 have plainNew:=C105Research.core_plainK s m hz hb clean.cin ha zeroOld goodKnown flag
 have midEq:run KnownCMidStaged.body (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s)=
  run C163Low4Middle.bankChecked.out (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using knownEq
 have ctxt:=ReorderedKnownA.context_eq
  (ReorderedCPlain.build ga pad bank L.core.cin src) C163Low4Middle.bankChecked.out KnownCMidStaged.body
  (ReorderedCPlain.unbuild ga pad bank L.core.cin src) s m CKKnownMiddleResearch.measurements midEq
 have plainEq0:=plainNew.trans ctxt
 have middleReplace:=bank_cert.surround_eq C163Low4Middle.hs specialChecked.out bankChecked.out
  (ReorderedCPlain.build ga pad bank L.core.cin src) (ReorderedCPlain.unbuild ga pad bank L.core.cin src)
  s m zeroU offHs
 have plainEq:=ReorderedRetape.c_loop_eq ga pad bank L.core.cin src specialChecked.out
  len.1 len.2.2.2 fit s m hz hb clean.cin ha goodOld
 let record:=ReorderedRetape.tape (measurementCount (C163NarrowAcc.build8 ga pad bank L.core.cin src))
  (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)) m
 have oldFrame:=C163Low4Middle.frame base hc hp hd O hO s record hf
 rw [eq_plain base hc hp hd O hO s record hf] at oldFrame
 have finalEq:run pcCore m s=run (C163NarrowAcc.build8 ga pad bank L.core.cin src++specialChecked.out++
  C163SourceAdd.unbuild ga pad bank L.core.cin src) record s:=plainEq0.trans (middleReplace.trans plainEq)
 exact ReorderedCFixed.transport (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)) s _ _ finalEq oldFrame

end ECDSAAdd.Entrant.StairSqLoopC
end

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def suffixPC:Program:=C105LowEraseResearch.clear++C105Research.rawFK++C105Research.top++C105Research.M++
 C105Research.newIK++C105LowEraseResearch.clear++C105Research.tail

def loopPC:Program:=SignCHead.head++suffixPC

theorem loopPC_eq(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p)
 (s:State)(m:List Bool)(hf:SquareFrame L.core.out base O s.basis):
 run loopPC m s=run pcCore
  (SignRetape.tape SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) m) s:=by
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have hz:∀u∈pad,s.basis u=false:=fun u hu=>
  (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_drop (List.mem_of_mem_take hu))
 have hb:∀u∈bank,s.basis u=false:=fun u hu=>(regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
 have ha:regValue ga s.basis=0:=ghostAcc_zero L s.basis clean
 have h:∀a b:List Bool,run SignCHead.head a s=run (ReorderedCHead.head ga pad bank L.core.cin src) b s:=by
  intro a b
  exact ReorderedFrameUnique.program_eq ga s.basis 0 ((2^140-48*regValue src s.basis)%2^140) _ _
   (SignCHead.frame s.basis hz hb clean.cin)
   (ReorderedCHead.head_triple ga pad bank L.core.cin src lengths.1 (by decide) fits s.basis hz hb clean.cin)
   s a b ⟨ha,fun _ _=>rfl⟩
 have eq:=SignRetape.replace SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) suffixPC s m h
 simpa only [loopPC,suffixPC,pcCore,C105Research.coreK,C105Research.newFK,C105Research.rawFK,C105Research.head,List.append_assoc] using eq

theorem loopPC_frame(base:BasisState)(hc:L.PairClean base)(hp:base C163Low4Middle.p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loopPC
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have e:=loopPC_eq base hc O hO s m hf
 have old:=pcCore_frame base hc hp hd O hO s
  (SignRetape.tape SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) m) hf
 exact ReorderedCFixed.transport _ s _ _ e old

end ECDSAAdd.Entrant.StairSqLoopC
end

section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires

theorem keepK_cached_wires:wires C105Research.rawFK⊆C105Research.domain.toFinset∪C105Research.keepK.toFinset:=
 (ReorderedSupport.cached 61 C105Research.xs C105Research.ys C105Research.cs C105Research.keepK C105PrefixResearch.cin
  (by rw [C105Research.raw_lengths.1];decide) (by rw [C105Research.raw_lengths.2.1];decide)
  (by rw [C105Research.raw_lengths.2.2];decide)
  (by rw [C105Research.raw_lengths.1,C105Research.raw_lengths.2.1])
  (by rw [C105Research.raw_lengths.2.1,C105Research.raw_lengths.2.2])).1

theorem keepK_consumed_wires:
 wires (ReorderedConsumedSub.consumed 61 C105Research.xs C105Research.ys C105Research.cs C105Research.keepK C105PrefixResearch.cin)⊆
  C105Research.domain.toFinset∪C105Research.keepK.toFinset:=
 ReorderedSupport.consumed 61 C105Research.xs C105Research.ys C105Research.cs C105Research.keepK C105PrefixResearch.cin
  (by rw [C105Research.raw_lengths.1];decide) (by rw [C105Research.raw_lengths.2.1];decide)
  (by rw [C105Research.raw_lengths.2.2];decide)
  (by rw [C105Research.raw_lengths.1,C105Research.raw_lengths.2.1])
  (by rw [C105Research.raw_lengths.2.1,C105Research.raw_lengths.2.2])

theorem keepK_out(h:Wire)(hA:h∈C105Research.hosts)(hk:h∉C105Research.keepK):
 h∉C105Research.domain.toFinset∪C105Research.keepK.toFinset:=by
 simp only [Finset.mem_union,List.mem_toFinset,not_or]
 exact ⟨C105Research.geometry.2.2 h hA,hk⟩

theorem loopPC_off(h:Wire)(hh:h∈ReorderedCFixed.hosts)(hk:h∉C105Research.keepK):h∉wires loopPC:=by
 have hA:h∈C105Research.hosts:=by
  simp only [C105Research.hosts,List.mem_append]
  exact Or.inl hh
 have op:=off_plain h hh
 have hb:=op.1
 rw [ReorderedCBuild.plain_split ga pad bank L.core.cin src lengths.2.2.2] at hb
 simp only [wires_append,Finset.mem_union,not_or] at hb
 have headOff:h∉wires SignCHead.head:=fun bad=>hb.1.1 (SignCHeadSupport.support bad)
 have clearOff:h∉wires C105LowEraseResearch.clear:=by
  rw [clear_wires]
  intro bad
  have sub:([4243,4505,4244,4506,4245,4507]:List Wire)⊆C105Research.ports:=by decide
  exact C105Research.old_away h hh (sub (List.mem_toFinset.mp bad))
 have ht:=op.2
 rw [ReorderedCUnbuild.plain_split ga pad bank L.core.cin src lengths.2.2.2] at ht
 simp only [wires_append,Finset.mem_union,not_or] at ht
 have tailOff:h∉wires C105Research.tail:=fun bad=>ht.2 bad
 have out:=keepK_out h hA hk
 have rfOff:h∉wires C105Research.rawFK:=fun bad=>out (keepK_cached_wires bad)
 have iOff:h∉wires C105Research.newIK:=by
  simp only [C105Research.newIK,wires_append,Finset.mem_union,not_or]
  exact ⟨C105Research.preInv_off h hA,fun bad=>out (keepK_consumed_wires bad)⟩
 simp only [loopPC,suffixPC,wires_append,Finset.mem_union,not_or,and_assoc]
 exact ⟨headOff,clearOff,rfOff,C105Research.top_off h hA,C105Research.middle_fresh h hA,
  iOff,clearOff,tailOff⟩

end ECDSAAdd.Entrant.StairSqLoopC
end

section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.StairSqLoopC
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

section counts
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem loopPC_counts_rel:toffoliCount loopPC+61=toffoliCount loopNC ∧
 measurementCount loopPC=measurementCount loopNC:=by
 have cb:=ReorderedGenericCache.count_balance 61 C105Research.xs C105Research.ys C105Research.cs
  C105Research.keepK C105PrefixResearch.cin
  (by rw [C105Research.raw_lengths.1];decide) (by rw [C105Research.raw_lengths.2.1];decide)
  (by rw [C105Research.raw_lengths.2.2];decide)
 rw [loopPC,suffixPC,loopNC,suffixNC,C105Research.newIK,C105Research.I,C105Research.rawFK,
  C105Research.rawI,C105Research.rawF,ReorderedConsumedSub.consumed,ReorderedConsumedSub.plain]
 simp only [toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩

theorem loopPC_counts:toffoliCount loopPC=toffoliCount C105SignResearch.loop+47 ∧
 measurementCount loopPC=measurementCount C105SignResearch.loop:=by
 have r:=loopPC_counts_rel
 have o:=loopNC_counts
 exact ⟨by omega,by omega⟩

theorem loopPC_slots_rel:Challenge.gateSlots loopPC+183=Challenge.gateSlots loopNC:=by
 have sc:=ReorderedSlots.cache 61 C105Research.xs C105Research.ys C105Research.cs
  C105Research.keepK C105PrefixResearch.cin
  (by rw [C105Research.raw_lengths.1];decide) (by rw [C105Research.raw_lengths.2.1];decide)
  (by rw [C105Research.raw_lengths.2.2];decide) C105Research.keepK_geometry.2.1
 rw [loopPC,suffixPC,loopNC,suffixNC,C105Research.newIK,C105Research.I,C105Research.rawFK,
  C105Research.rawI,C105Research.rawF,ReorderedConsumedSub.consumed,ReorderedConsumedSub.plain]
 simp only [Challenge.gateSlots_append]
 omega

theorem loopPC_slots:Challenge.gateSlots loopPC=Challenge.gateSlots C105SignResearch.loop+135:=by
 have r:=loopPC_slots_rel
 have o:=loopNC_slots
 omega

end counts

section physical
attribute [local irreducible] GatePhysical ECDSAAdd.wires

theorem loopPC_physical:GatePhysical loopPC:=by
 have f:=ReorderedPhysical.cached 61 C105Research.xs C105Research.ys C105Research.cs C105Research.keepK
  C105PrefixResearch.cin
  (by rw [C105Research.raw_lengths.1];decide) (by rw [C105Research.raw_lengths.2.1];decide)
  (by rw [C105Research.raw_lengths.2.2];decide)
  C105Research.raw_nd (fun q hq bad=>C105Research.geometry.2.2 q (C105Research.keepK_sub q hq) (C105Research.c_in q bad))
 have n:=notRegister_physical C105Research.ys
 have hi:GatePhysical C105Research.newIK:=by
  simp only [C105Research.newIK,ReorderedConsumedSub.consumed,gatePhysical_append]
  exact ⟨C105Research.endpoint_physical.2.1,⟨⟨n,f.2⟩,n⟩⟩
 have hf:GatePhysical C105Research.rawFK:=f.1
 simp only [loopPC,suffixPC,gatePhysical_append]
 exact ⟨SignCHeadResources.physical,⟨⟨⟨⟨⟨⟨C105LowEraseResearch.physical,hf⟩,
  C105Research.endpoint_physical.1⟩,CKAliasesResearch.physical⟩,hi⟩,C105LowEraseResearch.physical⟩,
  C105Research.endpoint_physical.2.2⟩⟩

end physical

section support
attribute [local irreducible] ECDSAAdd.wires

theorem loopPC_support:wires loopPC⊆C105Research.S:=by
 have hh:wires SignCHead.head⊆C105Research.S:=by
  apply Finset.Subset.trans ?_ C105Research.old_prefix_support
  rw [C105Research.oldPrefix,wires_append]
  exact Finset.subset_union_left
 have ks:C105Research.domain.toFinset∪C105Research.keepK.toFinset⊆C105Research.S:=by
  intro q hq
  apply C105Research.raw_domain_in
  simp only [Finset.mem_union,List.mem_toFinset] at hq ⊢
  rcases hq with h|h
  · exact Or.inl h
  · exact Or.inr (C105Research.keepK_sub q h)
 have rf:wires C105Research.rawFK⊆C105Research.S:=keepK_cached_wires.trans ks
 have ii:wires C105Research.newIK⊆C105Research.S:=by
  simp only [C105Research.newIK,wires_append]
  exact Finset.union_subset C105Research.endpoint_support.2.1 (keepK_consumed_wires.trans ks)
 simp only [loopPC,suffixPC,wires_append,Finset.union_subset_iff]
 exact ⟨hh,⟨⟨⟨⟨⟨⟨C105Research.clear_support,rf⟩,C105Research.endpoint_support.1⟩,C105Research.middle_support⟩,ii⟩,
  C105Research.clear_support⟩,C105Research.endpoint_support.2.2⟩⟩

end support

end ECDSAAdd.Entrant.StairSqLoopC
end

-- Hole -> host assignment and the renamed loop.
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSqLoopC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires


/-- Host of a hole: the hole's index into `C163Low4Middle.hs` (work wires). -/
def hostOf(q:Wire):Wire:=C163Low4Middle.hs.getD (StairSqLoopA.hostDomain.idxOf q) 0

def pairs(hl:List Wire):List (Wire×Wire):=hl.map (fun q=>(q,hostOf q))

/-- The hole-free C loop for any sublist `hl` of the 39 holes. -/
def loopC(hl:List Wire):Program:=StairSquareHolesCore.hostRename (pairs hl) loopPC

theorem holes_geometry:(holes++holes.map hostOf).Nodup ∧ (∀q∈holes,q∈L.foldPad ∧ q∉L.core.out) ∧
 (∀q∈holes,hostOf q∈C163Low4Middle.hs):=by decide +kernel


theorem holes_geometry44:(StairSqLoopA.hostDomain++StairSqLoopA.hostDomain.map hostOf).Nodup ∧ (∀q∈StairSqLoopA.hostDomain,q∈L.foldPad ∧ q∉L.core.out) ∧
 (∀q∈StairSqLoopA.hostDomain,hostOf q∈C163Low4Middle.hs):=by decide +kernel

theorem pairs_fst(hl:List Wire):StairSquareHolesCore.holesOf (pairs hl)=hl:=by
 induction hl with
 | nil => rfl
 | cons a t ih =>
   simp only [StairSquareHolesCore.holesOf,pairs,List.map_cons] at ih ⊢
   rw [ih]

theorem pairs_snd(hl:List Wire):StairSquareHolesCore.hostsOf (pairs hl)=hl.map hostOf:=by
 induction hl with
 | nil => rfl
 | cons a t ih =>
   simp only [StairSquareHolesCore.hostsOf,pairs,List.map_cons] at ih ⊢
   rw [ih]

theorem pairs_nodup(hl:List Wire)(hsub:hl.Sublist holes):
 (StairSquareHolesCore.holesOf (pairs hl)++StairSquareHolesCore.hostsOf (pairs hl)).Nodup:=by
 rw [pairs_fst,pairs_snd]
 exact (hsub.append (hsub.map hostOf)).nodup holes_geometry.1


theorem pairs_nodup44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):
 (StairSquareHolesCore.holesOf (pairs hl)++StairSquareHolesCore.hostsOf (pairs hl)).Nodup:=by
 rw [pairs_fst,pairs_snd]
 exact (hsub.append (hsub.map hostOf)).nodup holes_geometry44.1

/-- PSQ: a hole's host is one of the 44 hole hosts `hs.take 44`, never a kept cache host. -/
theorem hostOf_not_keep44(q:Wire)(hq:q∈StairSqLoopA.hostDomain):hostOf q∉C105Research.keepK:=by
 unfold hostOf
 apply C105Research.keepK_geometry.2.2
 have h:=List.idxOf_lt_length_of_mem hq
 rw [StairSqLoopA.hostDomain_length44] at h
 exact h

theorem hostOf_not_keep(q:Wire)(hq:q∈holes):hostOf q∉C105Research.keepK:=
 hostOf_not_keep44 q (StairSqLoopA.holes_mem_hostDomain q hq)

theorem pairs_hostFree(hl:List Wire)(hsub:hl.Sublist holes):∀ab∈pairs hl,ab.2∉wires loopPC:=by
 intro ab hab
 obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
 exact loopPC_off _ (hosts_of_hs _ (holes_geometry.2.2 y (hsub.subset hy))) (hostOf_not_keep y (hsub.subset hy))


theorem pairs_hostFree44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):∀ab∈pairs hl,ab.2∉wires loopPC:=by
 intro ab hab
 obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
 exact loopPC_off _ (hosts_of_hs _ (holes_geometry44.2.2 y (hsub.subset hy))) (hostOf_not_keep44 y (hsub.subset hy))

/-- Same triple as `C105SignResearch.frame`. -/
theorem loopC_frame(hl:List Wire)(hsub:hl.Sublist holes)(base:BasisState)(hc:L.PairClean base)
 (hp:base C163Low4Middle.p=false)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (loopC hl)
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have f:=loopPC_frame base hc hp hd O hO s m hf
 have holeBase:∀q∈holes,base q=false:=fun q hq=>(regValue_zero _ _).mp hc.pad q (holes_geometry.2.1 q hq).1
 have eq:run (loopC hl) m s=run loopPC m s:=by
  rw [loopC]
  apply StairSquareHolesCore.hostRename_run_eq
  · intro ab hab
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
    have hyH:=hsub.subset hy
    exact (hf.2 y (holes_geometry.2.1 y hyH).2).trans (holeBase y hyH)
  · intro ab hab
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
    exact hs_zero base hc hd O s hf (hostOf y) (holes_geometry.2.2 y (hsub.subset hy))
  · intro ab hab
    -- LT50: no defeq `ab.1 =?= y` under `(run loopPC m s).basis` (the kernel would evaluate `run loopPC`)
    obtain ⟨y,hy,e⟩:=List.mem_map.mp hab
    have h1:ab.1=y:=by rw [← e]
    rw [h1]
    have hyH:=hsub.subset hy
    exact (f.2.2 y (holes_geometry.2.1 y hyH).2).trans (holeBase y hyH)
  · exact pairs_hostFree hl hsub
 exact ReorderedCFixed.transport _ s _ _ eq f


theorem loopC_frame44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain)(base:BasisState)(hc:L.PairClean base)
 (hp:base C163Low4Middle.p=false)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (loopC hl)
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have f:=loopPC_frame base hc hp hd O hO s m hf
 have holeBase:∀q∈StairSqLoopA.hostDomain,base q=false:=fun q hq=>(regValue_zero _ _).mp hc.pad q (holes_geometry44.2.1 q hq).1
 have eq:run (loopC hl) m s=run loopPC m s:=by
  rw [loopC]
  apply StairSquareHolesCore.hostRename_run_eq
  · intro ab hab
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
    have hyH:=hsub.subset hy
    exact (hf.2 y (holes_geometry44.2.1 y hyH).2).trans (holeBase y hyH)
  · intro ab hab
    obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hab
    exact hs_zero base hc hd O s hf (hostOf y) (holes_geometry44.2.2 y (hsub.subset hy))
  · intro ab hab
    -- LT50: no defeq `ab.1 =?= y` under `(run loopPC m s).basis` (the kernel would evaluate `run loopPC`)
    obtain ⟨y,hy,e⟩:=List.mem_map.mp hab
    have h1:ab.1=y:=by rw [← e]
    rw [h1]
    have hyH:=hsub.subset hy
    exact (f.2.2 y (holes_geometry44.2.1 y hyH).2).trans (holeBase y hyH)
  · exact pairs_hostFree44 hl hsub
 exact ReorderedCFixed.transport _ s _ _ eq f

theorem loopC_avoids(hl:List Wire)(hsub:hl.Sublist holes):∀q∈hl,q∉wires (loopC hl):=by
 have h:=StairSquareHolesCore.hostRename_avoids (pairs hl) loopPC (pairs_nodup hl hsub) (pairs_hostFree hl hsub)
 rw [pairs_fst] at h
 exact h


theorem loopC_avoids44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):∀q∈hl,q∉wires (loopC hl):=by
 have h:=StairSquareHolesCore.hostRename_avoids (pairs hl) loopPC (pairs_nodup44 hl hsub) (pairs_hostFree44 hl hsub)
 rw [pairs_fst] at h
 exact h

theorem loopC_support(hl:List Wire)(hsub:hl.Sublist holes):wires (loopC hl)⊆C105Research.S:=by
 have hs:=StairSquareHolesCore.hostRename_support (pairs hl) loopPC (pairs_nodup hl hsub) (pairs_hostFree hl hsub)
 rw [pairs_snd] at hs
 intro x hx
 rcases Finset.mem_union.mp (hs hx) with h|h
 · exact loopPC_support (Finset.mem_sdiff.mp h).1
 · obtain ⟨y,hy,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
   have hm:hostOf y∈C105Research.hosts:=by
    simp only [C105Research.hosts,List.mem_append]
    exact Or.inl (hosts_of_hs _ (holes_geometry.2.2 y (hsub.subset hy)))
   apply C105Research.raw_domain_in
   exact Finset.mem_union_right _ (List.mem_toFinset.mpr hm)


theorem loopC_support44(hl:List Wire)(hsub:hl.Sublist StairSqLoopA.hostDomain):wires (loopC hl)⊆C105Research.S:=by
 have hs:=StairSquareHolesCore.hostRename_support (pairs hl) loopPC (pairs_nodup44 hl hsub) (pairs_hostFree44 hl hsub)
 rw [pairs_snd] at hs
 intro x hx
 rcases Finset.mem_union.mp (hs hx) with h|h
 · exact loopPC_support (Finset.mem_sdiff.mp h).1
 · obtain ⟨y,hy,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp h)
   have hm:hostOf y∈C105Research.hosts:=by
    simp only [C105Research.hosts,List.mem_append]
    exact Or.inl (hosts_of_hs _ (holes_geometry44.2.2 y (hsub.subset hy)))
   apply C105Research.raw_domain_in
   exact Finset.mem_union_right _ (List.mem_toFinset.mpr hm)

theorem loopC_counts(hl:List Wire):toffoliCount (loopC hl)=toffoliCount C105SignResearch.loop+47 ∧
 measurementCount (loopC hl)=measurementCount C105SignResearch.loop:=by
 have h:=StairSquareHolesCore.hostRename_counts (pairs hl) loopPC
 rw [loopC,h.1,h.2]
 exact loopPC_counts

theorem loopC_slots(hl:List Wire):Challenge.gateSlots (loopC hl)=Challenge.gateSlots C105SignResearch.loop+135:=by
 rw [loopC,StairSquareHolesCore.hostRename_slots]
 exact loopPC_slots

theorem loopC_physical(hl:List Wire):GatePhysical (loopC hl):=
 StairSquareHolesCore.hostRename_physical (pairs hl) loopPC loopPC_physical

end ECDSAAdd.Entrant.StairSqLoopC

end
end Merge_StairSqLoopC_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareBodyAInst_at_BOptimizations` -/
section Merge_StairSquareBodyAInst_at_BOptimizations

/-! # LT37 U3a (final): the hole-free A body

`StairSquareBodyA.bodyA hl = A109SignResearch.directBody (StairSqLoopA.loopA hl)`: the record's A body with both folds
direct (U1) and LT38's renamed non-cached loop (U2a).  For any sublist `hl` of the 39 holes it has the record's exact
`body_frame` statement, the two `fastCore_correct` support hypotheses, avoids `hl`, costs `+112` T, `=` M, `−694` slots,
and is physical. -/

-- generic slot balance and record-support transfer (`A109Research.S = wires HighSignAResearch.body`)
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.A109SignResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed
open ECDSAAdd.Entrant.StairSquareDirectFold
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

/-- EXACT slots: the two direct folds save 2 × 512 slots. -/
theorem direct_body_slots (P : Program) :
 Challenge.gateSlots (directBody P)+Challenge.gateSlots A109SignResearch.loop+1024=
  Challenge.gateSlots A109SignResearch.body+Challenge.gateSlots P := by
 have a:=directFoldQ_slots L hw (negP L) (negP_length L hw) rfl
 have b:=directFoldQ_slots L hw (rot128F L) (rot128F_length L hw) rfl
 simp only [directBody,directRawBody,A109SignResearch.body,A109SignResearch.rawBody,A109SignResearch.fold,
  Challenge.gateSlots_append]
 omega

theorem direct_body_S (P : Program) (hl : wires P⊆A109Research.S) : wires (directBody P)⊆A109Research.S := by
 intro x hx
 rcases Finset.mem_union.mp (direct_body_wires P hx) with h|h
 · exact A109Research.body_support h
 · exact hl h

/-- `aSupport` of `fastCore_correct` / `SumSavedB95Entry.squareEntry_eq` / LT40 `BodyAOK.support`. -/
theorem direct_body_support_S (P : Program) (hl : wires P⊆A109Research.S) :
 wires (directBody P)⊆insert (Baselines.layout.core.poolWire 1540)
   (Baselines.layout.core.generic::Baselines.layout.dialogStreamedSquareWide.wires).toFinset := by
 have old : A109Research.S⊆insert (Baselines.layout.core.poolWire 1540)
   (Baselines.layout.core.generic::Baselines.layout.dialogStreamedSquareWide.wires).toFinset := by
  simpa only [List.toFinset_cons] using KnownProgramActual.a_body_support
 exact (direct_body_S P hl).trans old

/-- `eUfree` of `fastCore_correct` / LT40 `BodyAOK.eUfree`. -/
theorem direct_body_eU_free_S (P : Program) (hl : wires P⊆A109Research.S) :
 ControlLoan1589BFFold.eU ReorderedAFixed.L∉wires (directBody P) :=
 fun h=>KnownProgramActual.a_body_eU_free (direct_body_S P hl h)

theorem direct_body_coarse_S (P : Program) (hl : wires P⊆A109Research.S) :
 wires (directBody P)⊆insert ReorderedAFixed.d (ReorderedAFixed.g::ReorderedAFixed.L.wires).toFinset :=
 (direct_body_S P hl).trans KnownProgramActual.a_coarse

theorem direct_body_fine_S (P : Program) (hl : wires P⊆A109Research.S) :
 wires (directBody P)⊆insert ReorderedAFixed.d
  (wires (InverseCarryDevelop.hostedADual ReorderedAFixed.L
   (LowZero18Square.foldPerm ReorderedAFixed.L (OwnDiagAll12Square.kext Baselines.layout)) ReorderedAFixed.g)) :=
 (direct_body_S P hl).trans KnownProgramActual.a_fine

end ECDSAAdd.Entrant.A109SignResearch
end

-- the final A body
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSquareBodyA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

/-- The hole-free A body for the hole sublist `hl` (`hl.Sublist StairSqLoopA.holes`, `StairSqLoopA.holes = holes39`). -/
def bodyA (hl : List Wire) : Program := A109SignResearch.directBody (StairSqLoopA.loopA hl)

theorem loopA_directLoopFrame (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes) :
 A109SignResearch.DirectLoopFrame (StairSqLoopA.loopA hl) :=
 fun base hc a b c e O hO => StairSqLoopA.loopA_frame_rec hl hsub base hc a b c e O hO


theorem loopA_directLoopFrame44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) :
 A109SignResearch.DirectLoopFrame (StairSqLoopA.loopA hl) :=
 fun base hc a b c e O hO => StairSqLoopA.loopA_frame_rec44 hl hsub base hc a b c e O hO

/-- Exactly the statement of `A109SignResearch.body_frame` (`bodyFrame` of `fastCore_correct`, LT40 `BodyAOK.frame`). -/
theorem bodyA_frame (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes) (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue ReorderedAFixed.L.core.product base=M^2) (hc:ReorderedAFixed.L.PairClean base)
 (hzero:base ReorderedAFixed.q=false) (O:Nat) (hO:O<SquareReduction.p) (hg:base ReorderedAFixed.g=false → M=0)
 (hd:base ReorderedAFixed.d=false) :
 Triple (SquareFrame ReorderedAFixed.L.core.out base O) (bodyA hl)
  (SquareFrame ReorderedAFixed.L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base ReorderedAFixed.g))) :=
 A109SignResearch.direct_body_frame _ (loopA_directLoopFrame hl hsub) base M hM hP hc hzero O hO hg hd



theorem bodyA_frame44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue ReorderedAFixed.L.core.product base=M^2) (hc:ReorderedAFixed.L.PairClean base)
 (hzero:base ReorderedAFixed.q=false) (O:Nat) (hO:O<SquareReduction.p) (hg:base ReorderedAFixed.g=false → M=0)
 (hd:base ReorderedAFixed.d=false) :
 Triple (SquareFrame ReorderedAFixed.L.core.out base O) (bodyA hl)
  (SquareFrame ReorderedAFixed.L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base ReorderedAFixed.g))) :=
 A109SignResearch.direct_body_frame _ (loopA_directLoopFrame44 hl hsub) base M hM hP hc hzero O hO hg hd

theorem bodyA_support (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes) :
 wires (bodyA hl)⊆insert (Baselines.layout.core.poolWire 1540)
   (Baselines.layout.core.generic::Baselines.layout.dialogStreamedSquareWide.wires).toFinset :=
 A109SignResearch.direct_body_support_S _ (StairSqLoopA.loopA_support hl hsub)


theorem bodyA_support44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) :
 wires (bodyA hl)⊆insert (Baselines.layout.core.poolWire 1540)
   (Baselines.layout.core.generic::Baselines.layout.dialogStreamedSquareWide.wires).toFinset :=
 A109SignResearch.direct_body_support_S _ (StairSqLoopA.loopA_support44 hl hsub)

theorem bodyA_eU_free (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes) :
 ControlLoan1589BFFold.eU ReorderedAFixed.L∉wires (bodyA hl) :=
 A109SignResearch.direct_body_eU_free_S _ (StairSqLoopA.loopA_support hl hsub)


theorem bodyA_eU_free44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) :
 ControlLoan1589BFFold.eU ReorderedAFixed.L∉wires (bodyA hl) :=
 A109SignResearch.direct_body_eU_free_S _ (StairSqLoopA.loopA_support44 hl hsub)

theorem bodyA_coarse (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes) :
 wires (bodyA hl)⊆insert ReorderedAFixed.d (ReorderedAFixed.g::ReorderedAFixed.L.wires).toFinset :=
 A109SignResearch.direct_body_coarse_S _ (StairSqLoopA.loopA_support hl hsub)


theorem bodyA_coarse44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) :
 wires (bodyA hl)⊆insert ReorderedAFixed.d (ReorderedAFixed.g::ReorderedAFixed.L.wires).toFinset :=
 A109SignResearch.direct_body_coarse_S _ (StairSqLoopA.loopA_support44 hl hsub)

theorem bodyA_fine (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes) :
 wires (bodyA hl)⊆insert ReorderedAFixed.d
  (wires (InverseCarryDevelop.hostedADual ReorderedAFixed.L
   (LowZero18Square.foldPerm ReorderedAFixed.L (OwnDiagAll12Square.kext Baselines.layout)) ReorderedAFixed.g)) :=
 A109SignResearch.direct_body_fine_S _ (StairSqLoopA.loopA_support hl hsub)


theorem bodyA_fine44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) :
 wires (bodyA hl)⊆insert ReorderedAFixed.d
  (wires (InverseCarryDevelop.hostedADual ReorderedAFixed.L
   (LowZero18Square.foldPerm ReorderedAFixed.L (OwnDiagAll12Square.kext Baselines.layout)) ReorderedAFixed.g)) :=
 A109SignResearch.direct_body_fine_S _ (StairSqLoopA.loopA_support44 hl hsub)

theorem bodyA_avoids (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes) : ∀q∈hl,q∉wires (bodyA hl) :=
 A109SignResearch.direct_body_holes _ hl (fun q hq => (StairSqLoopA.holes_geometry.2.1 q (hsub.subset hq)).1)
  (StairSqLoopA.loopA_avoids hl hsub)


theorem bodyA_avoids44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) : ∀q∈hl,q∉wires (bodyA hl) :=
 A109SignResearch.direct_body_holes _ hl (fun q hq => (StairSqLoopA.holes_geometry44.2.1 q (hsub.subset hq)).1)
  (StairSqLoopA.loopA_avoids44 hl hsub)

theorem bodyA_counts (hl : List Wire) :
 toffoliCount (bodyA hl)=toffoliCount A109SignResearch.body+47 ∧
 measurementCount (bodyA hl)=measurementCount A109SignResearch.body := by
 have h:=A109SignResearch.direct_body_counts (StairSqLoopA.loopA hl)
 have l:=StairSqLoopA.loopA_counts hl
 unfold bodyA
 omega

theorem bodyA_slots (hl : List Wire) :
 Challenge.gateSlots (bodyA hl)+889=Challenge.gateSlots A109SignResearch.body := by
 have h:=A109SignResearch.direct_body_slots (StairSqLoopA.loopA hl)
 have l:=StairSqLoopA.loopA_slots hl
 unfold bodyA
 omega

theorem bodyA_physical (hl : List Wire) : GatePhysical (bodyA hl) :=
 A109SignResearch.direct_body_physical _ (StairSqLoopA.loopA_physical hl)

end ECDSAAdd.Entrant.StairSquareBodyA
end
end Merge_StairSquareBodyAInst_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareBodyCInst_at_BOptimizations` -/
section Merge_StairSquareBodyCInst_at_BOptimizations

/-! # LT37 U3c (final): the hole-free C body

`StairSquareBodyC.bodyC hl = C105SignResearch.directBody (StairSqLoopC.loopC hl)`: the record's C body with its fold
direct (U1) and LT38's renamed non-cached loop (U2c).  For any sublist `hl` of the 39 holes it has the record's exact
`body_frame` statement, the `cSupport` hypothesis of `fastCore_correct`, avoids `hl`, costs `+108` T, `=` M, `−194`
slots, and is physical. -/

-- generic slot balance and record-support transfer (`C105Research.S = wires HighSignCResearch.body`)
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.C105SignResearch
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
open ECDSAAdd.Entrant.StairSquareDirectFold
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

/-- EXACT slots: the direct fold saves 512 slots. -/
theorem direct_body_slots (P : Program) :
 Challenge.gateSlots (directBody P)+Challenge.gateSlots C105SignResearch.loop+512=
  Challenge.gateSlots C105SignResearch.body+Challenge.gateSlots P := by
 have a:=directFoldQ_slots L hw (negRot L) (negRot_length L hw) rfl
 have e:=C163Low4Body.mix_negRot L
 simp only [directBody,directRawBody,C163Low4Body.directBodyProgram,C105SignResearch.body,C105SignResearch.rawBody,
  C163Low4Body.bodyProgram,e,Challenge.gateSlots_append]
 omega

theorem direct_body_S (P : Program) (hl : wires P⊆C105Research.S) : wires (directBody P)⊆C105Research.S := by
 intro x hx
 rcases Finset.mem_union.mp (direct_body_wires P hx) with h|h
 · exact C105Research.body_support h
 · exact hl h

/-- `cSupport` of `fastCore_correct` / `SumSavedB95Entry.squareEntry_eq` / LT40 `BodyCOK.support`. -/
theorem direct_body_coarse_S (P : Program) (hl : wires P⊆C105Research.S) :
 wires (directBody P)⊆insert C163Low4Middle.d (C163Low4Middle.g::C163Low4Middle.L.wires).toFinset :=
 (direct_body_S P hl).trans KnownProgramActual.c_body_coarse

theorem direct_body_fine_S (P : Program) (hl : wires P⊆C105Research.S) :
 wires (directBody P)⊆insert C163Low4Middle.d
  (wires (OwnDiagAll12Square.bodyCKTq C163Low4Middle.L C163Low4Middle.g)) :=
 (direct_body_S P hl).trans KnownProgramActual.c_body_fine

end ECDSAAdd.Entrant.C105SignResearch
end

-- the final C body
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.StairSquareBodyC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

/-- The hole-free C body for the hole sublist `hl` (`hl.Sublist StairSqLoopC.holes`, `= StairSqLoopA.holes = holes39`). -/
def bodyC (hl : List Wire) : Program := C105SignResearch.directBody (StairSqLoopC.loopC hl)

theorem loopC_directLoopFrame (hl : List Wire) (hsub : hl.Sublist StairSqLoopC.holes) :
 C105SignResearch.DirectLoopFrame (StairSqLoopC.loopC hl) :=
 fun base hc a b O hO => StairSqLoopC.loopC_frame hl hsub base hc a b O hO


theorem loopC_directLoopFrame44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) :
 C105SignResearch.DirectLoopFrame (StairSqLoopC.loopC hl) :=
 fun base hc a b O hO => StairSqLoopC.loopC_frame44 hl hsub base hc a b O hO

/-- Exactly the statement of `C105SignResearch.body_frame` (`cFrame` of `fastCore_correct`, LT40 `BodyCOK.frame`). -/
theorem bodyC_frame (hl : List Wire) (hsub : hl.Sublist StairSqLoopC.holes) (base:BasisState) (M:Nat)
 (pv:regValue C163Low4Middle.L.core.product base=M^2) (clean:C163Low4Middle.L.PairClean base)
 (disabled:base C163Low4Middle.g=false→M=0) (hd:base C163Low4Middle.d=false) (O:Nat) (hO:O<SquareReduction.p) :
 Triple (SquareFrame C163Low4Middle.L.core.out base O) (bodyC hl)
  (SquareFrame C163Low4Middle.L.core.out base
   (C163Low4Body.resCFK C163Low4Facts.Klow (base C163Low4Middle.g) (M^2) O)) :=
 C105SignResearch.direct_body_frame _ (loopC_directLoopFrame hl hsub) base M pv clean disabled hd O hO



theorem bodyC_frame44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) (base:BasisState) (M:Nat)
 (pv:regValue C163Low4Middle.L.core.product base=M^2) (clean:C163Low4Middle.L.PairClean base)
 (disabled:base C163Low4Middle.g=false→M=0) (hd:base C163Low4Middle.d=false) (O:Nat) (hO:O<SquareReduction.p) :
 Triple (SquareFrame C163Low4Middle.L.core.out base O) (bodyC hl)
  (SquareFrame C163Low4Middle.L.core.out base
   (C163Low4Body.resCFK C163Low4Facts.Klow (base C163Low4Middle.g) (M^2) O)) :=
 C105SignResearch.direct_body_frame _ (loopC_directLoopFrame44 hl hsub) base M pv clean disabled hd O hO

theorem bodyC_coarse (hl : List Wire) (hsub : hl.Sublist StairSqLoopC.holes) :
 wires (bodyC hl)⊆insert C163Low4Middle.d (C163Low4Middle.g::C163Low4Middle.L.wires).toFinset :=
 C105SignResearch.direct_body_coarse_S _ (StairSqLoopC.loopC_support hl hsub)


theorem bodyC_coarse44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) :
 wires (bodyC hl)⊆insert C163Low4Middle.d (C163Low4Middle.g::C163Low4Middle.L.wires).toFinset :=
 C105SignResearch.direct_body_coarse_S _ (StairSqLoopC.loopC_support44 hl hsub)

theorem bodyC_fine (hl : List Wire) (hsub : hl.Sublist StairSqLoopC.holes) :
 wires (bodyC hl)⊆insert C163Low4Middle.d
  (wires (OwnDiagAll12Square.bodyCKTq C163Low4Middle.L C163Low4Middle.g)) :=
 C105SignResearch.direct_body_fine_S _ (StairSqLoopC.loopC_support hl hsub)


theorem bodyC_fine44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) :
 wires (bodyC hl)⊆insert C163Low4Middle.d
  (wires (OwnDiagAll12Square.bodyCKTq C163Low4Middle.L C163Low4Middle.g)) :=
 C105SignResearch.direct_body_fine_S _ (StairSqLoopC.loopC_support44 hl hsub)

theorem bodyC_avoids (hl : List Wire) (hsub : hl.Sublist StairSqLoopC.holes) : ∀q∈hl,q∉wires (bodyC hl) :=
 C105SignResearch.direct_body_holes _ hl (fun q hq => (StairSqLoopC.holes_geometry.2.1 q (hsub.subset hq)).1)
  (StairSqLoopC.loopC_avoids hl hsub)


theorem bodyC_avoids44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) : ∀q∈hl,q∉wires (bodyC hl) :=
 C105SignResearch.direct_body_holes _ hl (fun q hq => (StairSqLoopC.holes_geometry44.2.1 q (hsub.subset hq)).1)
  (StairSqLoopC.loopC_avoids44 hl hsub)

theorem bodyC_counts (hl : List Wire) :
 toffoliCount (bodyC hl)=toffoliCount C105SignResearch.body+47 ∧
 measurementCount (bodyC hl)=measurementCount C105SignResearch.body := by
 have h:=C105SignResearch.direct_body_counts (StairSqLoopC.loopC hl)
 have l:=StairSqLoopC.loopC_counts hl
 unfold bodyC
 omega

theorem bodyC_slots (hl : List Wire) :
 Challenge.gateSlots (bodyC hl)+377=Challenge.gateSlots C105SignResearch.body := by
 have h:=C105SignResearch.direct_body_slots (StairSqLoopC.loopC hl)
 have l:=StairSqLoopC.loopC_slots hl
 unfold bodyC
 omega

theorem bodyC_physical (hl : List Wire) : GatePhysical (bodyC hl) :=
 C105SignResearch.direct_body_physical _ (StairSqLoopC.loopC_physical hl)

end ECDSAAdd.Entrant.StairSquareBodyC
end
end Merge_StairSquareBodyCInst_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareBodyOK_at_BOptimizations` -/
section Merge_StairSquareBodyOK_at_BOptimizations

/-! # LT37: the new A and C bodies in LT40's contract shapes (`BodyAOK`, `BodyCOK`) -/

section
set_option autoImplicit false

namespace ECDSAAdd.Entrant.StairSquareBodyOK
open ECDSAAdd ECDSAAdd.Entrant StairSquareContract

/-- The hole-free A body satisfies LT40's `BodyAOK` (= the A-body hypotheses of `fastCore_correct`). -/
theorem bodyA_ok (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes) : BodyAOK (StairSquareBodyA.bodyA hl) :=
  ⟨StairSquareBodyA.bodyA_support hl hsub, StairSquareBodyA.bodyA_eU_free hl hsub, StairSquareBodyA.bodyA_frame hl hsub⟩


theorem bodyA_ok44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) : BodyAOK (StairSquareBodyA.bodyA hl) :=
  ⟨StairSquareBodyA.bodyA_support44 hl hsub, StairSquareBodyA.bodyA_eU_free44 hl hsub, StairSquareBodyA.bodyA_frame44 hl hsub⟩

/-- The hole-free C body satisfies LT40's `BodyCOK` (= the C-body hypotheses of `fastCore_correct`). -/
theorem bodyC_ok (hl : List Wire) (hsub : hl.Sublist StairSqLoopC.holes) : BodyCOK (StairSquareBodyC.bodyC hl) :=
  ⟨StairSquareBodyC.bodyC_coarse hl hsub, StairSquareBodyC.bodyC_frame hl hsub⟩




theorem bodyC_ok44 (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.hostDomain) : BodyCOK (StairSquareBodyC.bodyC hl) :=
  ⟨StairSquareBodyC.bodyC_coarse44 hl hsub, StairSquareBodyC.bodyC_frame44 hl hsub⟩

end ECDSAAdd.Entrant.StairSquareBodyOK
end
end Merge_StairSquareBodyOK_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareEntryR_at_BOptimizations` -/
section Merge_StairSquareEntryR_at_BOptimizations

/-! # LT40 U5: the square tail `entryR` frees hole pool 725 (0 T)

`E1ReflectedPlacement.entryR L k` (the reflected constant addition + first tick at the end of
`A161Generic.squareEntry`) uses the hole pool 725 (its compare carry, label `base 511` after the
scratch relocation `rho`) and never uses pool 512.  `entryRH k := hostRename [(pool 725, pool 512)]
(entryR Baselines.layout k)` is run-equal to `entryR` whenever both wires are zero at entry and the
hole is zero at exit (`entryRH_run_eq`; the exit fact is `entryR_hole_out`, from the record's own
`entryR_eq`).  The field-12 piece fact is in `StairSquareEntryRSites`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

namespace ECDSAAdd.Entrant.E1Reflected
open ECDSAAdd ECDSAAdd.Arithmetic NativeFirstDirect RecordedQuantum
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires







theorem merged_support512 (w : Nat → Wire) (g : Wire) (k : Nat) :
    wires (merged w g k)⊆(mS5 w g).toFinset := by
  have B := blk_m5 w g
  have I := in_m5 w g
  have G := g_m5 w g
  have mskH (c : Wire) (hc : c∈mS5 w g) (v : Nat) : wires (maskedConstant c (hR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset c (hR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 0 258 (by omega) q hq))
  have mskT (c : Wire) (hc : c∈mS5 w g) (v : Nat) : wires (maskedConstant c (tR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset c (tR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hc
      · exact B 1029 256 (by omega) q hq))
  have mskS (v : Nat) : wires (maskedConstant g (srcR w) v)⊆(mS5 w g).toFinset :=
    (maskedConstant_wires_subset g (srcR w) v).trans (lsub5 w g _ (fun q hq => by
      rcases List.mem_cons.mp hq with rfl|hq
      · exact G
      · exact B 0 256 (by omega) q hq))
  have notS : wires (notRegister (srcR w))⊆(mS5 w g).toFinset := by
    rw [notRegister_wires]; exact lsub5 w g _ (B 0 256 (by omega))
  have cmp : wires (compareLt none (xR w) (srcR w) (cR w) (w 513) (w 514))⊆(mS5 w g).toFinset := by
    rw [(compareLt_wires none (xR w) (srcR w) (cR w) (w 513) (w 514) (by simp [srcR,xR,wireBlock_length])
      (by simp [cR,srcR,xR,wireBlock_length])).1]
    apply lsub5; intro q hq
    simp only [Option.toList_none,List.nil_append,List.mem_cons,List.mem_append] at hq
    rcases hq with rfl|rfl|(hq|hq)|hq
    · exact I 514 (by omega)
    · exact I 513 (by omega)
    · exact B 770 256 (by omega) q hq
    · exact B 0 256 (by omega) q hq
    · exact B 256 256 (by omega) q hq
  have hC : wires (comparePart w g k)⊆(mS5 w g).toFinset := by
    simp only [comparePart,wires_append,Finset.union_subset_iff]
    exact ⟨⟨mskS _,cmp⟩,mskS _⟩
  have cx (a b : Nat) (ha : (a < 512 ∨ a = 513 ∨ a = 514) ∨ (770 ≤ a ∧ a < 1285) ∨ (1540 ≤ a ∧ a < 1798) ∨ a = 721 ∨ a = 722)
      (hb : (b < 512 ∨ b = 513 ∨ b = 514) ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX (w a) (w b)]⊆(mS5 w g).toFinset := gate_sub5 w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact I a ha
    · exact I b hb)
  have cxg (b : Nat) (hb : (b < 512 ∨ b = 513 ∨ b = 514) ∨ (770 ≤ b ∧ b < 1285) ∨ (1540 ≤ b ∧ b < 1798) ∨ b = 721 ∨ b = 722) :
      wires [.CX g (w b)]⊆(mS5 w g).toFinset := gate_sub5 w g _ (by
    intro q hq; simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq
    rcases hq with rfl|rfl
    · exact G
    · exact I b hb)
  have hP : wires (parGates w g k)⊆(mS5 w g).toFinset := by
    unfold parGates
    split_ifs <;> simp only [wires_append,Finset.union_subset_iff] <;>
      refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩,?_⟩ <;>
      first | exact cx _ _ (by omega) (by omega) | exact cxg _ (by omega) | simp [wires]
  have hR' : wires (rotateRight (kR w))⊆(mS5 w g).toFinset := by
    rw [(rotate_wires (kR w)).1]
    simp only [kR,wireBlock_length,show ¬(258<2) by omega,if_false]
    exact lsub5 w g _ (B 770 258 (by omega))
  have hNot : wires (notRegister (kR w))⊆(mS5 w g).toFinset := by
    rw [notRegister_wires]
    exact lsub5 w g _ (B 770 258 (by omega))
  have hPr : wires (prodPart w g)⊆(mS5 w g).toFinset := by
    unfold prodPart
    rw [show ([.CCX g (w 1028) (w 721),.CCX (w 514) (w 1028) (w 722)] : Program)=
      [.CCX g (w 1028) (w 721)]++[.CCX (w 514) (w 1028) (w 722)] from rfl,wires_append,Finset.union_subset_iff]
    constructor <;> apply gate_sub5 <;> intro q hq <;>
      simp only [Instr.wires,Finset.mem_insert,Finset.mem_singleton] at hq <;>
      rcases hq with rfl|rfl|rfl <;> first | exact G | exact I _ (by omega)
  have hL : wires (loadK w g k)⊆(mS5 w g).toFinset := by
    simp only [loadK,wires_append,Finset.union_subset_iff]
    refine ⟨⟨⟨⟨⟨?_,mskH g G _⟩,mskH _ (I 514 (by omega)) _⟩,mskH _ (I 1028 (by omega)) _⟩,
      mskH _ (I 721 (by omega)) _⟩,mskH _ (I 722 (by omega)) _⟩
    exact (xorConstant_wires_subset (hR w) _).trans (lsub5 w g _ (B 0 258 (by omega)))
  have hKOld : wires (kAddM w)⊆(mS5 w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [mappedRead_wires,List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · exact B 0 258 (by omega) q hq
    · exact B 770 258 (by omega) q hq
    · exact B 1540 257 (by omega) q hq
    · exact I 1797 (by omega)
  have hK : wires (E1WholeKAdd52Research.flagKAdd52 w)⊆(mS5 w g).toFinset := by
    have sub := E1ResourceBridge52Research.flag_support52 w
    rw [← kAdd_literal w] at sub
    apply sub.trans
    refine Finset.union_subset hKOld ?_
    exact Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr (I 1028 (by omega)))
  have hM1 : wires [.measureX (w 722) [] [.CZ (w 514) (w 1028)]]⊆(mS5 w g).toFinset := by
    apply gate_sub5; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl <;> exact I _ (by omega)
  have hM2 : wires [.measureX (w 721) [] [.CZ g (w 1028)]]⊆(mS5 w g).toFinset := by
    apply gate_sub5; intro q hq
    simp only [Instr.wires,correctionWires,Finset.mem_union,Finset.mem_singleton,Finset.mem_insert,
      Finset.notMem_empty,Finset.union_empty,Finset.empty_union] at hq
    rcases hq with rfl|rfl|rfl
    · exact I _ (by omega)
    · exact G
    · exact I _ (by omega)
  have hCp : wires (copyRegister none (wireBlock w 770 257) (hpR w))⊆(mS5 w g).toFinset := by
    rw [copyRegister_wires none _ _ (by simp [hpR,wireBlock_length])]
    split
    · exact Finset.empty_subset _
    · apply lsub5; intro q hq
      simp only [Option.toList_none,List.nil_append,List.mem_append] at hq
      rcases hq with hq|hq
      · exact B 770 257 (by omega) q hq
      · exact B 1 257 (by omega) q hq
  have hH : wires (hAddM w)⊆(mS5 w g).toFinset := by
    apply (mappedAdd_wires_subset _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [List.mem_append,List.mem_singleton] at hq
    rcases hq with ((hq|hq)|hq)|rfl
    · rw [dBits_wire w q hq]; exact I 1028 (by omega)
    · exact B 1 257 (by omega) q hq
    · exact B 1540 256 (by omega) q hq
    · exact I 1797 (by omega)
  have hW : wires [.CX (w 1028) (w 0),.X (w 0)]⊆(mS5 w g).toFinset := by
    rw [show ([.CX (w 1028) (w 0),.X (w 0)] : Program)=[.CX (w 1028) (w 0)]++[.X (w 0)] from rfl,
      wires_append,Finset.union_subset_iff]
    refine ⟨cx 1028 0 (by omega) (by omega),gate_sub5 w g _ ?_⟩
    intro q hq; simp only [Instr.wires,Finset.mem_singleton] at hq; rw [hq]; exact I 0 (by omega)
  have hT : wires (loadT w g k)⊆(mS5 w g).toFinset := by
    simp only [loadT,wires_append,Finset.union_subset_iff]
    exact ⟨mskT g G _,mskT _ (I 721 (by omega)) _⟩
  have hE : wires (eraseLtChain (hp8 w) (tR w) (hC3 w) (w 1797) (w 514))⊆(mS5 w g).toFinset := by
    apply (eraseLtChain_wires_subset _ _ _ _ _).trans
    apply lsub5; intro q hq
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with ((hq|hq)|hq)|rfl|rfl
    · exact B 1 256 (by omega) q hq
    · exact B 1029 256 (by omega) q hq
    · exact B 1540 255 (by omega) q hq
    · exact I 1797 (by omega)
    · exact I 514 (by omega)
  have hHT : wires (hAddT w)⊆(mS5 w g).toFinset := (hAddT_wires w).trans hH
  simp only [merged,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hC,⟨hP,hR'⟩,hNot⟩,hPr⟩,hL⟩,hK⟩,hL⟩,hM1⟩,hCp⟩,hHT⟩,hW⟩,hT⟩,hE⟩,hT⟩,hM2⟩


end ECDSAAdd.Entrant.E1Reflected

namespace ECDSAAdd.Entrant.StairSquareEntryR

open ECDSAAdd Arithmetic Secp256k1 ControlledPointLayout MappedCompressed CompressedPointDialog
  CompressedAllocation CompressedFieldSupport DirectSkywalk E1QubitPlacement
  E1ReflectedPlacement StairSquareHolesCore

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires




/-- The new square tail. -/
def entryRH (k : Fp) : Program := hostRename entryPairs (entryR L0 k)

theorem pmapR_512 : pmapR L0 (base 512) = host512 := by decide +kernel
theorem pmapR_511 : pmapR L0 (base 511) = hole725 := by decide +kernel

theorem base512_S : base 512 ∈ S :=
  List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 512 (by omega))
theorem base511_S : base 511 ∈ S :=
  List.mem_toFinset.mpr (E1Merge.in_mSites base (base 2400) 511 (by omega))

/-- Support of `entryR` (k-free), without the host. -/
theorem entryR_support (k : Fp) :
    wires (entryR L0 k) ⊆ ((E1Reflected.mS5 base (base 2400)).map (pmapR L0)).toFinset := by
  intro x hx
  simp only [entryR, renameProgram_support, Finset.mem_image] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, List.mem_toFinset.mp
    (E1Reflected.merged_support512 base (base 2400) k.val hy), rfl⟩)

theorem host_free (k : Fp) : host512 ∉ wires (entryR L0 k) := by
  intro h
  simp only [entryR, renameProgram_support, Finset.mem_image] at h
  obtain ⟨y, hy, e⟩ := h
  have yS : y ∈ S := mergedR_S k.val hy
  have := pmap_inj L0 Baselines.layout_widths Baselines.layout_nodup y yS (base 512) base512_S
    (e.trans pmapR_512.symm)
  subst this
  exact E1Reflected.base512_not_m5
    (List.mem_toFinset.mp (E1Reflected.merged_support512 base (base 2400) k.val hy))


theorem entryPairs_hostFree (k : Fp) : ∀ ab ∈ entryPairs, ab.2 ∉ wires (entryR L0 k) := by
  intro ab hab
  simp only [entryPairs, List.mem_singleton] at hab
  subst hab
  exact host_free k

/-! ## Run equality -/

theorem entryRH_run_eq (k : Fp) (s : State) (m : List Bool)
    (hole0 : s.basis hole725 = false) (host0 : s.basis host512 = false)
    (holeOut : (run (entryR L0 k) m s).basis hole725 = false) :
    run (entryRH k) m s = run (entryR L0 k) m s :=
  hostRename_run_eq entryPairs _ s m
    (by intro ab hab; simp only [entryPairs, List.mem_singleton] at hab; subst hab; exact hole0)
    (by intro ab hab; simp only [entryPairs, List.mem_singleton] at hab; subst hab; exact host0)
    (by intro ab hab; simp only [entryPairs, List.mem_singleton] at hab; subst hab; exact holeOut)
    (entryPairs_hostFree k)

theorem hole_pool : hole725 ∈ L0.dialogPool := by
  rw [← pmapR_511]
  apply pmap_pool L0 Baselines.layout_widths Baselines.layout_nodup _ base511_S
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    omega
  · intro e
    have := base_injective e
    omega

theorem host_pool : host512 ∈ L0.dialogPool := by
  rw [← pmapR_512]
  apply pmap_pool L0 Baselines.layout_widths Baselines.layout_nodup _ base512_S
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    simp only [List.mem_range'_1] at hj
    have := base_injective e
    omega
  · intro e
    have := base_injective e
    omega


theorem tickF_free : hole725 ∉ wires (E1QubitPlacement.tickF L0) := by
  intro h
  simp only [E1QubitPlacement.tickF, renameProgram_support, Finset.mem_image] at h
  obtain ⟨y, hy, e⟩ := h
  have yS : y ∈ S := forward_S hy
  have := pmap_inj L0 Baselines.layout_widths Baselines.layout_nodup y yS (base 511) base511_S
    (e.trans pmapR_511.symm)
  subst this
  exact base511_not_prefix (List.mem_toFinset.mp ((NativeFirstDirect.prefix_support base).1 hy))

/-- The hole is zero after `entryR`, under the hypotheses of the record's `entryR_eq`. -/
theorem entryR_hole_out (k : Fp) (s r : State) (X : Nat) (hX : X < p) (G : Bool)
    (hx : regValue L0.point.x s.basis = X) (hg : s.basis L0.core.generic = G)
    (hc : regValue L0.dialogPool s.basis = 0)
    (rphase : r.phase = s.phase)
    (rx : regValue L0.point.x r.basis = p - 1 - X)
    (rout : ∀ q, q ∉ L0.point.x → r.basis q = s.basis q) (m : List Bool) :
    (run (entryR L0 k) m s).basis hole725 = false := by
  have hw := Baselines.layout_widths
  have hn := Baselines.layout_nodup
  rw [entryR_eq L0 hw hn k s r X hX G hx hg hc rphase rx rout m [], run_append,
    run_preserves_outside _ _ _ _ tickF_free]
  have gx : L0.core.generic ∉ L0.point.x := ((E1QubitPlacement.lay L0 hw hn _).2.2 rfl).1
  have px (q : Wire) (hq : q ∈ L0.dialogPool) : q ∉ L0.point.x :=
    ((E1QubitPlacement.lay L0 hw hn q).2.1 hq).1
  have rg : r.basis L0.core.generic = G := (rout _ gx).trans hg
  have rc : regValue L0.dialogPool r.basis = 0 := by
    rw [regValue_congr _ _ s.basis (fun q hq => rout q (px q hq)), hc]
  have ppos : 0 < p := by norm_num [p]
  have fca := fastConstAdd_correct L0 hw hn L0.point.x (Or.inl rfl) k (p - 1 - X) G (by omega)
    r (List.take (measurementCount (fastConstAdd L0 L0.point.x k)) []) rg rx rc
  rw [fca.2.2 _ (px _ hole_pool), rout _ (px _ hole_pool)]
  exact (regValue_zero _ _).mp hc _ hole_pool

/-! ## Counts, slots, physicality -/

theorem entryRH_counts (k : Fp) :
    toffoliCount (entryRH k) = toffoliCount (entryR L0 k) ∧
      measurementCount (entryRH k) = measurementCount (entryR L0 k) :=
  hostRename_counts _ _

theorem entryRH_slots (k : Fp) : Challenge.gateSlots (entryRH k) = Challenge.gateSlots (entryR L0 k) :=
  hostRename_slots _ _

theorem entryRH_physical (k : Fp) : GatePhysical (entryRH k) :=
  hostRename_physical _ _ (entryR_physical L0 Baselines.layout_widths Baselines.layout_nodup k)

end ECDSAAdd.Entrant.StairSquareEntryR

end
end Merge_StairSquareEntryR_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareAssembly_at_BOptimizations` -/
section Merge_StairSquareAssembly_at_BOptimizations

/-! # LT40 U6: the hole-free square, assembled from new branches

The new square core is `coreN brC brB brA = brC ++ brB ++ brA`, where each new branch is run-equal at every
branch boundary (`BranchPre`) to the record's branch wrapper around a new body (`recBrC C'`, `recBrB B'`,
`recBrA A'`), and the new bodies satisfy the record's body contracts (`BodyCOK`, `BodyBOK`, `BodyAOK`).
From these named hypotheses:
* `coreN_correct` / `fastCoreN_correct`: the same conclusion as `SumSavedB95Core.core_correct` /
  `SumSavedB95Square.fastCore_correct`;
* `squareN_base`: the conclusion of `A161Generic.squareEntry_base` for the new square
  `squareN = place L0 (coreN …) ++ entryRH (k - delta)`, and `squareN_run_eq` (run-equal to the record square);
* `recBrB_correct`: the record's B wrapper is correct for every body satisfying `BodyBOK`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareAssembly

open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout Secp256k1
  ControlLoan1589BFFold CompressedPointDialog R2SqEp760 StairSquareContract

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires




theorem hdW : D0 ∉ G0 :: K0.wires := (B3CarryPort.pool1540_facts L0 hw0 hn0).1
theorem hdE : D0 ∉ E0 := (B3CarryPort.pool1540_facts L0 hw0 hn0).2.1

/-! ## The record's B wrapper is correct for every `BodyBOK` body -/

theorem recBrB_unswapped_correct (B : Program) (hB : BodyBOK B) (Bv O : Nat)
    (hO : O < SquareReduction.p) (s : State) (records : List Bool)
    (hb : regValue K0.core.high s.basis = Bv) (ho : regValue K0.core.out s.basis = O)
    (hp0 : regValue K0.core.product s.basis = 0) (hc : K0.PairClean s.basis)
    (hsum : s.basis K0.core.sumCarry = false) (hz : regValue E0 s.basis = 0) :
    (run (ParkCopy.withLowK2P K0 E0 G0 K0.core.high (K0.core.product.take 256) B) records s).phase =
        s.phase ∧
      regValue K0.core.out
          (run (ParkCopy.withLowK2P K0 E0 G0 K0.core.high (K0.core.product.take 256) B) records s).basis =
        ControlLoan1589BFFold.resBF ((if s.basis G0 then Bv else 0)^2) O (s.basis G0) ∧
      ∀ q, q ∉ K0.core.out →
        (run (ParkCopy.withLowK2P K0 E0 G0 K0.core.high (K0.core.product.take 256) B) records s).basis q =
          s.basis q := by
  have hw := hwK
  have hn := controlND
  have he := hext
  have nd := ndK
  have hcw : G0 ∉ K0.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis G0 then Bv else 0
  have bb : Bv < 2^128 := by
    simpa [K0.core.high_length hw.core, hb] using regValue_lt K0.core.high s.basis
  have mb : M < 2^128 := by cases h : s.basis G0 <;> simp [M, h]; omega
  have srcCount (q : Wire) : K0.core.high.count q ≤ (K0.core.y ++ [K0.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (K0.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 K0.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high, List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (K0.core.product.take 256).count q ≤ K0.core.product.count q :=
    (List.take_sublist 256 K0.core.product).count_le q
  have dstZero : regValue (K0.core.product.take 256) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀ q ∈ E0, q ∉ ECDSAAdd.wires B := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (hB.support hw'))
  apply ParkCopy.withLowK2P_correct K0 hw G0 hn K0.core.high (K0.core.product.take 256) srcCount dstCount
    (by simp [K0.core.high_length hw.core]) (by simp [K0.core.high_length hw.core])
    (by simp [hw.core.product, K0.core.high_length hw.core]) (K0.core.high_length hw.core) E0 he.nodup
    he.away he.len B hbody s records hc dstZero hz
  intro t m dstValue same
  rw [hb] at dstValue
  change regValue (K0.core.product.take 256) t.basis = M^2 at dstValue
  have full : regValue K0.core.product t.basis = M^2 :=
    K0.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := K0.measured_product_frame_clean nd (K0.core.product.take 256) dstCount s.basis t.basis hc same
  have outAway (q : Wire) (hq : q ∈ K0.core.out) : q ∉ K0.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (K0.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue K0.core.out t.basis = O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : G0 ∉ K0.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires, CuccaroStreamedSquareLayout.wires,
      List.mem_of_mem_take h])
  have ctrlT : t.basis G0 = s.basis G0 := same G0 ctrlProd
  have hg : t.basis G0 = false → M = 0 := by
    intro h; rw [ctrlT] at h; simp [M, h]
  have sumProd : K0.core.sumCarry ∉ K0.core.product.take 256 := by
    intro h
    apply ParkCarryDevelop.sumCarry_away K0 nd
    simp [ParkCarryDevelop.restWires, List.mem_of_mem_take h]
  have hsumT : t.basis K0.core.sumCarry = false := (same _ sumProd).trans hsum
  have sourceT : regValue K0.core.high t.basis = Bv := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    apply same q
    intro bad
    have vy : q ∈ K0.core.y := List.mem_of_mem_drop (List.mem_of_mem_take hq)
    have yp := List.count_pos_iff.mpr vy
    have pp := List.count_pos_iff.mpr (List.mem_of_mem_take bad)
    have lc := ControlLoan1589BFFold.layoutCount K0 nd q
    omega
  have hSource : M = if t.basis G0 then regValue K0.core.high t.basis else 0 := by
    rw [sourceT, ctrlT]
  have frame := hB.frame t.basis M mb full clean hsumT O hO hg hSource t m ⟨outO, fun _ _ => rfl⟩
  rw [ControlLoan1589BFFold.bO4_eq M O (t.basis G0) mb hg hO, ctrlT] at frame
  exact ⟨frame.1, frame.2.1, frame.2.2⟩

theorem recBrB_correct (B : Program) (hB : BodyBOK B) (Bv O : Nat)
    (hO : O < SquareReduction.p) (s : State) (records : List Bool)
    (hb : regValue K0.core.high s.basis = Bv) (ho : regValue K0.core.out s.basis = O)
    (hp0 : regValue K0.core.product s.basis = 0) (hc : K0.PairClean s.basis)
    (hsum : s.basis K0.core.sumCarry = false) (hz : regValue E0 s.basis = 0) :
    (run (recBrB B) records s).phase = s.phase ∧
      regValue K0.core.out (run (recBrB B) records s).basis =
        ControlLoan1589BFFold.resBF ((if s.basis G0 then Bv else 0)^2) O (s.basis G0) ∧
      ∀ q, q ∉ K0.core.out → (run (recBrB B) records s).basis q = s.basis q := by
  have u := recBrB_unswapped_correct B hB Bv O hO s records hb ho hp0 hc hsum hz
  have srcCount (q : Wire) : K0.core.high.count q ≤ (K0.core.y ++ [K0.core.sumCarry]).count q := by
    have h := (List.take_sublist 128 (K0.core.y.drop 128)).count_le q
    have d := (List.drop_sublist 128 K0.core.y).count_le q
    simp only [CuccaroStreamedSquareLayout.high, List.count_append] at h ⊢
    omega
  have dstCount (q : Wire) : (K0.core.product.take 256).count q ≤ K0.core.product.count q :=
    (List.take_sublist 256 K0.core.product).count_le q
  have dstZero : regValue (K0.core.product.take 256) s.basis = 0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have fin := u.2.2 (sqRet K0) (sqRet_not_out K0 hwK ndK)
  rw [sqRet_clean K0 hwK _ hc] at fin
  have eq := withLowK2P_swap_run_eq K0 hwK G0 controlND K0.core.high (K0.core.product.take 256)
    srcCount dstCount (by simp [K0.core.high_length hwK.core]) (by simp [K0.core.high_length hwK.core])
    (by simp [hwK.core.product, K0.core.high_length hwK.core]) E0 hext.nodup hext.away hext.len B
    hB.support s records hc dstZero hz fin
  simp only [recBrB]
  rw [eq]
  exact u

/-! ## The new core -/



/-- The new square. -/
def squareN (brC brB brA : Program) (k : Fp) : Program :=
  placedN brC brB brA ++ StairSquareEntryR.entryRH (k - (C163Low4Offsets.delta : Fp))



/-! ## Generic (variable-layout) square chain

Everything heavy is proved for a variable `L`, exactly as in the record, and only instantiated at `L0`. -/

/-- The core-level correctness statement (`SumSavedB95Core.core_correct`'s conclusion at the dialog layout). -/
def CoreOK (L : ControlledPointLayout) (P : Program) : Prop :=
  ∀ (Y O : Nat), O < SquareReduction.p → ∀ (s : State) (records : List Bool),
    regValue L.dialogStreamedSquareWide.core.y s.basis = Y →
    regValue L.dialogStreamedSquareWide.core.out s.basis = O →
    regValue L.dialogStreamedSquareWide.core.product s.basis = 0 →
    s.basis L.dialogStreamedSquareWide.core.sumCarry = false →
    L.dialogStreamedSquareWide.PairClean s.basis →
    regValue (OwnDiagAll12Square.kext L) s.basis = 0 →
    s.basis (L.core.poolWire 1540) = false →
    (run P records s).phase = s.phase ∧
    regValue L.dialogStreamedSquareWide.core.out (run P records s).basis =
      SquareReduction.p - 1 -
        (((O + SquareReduction.p - (if s.basis L.core.generic then Y^2 else 0) % SquareReduction.p) %
            SquareReduction.p +
          (if s.basis L.core.generic then C163Low4Offsets.squareK else 0)) % SquareReduction.p) ∧
    ∀ q, q ∉ L.dialogStreamedSquareWide.core.out → (run P records s).basis q = s.basis q

theorem fastG_correct (L : ControlledPointLayout) (hw : L.Widths) (hn : L.wires.Nodup) (P : Program)
    (hP : CoreOK L P) (X Y : Nat) (Bc : Bool) (hX : X < p)
    (s : State) (m : List Bool) (hb : s.basis L.core.generic = Bc)
    (hx : regValue L.point.x s.basis = X) (hy : regValue L.point.y s.basis = Y)
    (hc : regValue L.dialogPool s.basis = 0) :
    (run P m s).phase = s.phase ∧
    regValue L.point.x (run P m s).basis =
      p - 1 - (((X + p - (if Bc then Y * Y else 0) % p) % p +
        (if Bc then C163Low4Offsets.squareK else 0)) % p) ∧
    ∀ q, q ∉ L.point.x → (run P m s).basis q = s.basis q := by
  let K := L.dialogStreamedSquareWide
  have auxZero (q : Wire)
      (hq : q ∈ K.core.product ++ K.core.pad ++ K.core.work ++
        [K.core.productHigh, K.core.outHigh, K.core.workHigh, K.core.cin,
          K.core.normFlag, K.core.modFlag, K.core.sumCarry] ++ K.overflowPad) :
      s.basis q = false := by
    change q ∈ L.dialogStreamedSquareWide.core.product ++
      L.dialogStreamedSquareWide.core.pad ++ L.dialogStreamedSquareWide.core.work ++
      [L.dialogStreamedSquareWide.core.productHigh, L.dialogStreamedSquareWide.core.outHigh,
        L.dialogStreamedSquareWide.core.workHigh, L.dialogStreamedSquareWide.core.cin,
        L.dialogStreamedSquareWide.core.normFlag, L.dialogStreamedSquareWide.core.modFlag,
        L.dialogStreamedSquareWide.core.sumCarry] ++ L.dialogStreamedSquareWide.overflowPad at hq
    rw [L.dialogStreamedSquareWide_pool hw] at hq
    exact (regValue_zero _ _).mp hc q (List.mem_of_mem_take hq)
  have prod0 : regValue K.core.product s.basis = 0 := by
    apply (regValue_zero _ _).mpr
    intro q hq
    exact auxZero q (by simp [hq])
  have clean : K.PairClean s.basis := by
    constructor
    · apply (regValue_zero _ _).mpr
      intro q hq
      simp only [CuccaroStreamedSquareWideLayout.foldPad, List.mem_append] at hq
      exact auxZero q (by simp; tauto)
    · apply (regValue_zero _ _).mpr
      intro q hq
      exact auxZero q (by simp [hq])
    all_goals exact auxZero _ (by simp)
  have sum0 : s.basis K.core.sumCarry = false := auxZero _ (by simp)
  have hp : SquareReduction.p = p := by
    norm_num [SquareReduction.p, SquareReduction.B, SquareReduction.c, p]
  have hz : regValue (OwnDiagAll12Square.kext L) s.basis = 0 :=
    (regValue_zero _ _).mpr
      (fun q hq => (regValue_zero _ _).mp hc q (OwnDiagAll12Square.kext_mem L hw q hq))
  have kernel := hP Y X (by simpa only [hp] using hX) s m hy hx prod0 sum0 clean hz
    ((regValue_zero _ _).mp hc _ (B3CarryPort.pool1540_facts L hw hn).2.2)
  simpa only [hb, hp, pow_two] using kernel



/-- A replacement tail is run-equal to `entryR` on the states the square leaves. -/
def TailOK (L : ControlledPointLayout) (T : Fp → Program) : Prop :=
  ∀ (k : Fp) (a r : State) (X : Nat), X < p → ∀ (G : Bool),
    regValue L.point.x a.basis = X → a.basis L.core.generic = G → regValue L.dialogPool a.basis = 0 →
    r.phase = a.phase → regValue L.point.x r.basis = p - 1 - X →
    (∀ q, q ∉ L.point.x → r.basis q = a.basis q) →
    ∀ m : List Bool, run (T k) m a = run (E1ReflectedPlacement.entryR L k) m a


/-- U5 in the `TailOK` shape. -/
theorem entryRH_tailOK : TailOK L0 StairSquareEntryR.entryRH := by
  intro k a r X hX G hx hg hc rphase rx rout m
  exact StairSquareEntryR.entryRH_run_eq k a m ((regValue_zero _ _).mp hc _ StairSquareEntryR.hole_pool)
    ((regValue_zero _ _).mp hc _ StairSquareEntryR.host_pool)
    (StairSquareEntryR.entryR_hole_out k a r X hX G hx hg hc rphase rx rout m)

section Core






end Core

/-! ## Counts and physicality -/



theorem recBrB_counts (X Y : Program) :
    toffoliCount (recBrB X) + toffoliCount Y = toffoliCount (recBrB Y) + toffoliCount X ∧
      measurementCount (recBrB X) + measurementCount Y = measurementCount (recBrB Y) + measurementCount X := by
  simp only [recBrB, ParkCopy.withLowK2P, ParkCopy.pB, bodySwap,
    toffoliCount_append, measurementCount_append, (renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2]
  constructor <;> omega

theorem recBrA_counts (X Y : Program) :
    toffoliCount (recBrA X) + toffoliCount Y = toffoliCount (recBrA Y) + toffoliCount X ∧
      measurementCount (recBrA X) + measurementCount Y = measurementCount (recBrA Y) + measurementCount X := by
  simp only [recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10, ParkCopy10.pB, bodySwap,
    toffoliCount_append, measurementCount_append, (renameProgram_counts _ _).1,
    (renameProgram_counts _ _).2]
  constructor <;> omega




theorem squareN_physical (brC brB brA : Program) (k : Fp) (hpC : GatePhysical brC)
    (hpB : GatePhysical brB) (hpA : GatePhysical brA) : GatePhysical (squareN brC brB brA k) := by
  simp only [squareN, placedN, gatePhysical_append, R2SqEp760.place_physical_iff, coreN]
  exact ⟨⟨⟨hpC, hpB⟩, hpA⟩, StairSquareEntryR.entryRH_physical _⟩

theorem squareN_slots (brC brB brA : Program) (k : Fp) :
    Challenge.gateSlots (squareN brC brB brA k) =
      Challenge.gateSlots brC + Challenge.gateSlots brB + Challenge.gateSlots brA +
        Challenge.gateSlots (E1ReflectedPlacement.entryR L0 (k - (C163Low4Offsets.delta : Fp))) := by
  simp only [squareN, placedN, SquareCarryLoan719BF.place, coreN, Challenge.gateSlots_append,
    Baselines.rename_gateSlots, StairSquareEntryR.entryRH_slots]

/-! ## Field 12: hole freedom of the placed new core -/





/-! ## Layout selector (drop-in for `A161Generic.squareEntry L k` in generic-`L` statements) -/






section Select



end Select

end ECDSAAdd.Entrant.StairSquareAssembly

end
end Merge_StairSquareAssembly_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareKernel26Support_at_BOptimizations` -/
section Merge_StairSquareKernel26Support_at_BOptimizations

/-! # LT39 K0: support facts for hosting the kernel holes (inner-S bits) on the outer-S bits

The record square's three leaves use the kernel `K := LowZero18LowK.kg L ext src dst`, whose clean-sum producer
`Q1 = LowZero18Diagonal.makeC (iregs …)` and cleanup `Q1c = RawClearSquare.clearC (iregs …)` use the inner sum register
`iregs.S = ktmp[66..98]`. The holes `ktmp[68..98]` (pool 720..750) are inner-S bits 2..32. The record already renamed
`ktmp[67]` (pool 719) to `ktmp[1]` (pool 653) in `Q1`/`Q1c` (`SquareCarryLoan719.patchKG`); here the same is prepared
for the 31 holes, hosted on the outer-S bits `ktmp[2..32]` (pool 654..684).

Statements (all for variable layouts; no concrete program is evaluated):
* `holes_mem_inner`, `holes_mem_X1`, `hosts_mem_outer` — where the two lists live;
* `hosts_Q1_free` — the hosts are not wires of `Q1` / `Q1c`;
* `holes_make_tail_free`, `holes_clearPrefix_free`, `holes_sumSavedPrefix_free` — the holes are not wires of the rest of
  the producer, of the record clear prefix, or of the SumSaved (C-branch) clear prefix;
* `tmp_park_free`, `tmp_park10_free`, `tmp_parkS_free` — no `ktmp` wire is used by the park pieces around the kernel;
* index facts (`holes_hosts_nodup`, `*_ne_target`, `*_ne_earlyHost`, …).
-/

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic

namespace ECDSAAdd.Entrant.StairSquareKernel26
open Arithmetic.CuccaroStreamedSquareWideLayout StairSquareHolesCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- The 31 kernel holes: inner-S bits 2..32 = `ktmp[68..98]` (pool 720..750). -/
def holes (L : CuccaroStreamedSquareWideLayout) : List Wire := ((LowZero18LowK.ktmp L).drop 68).take 31

/-- Their hosts: outer-S bits 2..32 = `ktmp[2..32]` (pool 654..684). -/
def hosts (L : CuccaroStreamedSquareWideLayout) : List Wire := ((LowZero18LowK.ktmp L).drop 2).take 31

/-- hole i ↦ host i. -/
def pairs (L : CuccaroStreamedSquareWideLayout) : List (Wire × Wire) := (holes L).zip (hosts L)


/-! ## index helpers -/






/-! ## the ktmp block -/

section Layout
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)

omit hw in
theorem holes_index (q : Wire) (h : q∈holes L) :
    ∃ k, k<(LowZero18LowK.ktmp L).length ∧ 68≤k ∧ k<99 ∧ (LowZero18LowK.ktmp L).getD k 0=q := by
  obtain ⟨k,a,b,c,d⟩ := slice_index _ 68 31 q h
  exact ⟨k,a,b,by omega,d⟩

omit hw in
theorem hosts_index (q : Wire) (h : q∈hosts L) :
    ∃ k, k<(LowZero18LowK.ktmp L).length ∧ 2≤k ∧ k<33 ∧ (LowZero18LowK.ktmp L).getD k 0=q := by
  obtain ⟨k,a,b,c,d⟩ := slice_index _ 2 31 q h
  exact ⟨k,a,b,by omega,d⟩

theorem holes_sub_ktmp (q : Wire) (h : q∈holes L) : q∈LowZero18LowK.ktmp L :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

theorem hosts_sub_ktmp (q : Wire) (h : q∈hosts L) : q∈LowZero18LowK.ktmp L :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

include hw in
theorem holes_length : (holes L).length=31 := by
  have len := LowZero18LowK.ktmp_length L hw
  simp only [holes,List.length_take,List.length_drop,len]
  decide

include hw in
theorem hosts_length : (hosts L).length=31 := by
  have len := LowZero18LowK.ktmp_length L hw
  simp only [hosts,List.length_take,List.length_drop,len]
  decide

include hw in
theorem holesOf_pairs : holesOf (pairs L)=holes L := by
  simp only [holesOf,pairs]
  exact List.map_fst_zip (by rw [holes_length L hw,hosts_length L hw])

include hw in
theorem hostsOf_pairs : hostsOf (pairs L)=hosts L := by
  simp only [hostsOf,pairs]
  exact List.map_snd_zip (by rw [holes_length L hw,hosts_length L hw])

include hw in
/-- The holes lie in the inner sum register. -/
theorem holes_mem_inner (ext src dst : List Wire) :
    ∀ q∈holes L, q∈(LowZero18LowK.iregs L ext src dst).S := by
  intro q h
  obtain ⟨k,kl,a,b,rfl⟩ := holes_index L q h
  exact slice_mem _ 66 33 k kl (by omega) (by omega)



end Layout

/-! ## leaf section -/

section Leaf
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

include hn hs hd hx hdx in
theorem ktmp_nodup : (LowZero18LowK.ktmp L).Nodup := by
  apply knd (LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx)
  intro q
  simp only [LowZero18LowK.kbig2,List.count_append,List.count_cons]
  omega

include hn hs hd hx hdx in
/-- `ktmp` is disjoint from every other wire the leaf names. -/
theorem tmp_off : ∀ q∈LowZero18LowK.ktmp L, q∉outside L ext control src dst := by
  intro q hq
  apply kdis (LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx) _ q hq
  intro w
  simp only [outside,LowZero18LowK.kbig2,List.count_append,List.count_cons]
  omega


/-! ### register inventories -/

theorem iregs_all_sub (q : Wire) (h : q∈(LowZero18LowK.iregs L ext src dst).all) :
    q∈outside L ext control src dst ∨ q∈(LowZero18LowK.iregs L ext src dst).S := by
  simp only [KRegs.all,LowZero18LowK.iregs,LowZero18LowK.oregs,KRegs.lo,KRegs.dlo,
    List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h|h|h|h|h
  · exact Or.inl (by rw [h]; exact out_cin L control ext src dst)
  · exact Or.inl (out_bank L control ext src dst q (List.mem_of_mem_take h))
  · exact Or.inl (out_dst L control ext src dst q (List.mem_of_mem_take h))
  · exact Or.inr h
  · exact Or.inl (out_ext L control ext src dst q (List.mem_of_mem_drop (List.mem_of_mem_take h)))
  · exact Or.inl (out_carry L control ext src dst q
      (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take h))))
  · exact Or.inl (out_pad L control ext src dst q h)
  · exact Or.inl (out_carry L control ext src dst q (List.mem_of_mem_take h))

theorem oregs_all_sub (q : Wire) (h : q∈(LowZero18LowK.oregs L ext src dst).all) :
    q∈outside L ext control src dst ∨ q∈(LowZero18LowK.oregs L ext src dst).S := by
  simp only [KRegs.all,LowZero18LowK.oregs,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h|h|h|h|h
  · exact Or.inl (by rw [h]; exact out_cin L control ext src dst)
  · exact Or.inl (out_bank L control ext src dst q h)
  · exact Or.inl (out_dst L control ext src dst q h)
  · exact Or.inr h
  · exact Or.inl (out_ext L control ext src dst q (List.mem_of_mem_take (List.mem_of_mem_take h)))
  · exact Or.inl (out_carry L control ext src dst q (List.mem_of_mem_drop (List.mem_of_mem_take h)))
  · exact Or.inl (out_pad L control ext src dst q h)
  · exact Or.inl (out_carry L control ext src dst q (List.mem_of_mem_take h))

theorem jregsH_all_sub (q : Wire) (h : q∈(LowZero18LowK.jregsH L ext src dst).all) :
    q∈outside L ext control src dst ∨ q∈(LowZero18LowK.oregs L ext src dst).S := by
  simp only [KRegs.all,LowZero18LowK.jregsH,LowZero18LowK.oregs,KRegs.hi,KRegs.dhi,
    List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h|h|h|h|h
  · exact Or.inl (by rw [h]; exact out_cin L control ext src dst)
  · exact Or.inl (out_bank L control ext src dst q (List.mem_of_mem_drop h))
  · exact Or.inl (out_dst L control ext src dst q (List.mem_of_mem_drop h))
  · exact Or.inl (out_ext L control ext src dst q
      (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take h))))
  · exact Or.inl (out_ext L control ext src dst q (List.mem_of_mem_drop (List.mem_of_mem_take h)))
  · exact Or.inl (out_carry L control ext src dst q
      (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take h))))
  · exact Or.inl (out_pad L control ext src dst q h)
  · exact Or.inl (out_carry L control ext src dst q (List.mem_of_mem_take h))

theorem jregsS_all_sub (q : Wire) (h : q∈(LowZero18LowK.jregsS L ext src dst).all) :
    q∈outside L ext control src dst ∨ q∈(LowZero18LowK.oregs L ext src dst).S := by
  simp only [KRegs.all,LowZero18LowK.jregsS,List.mem_cons,List.mem_append,or_assoc] at h
  rcases h with h|h|h|h|h|h|h|h
  · exact Or.inl (by rw [h]; exact out_cin L control ext src dst)
  · exact Or.inr h
  · have h' : q∈(ext.take 132).take (2*(src.length-63)) := h
    exact Or.inl (out_ext L control ext src dst q (List.mem_of_mem_take (List.mem_of_mem_take h')))
  · exact Or.inl (out_ext L control ext src dst q (List.mem_of_mem_drop (List.mem_of_mem_take h)))
  · exact Or.inl (out_ext L control ext src dst q (List.mem_of_mem_drop (List.mem_of_mem_take h)))
  · have h' : q∈((L.leafCarry.drop 193).take 62).take 31 := h
    exact Or.inl (out_carry L control ext src dst q
      (List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_of_mem_take h'))))
  · have h' : q∈L.leafPad := h
    exact Or.inl (out_pad L control ext src dst q h')
  · have h' : q∈L.leafCarry.take 193 := h
    exact Or.inl (out_carry L control ext src dst q (List.mem_of_mem_take h'))

/-! ### where holes and hosts are not -/

include hw hn hs hd hx hdx in
theorem holes_not_outerS : ∀ q∈holes L, q∉(LowZero18LowK.oregs L ext src dst).S := by
  intro q h used
  have nd := ktmp_nodup L control hn ext src dst hs hd hx hdx
  obtain ⟨k,kl,a,b,rfl⟩ := holes_index L q h
  have used' : (LowZero18LowK.ktmp L).getD k 0∈((LowZero18LowK.ktmp L).take 66).take (src.length-63) := used
  have u : (LowZero18LowK.ktmp L).getD k 0∈((LowZero18LowK.ktmp L).drop 0).take 66 :=
    take_as_slice _ _ _ (List.mem_of_mem_take used')
  obtain ⟨j,jl,c,d,e⟩ := slice_index _ 0 66 _ u
  have := getD_index_inj _ nd j k jl kl e
  omega

include hw hn hs hd hx hdx in
theorem hosts_not_innerS : ∀ q∈hosts L, q∉(LowZero18LowK.iregs L ext src dst).S := by
  intro q h used
  have nd := ktmp_nodup L control hn ext src dst hs hd hx hdx
  obtain ⟨k,kl,a,b,rfl⟩ := hosts_index L q h
  obtain ⟨j,jl,c,d,e⟩ := slice_index (LowZero18LowK.ktmp L) 66 33 _ used
  have := getD_index_inj _ nd j k jl kl e
  omega

include hw hn hs hd hx hdx in
theorem holes_hosts_nodup : (holes L++hosts L).Nodup := by
  have nd := ktmp_nodup L control hn ext src dst hs hd hx hdx
  have sub (a n : Nat) : List.Sublist (((LowZero18LowK.ktmp L).drop a).take n) (LowZero18LowK.ktmp L) :=
    (List.take_sublist _ _).trans (List.drop_sublist _ _)
  refine List.nodup_append.mpr ⟨nd.sublist (sub 68 31),nd.sublist (sub 2 31),?_⟩
  intro a ha b hb e
  obtain ⟨k,kl,k1,k2,rfl⟩ := holes_index L a ha
  obtain ⟨j,jl,j1,j2,rfl⟩ := hosts_index L b hb
  have := getD_index_inj _ nd k j kl jl e
  omega

include hw hn hs hd hx hdx in
/-- Holes and hosts avoid the two sites of the record's `earlyPerm` (`ktmp[67]`, `ktmp[1]`). -/
theorem tmp_ne_early (q : Wire) (hq : q∈holes L ∨ q∈hosts L) :
    q≠SquareCarryLoan719.target L ∧ q≠SquareCarryLoan719.earlyHost L := by
  have nd := ktmp_nodup L control hn ext src dst hs hd hx hdx
  have len := LowZero18LowK.ktmp_length L hw
  obtain ⟨k,kl,k1,k2,rfl⟩ : ∃ k, k<(LowZero18LowK.ktmp L).length ∧
      ((68≤k ∧ k<99) ∨ (2≤k ∧ k<33)) ∧ True ∧ (LowZero18LowK.ktmp L).getD k 0=q := by
    rcases hq with h|h
    · obtain ⟨k,kl,a,b,e⟩ := holes_index L q h
      exact ⟨k,kl,Or.inl ⟨a,b⟩,trivial,e⟩
    · obtain ⟨k,kl,a,b,e⟩ := hosts_index L q h
      exact ⟨k,kl,Or.inr ⟨a,b⟩,trivial,e⟩
  constructor
  · intro e
    change (LowZero18LowK.ktmp L).getD k 0=(LowZero18LowK.ktmp L).getD 67 0 at e
    have := getD_index_inj _ nd k 67 kl (by omega) e
    omega
  · intro e
    change (LowZero18LowK.ktmp L).getD k 0=(LowZero18LowK.ktmp L).getD 1 0 at e
    have := getD_index_inj _ nd k 1 kl (by omega) e
    omega

include hw hn hs hd hx hdx in
theorem early_fix (q : Wire) (hq : q∈holes L ∨ q∈hosts L) : SquareCarryLoan719.earlyPerm L q=q := by
  have ne := tmp_ne_early L hw control hn ext src dst hs hd hx hdx q hq
  rw [SquareCarryLoan719.earlyPerm_eq L hw]
  exact Equiv.swap_apply_of_ne_of_ne ne.1 ne.2

include hw hn hs hd hx hdx he in
/-- Holes and hosts are fixed by the fold rename `foldPerm` (= swap ktmp[67] ext[0]) and by `bodySwap`
(= swap sqRet sqHost, sqRet = ktmp[108], sqHost = ext[130]). -/
theorem tmp_fold_fix (q : Wire) (hq : q∈holes L ∨ q∈hosts L) :
    SquareCarryLoan719.foldPerm L ext q=q ∧ R2SqEp760.sqSwap L ext q=q := by
  have nd := ktmp_nodup L control hn ext src dst hs hd hx hdx
  have len := LowZero18LowK.ktmp_length L hw
  have ne := tmp_ne_early L hw control hn ext src dst hs hd hx hdx q hq
  have inT : q∈LowZero18LowK.ktmp L := by
    rcases hq with h|h
    · exact holes_sub_ktmp L q h
    · exact hosts_sub_ktmp L q h
  have offE : q∉ext := fun h => tmp_off L control hn ext src dst hs hd hx hdx q inT
    (out_ext L control ext src dst q h)
  have k := (by
    rcases hq with h|h
    · obtain ⟨k,kl,a,b,e⟩ := holes_index L q h
      exact ⟨k,kl,Or.inl ⟨a,b⟩,e⟩
    · obtain ⟨k,kl,a,b,e⟩ := hosts_index L q h
      exact ⟨k,kl,Or.inr ⟨a,b⟩,e⟩ :
    ∃ k, k<(LowZero18LowK.ktmp L).length ∧ ((68≤k ∧ k<99) ∨ (2≤k ∧ k<33)) ∧
      (LowZero18LowK.ktmp L).getD k 0=q)
  obtain ⟨k,kl,kr,rfl⟩ := k
  refine ⟨?_,?_⟩
  · rw [SquareCarryLoan719.foldPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne ne.1 (fun e => offE (e ▸ DiagSq.getD_in ext 0 (by omega)))
  · unfold R2SqEp760.sqSwap
    apply Equiv.swap_apply_of_ne_of_ne
    · intro e
      rw [R2SqEp760.sqRet_ktmp L] at e
      have := getD_index_inj _ nd k 108 kl (by omega) e
      omega
    · exact fun e => offE (e ▸ DiagSq.getD_in ext 130 (by omega))

/-! ### K0: kernel supports -/

include hw h128 hsmax hlen he in
theorem kg_Q1_support :
    wires (LowZero18LowK.kg L ext src dst).Q1⊆(LowZero18LowK.iregs L ext src dst).all.toFinset ∧
    wires (LowZero18LowK.kg L ext src dst).Q1c⊆(LowZero18LowK.iregs L ext src dst).all.toFinset := by
  have wi := LowZero18LowK.iregs_W L hw ext src dst h128 hsmax hlen he
  have ip := (LowZero18LowK.iregs L ext src dst).piece_support wi
  have is := LowZero18Diagonal.steps_support (LowZero18LowK.iregs L ext src dst) wi
  have isc := (LowZero18LowK.iregs L ext src dst).scl1591_support wi
  have sk := (LowZero18LowK.iregs L ext src dst).smkT_support wi ip.1
  have q1 : wires (LowZero18Diagonal.makeC (LowZero18LowK.iregs L ext src dst))⊆
      (LowZero18LowK.iregs L ext src dst).all.toFinset := by
    simp only [LowZero18Diagonal.makeC,wires_append]
    exact Finset.union_subset is.1 isc
  have q1c : wires (LowZero18Diagonal.clearC (LowZero18LowK.iregs L ext src dst))⊆
      (LowZero18LowK.iregs L ext src dst).all.toFinset := by
    simp only [LowZero18Diagonal.clearC,RawClearSquare.clearC,wires_append]
    exact Finset.union_subset sk is.2
  unfold LowZero18LowK.kg
  split
  · exact ⟨q1,q1c⟩
  · exact ⟨q1,q1c⟩

include hw hn hs hd h128 hsmax hlen hx hdx he in
/-- K0 (hosts): the outer-S hosts are not wires of the kernel's `Q1` or `Q1c`. -/
theorem hosts_Q1_free :
    ∀ q∈hosts L, q∉wires (LowZero18LowK.kg L ext src dst).Q1 ∧
      q∉wires (LowZero18LowK.kg L ext src dst).Q1c := by
  intro q hq
  have sup := kg_Q1_support L hw ext src dst h128 hsmax hlen he
  have off : q∉(LowZero18LowK.iregs L ext src dst).all.toFinset := by
    intro used
    rcases iregs_all_sub L control ext src dst q (List.mem_toFinset.mp used) with h|h
    · exact tmp_off L control hn ext src dst hs hd hx hdx q (hosts_sub_ktmp L q hq) h
    · exact hosts_not_innerS L hw control hn ext src dst hs hd hx hdx q hq h
  exact ⟨fun u => off (sup.1 u),fun u => off (sup.2 u)⟩

/-- The rest of the producer after `Q1`. -/
def tail (K : KG) : Program := K.Q2++K.R.smk++K.Q5++K.R.m6h++K.R.m7k++K.R.m8z++K.R.scl1591

theorem tail_support (K : KG) (w : K.R.W) (A : Finset Wire) (hR : K.R.all.toFinset⊆A)
    (h2 : wires K.Q2⊆A) (h5 : wires K.Q5⊆A) : wires (tail K)⊆A := by
  have p := K.R.piece_support w
  have sc := K.R.scl1591_support w
  have m := p.2.2.1
  simp only [wires_append,Finset.union_subset_iff] at m
  have m6 := K.R.m6h_support w m.1.1
  have m7 := (K.R.m7k_wires w).trans m.1.2
  have m8 := (K.R.m8z_wires w).trans m.2
  simp only [tail,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨h2,p.1.trans hR⟩,h5⟩,m6.trans hR⟩,m7.trans hR⟩,m8.trans hR⟩,sc.trans hR⟩

theorem clearPrefix_support (K : KG) (w : K.R.W) (A : Finset Wire) (hR : K.R.all.toFinset⊆A)
    (h2 : wires K.Q2c⊆A) (h5 : wires K.Q5c⊆A) : wires (LowZero18Square.clearPrefix K)⊆A := by
  have p := K.R.piece_support w
  have sc := K.R.scl1591_support w
  have c := p.2.2.2.1
  simp only [wires_append,Finset.union_subset_iff] at c
  have sk := K.R.smkT_support w p.1
  have c8 := (K.R.c8z_wires w).trans c.1.1
  have c7 := (K.R.c7t_wires).trans c.1.2
  have c6 := (K.R.c6h_wires w).trans c.2
  simp only [LowZero18Square.clearPrefix,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨⟨⟨sk.trans hR,c8.trans hR⟩,c7.trans hR⟩,c6.trans hR⟩,h5⟩,sc.trans hR⟩,h2⟩

/-- `outside ∪ outer S` as a finset: every kernel wire except the inner-S block. -/
def outerSet : Finset Wire :=
  (outside L ext control src dst++(LowZero18LowK.oregs L ext src dst).S).toFinset

theorem outerSet_of (q : Wire) (h : q∈outside L ext control src dst ∨ q∈(LowZero18LowK.oregs L ext src dst).S) :
    q∈outerSet L control ext src dst := by
  unfold outerSet
  rcases h with h|h
  · exact List.mem_toFinset.mpr (List.mem_append_left _ h)
  · exact List.mem_toFinset.mpr (List.mem_append_right _ h)

include hw hn hs hd hx hdx in
theorem holes_not_outerSet : ∀ q∈holes L, q∉outerSet L control ext src dst := by
  intro q hq used
  rcases List.mem_append.mp (List.mem_toFinset.mp used) with h|h
  · exact tmp_off L control hn ext src dst hs hd hx hdx q (holes_sub_ktmp L q hq) h
  · exact holes_not_outerS L hw control hn ext src dst hs hd hx hdx q hq h

theorem sub_outerSet_of (R : KRegs) (h : ∀ q∈R.all, q∈outside L ext control src dst ∨
    q∈(LowZero18LowK.oregs L ext src dst).S) : R.all.toFinset⊆outerSet L control ext src dst :=
  fun q hq => outerSet_of L control ext src dst q (h q (List.mem_toFinset.mp hq))

include hw h128 hsmax hlen he in
theorem kg_rest_support :
    wires (tail (LowZero18LowK.kg L ext src dst))⊆outerSet L control ext src dst ∧
    wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))⊆outerSet L control ext src dst := by
  have w := LowZero18LowK.oregs_W L hw ext src dst h128 hsmax hlen he
  have rp := (LowZero18LowK.oregs L ext src dst).piece_support w
  have rK := sub_outerSet_of L control ext src dst _ (oregs_all_sub L control ext src dst)
  by_cases h : src.length=128
  · have wj := LowZero18LowK.jregsH_W L hw ext src dst h hlen he
    have js := LowZero18Diagonal.steps_support (LowZero18LowK.jregsH L ext src dst) wj
    have jK := sub_outerSet_of L control ext src dst _ (jregsH_all_sub L control ext src dst)
    have q5 := ((TrimMid.tsqM_wires_le (LowZero18LowK.oregs L ext src dst).S (LowZero18LowK.oregs L ext src dst).T
      (LowZero18LowK.oregs L ext src dst).pad (LowZero18LowK.oregs L ext src dst).carry
      (LowZero18LowK.oregs L ext src dst).cin).1.trans rp.2.2.2.2.2.2.1).trans rK
    have q5c := ((PlainKnownClear.program_wires_le (LowZero18LowK.oregs L ext src dst).S
      (LowZero18LowK.oregs L ext src dst).T (LowZero18LowK.oregs L ext src dst).pad
      (LowZero18LowK.oregs L ext src dst).carry (LowZero18LowK.oregs L ext src dst).cin).trans
      rp.2.2.2.2.2.2.2).trans rK
    rw [LowZero18LowK.kg,if_pos h]
    exact ⟨tail_support (LowZero18LowK.kgH L ext src dst) w _ rK (js.1.trans jK) q5,
      clearPrefix_support (LowZero18LowK.kgH L ext src dst) w _ rK (js.2.trans jK) q5c⟩
  · have wj := LowZero18LowK.jregsS_W L hw ext src dst (by omega) hlen he
    have js := LowZero18Diagonal.steps_support (LowZero18LowK.jregsS L ext src dst) wj
    have jK := sub_outerSet_of L control ext src dst _ (jregsS_all_sub L control ext src dst)
    have q2 := ((TrimMid.tsqM_wires_le (LowZero18LowK.oregs L ext src dst).hi (LowZero18LowK.oregs L ext src dst).dhi
      (LowZero18LowK.oregs L ext src dst).pad (LowZero18LowK.oregs L ext src dst).carry
      (LowZero18LowK.oregs L ext src dst).cin).1.trans rp.2.2.2.2.1).trans rK
    have q2c := ((PlainKnownClear.program_wires_le (LowZero18LowK.oregs L ext src dst).hi
      (LowZero18LowK.oregs L ext src dst).dhi (LowZero18LowK.oregs L ext src dst).pad
      (LowZero18LowK.oregs L ext src dst).carry (LowZero18LowK.oregs L ext src dst).cin).trans
      rp.2.2.2.2.2.1).trans rK
    rw [LowZero18LowK.kg,if_neg h]
    exact ⟨tail_support (LowZero18LowK.kgS L ext src dst) w _ rK q2 (js.1.trans jK),
      clearPrefix_support (LowZero18LowK.kgS L ext src dst) w _ rK q2c (js.2.trans jK)⟩

include hw hn hs hd h128 hsmax hlen hx hdx he in
/-- K0 (holes): the holes are not wires of the producer after `Q1`. -/
theorem holes_make_tail_free :
    ∀ q∈holes L, q∉wires (tail (LowZero18LowK.kg L ext src dst)) :=
  fun q hq u => holes_not_outerSet L hw control hn ext src dst hs hd hx hdx q hq
    ((kg_rest_support L hw control ext src dst h128 hsmax hlen he).1 u)

include hw hn hs hd h128 hsmax hlen hx hdx he in
/-- K0 (holes): the holes are not wires of the record clear prefix (everything before `Q1c`). -/
theorem holes_clearPrefix_free :
    ∀ q∈holes L, q∉wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst)) :=
  fun q hq u => holes_not_outerSet L hw control hn ext src dst hs hd hx hdx q hq
    ((kg_rest_support L hw control ext src dst h128 hsmax hlen he).2 u)




/-! ### park pieces use no `ktmp` wire -/



theorem move_out (a b : List Wire)
    (ha : ∀ q∈a, q∈outside L ext control src dst) (hb : ∀ q∈b, q∈outside L ext control src dst) :
    wires (ParkCopy.move a b)⊆(outside L ext control src dst).toFinset := by
  intro q u
  have h := List.mem_toFinset.mp (R2SqEp760.park_move_wires a b u)
  apply List.mem_toFinset.mpr
  rcases List.mem_append.mp h with h|h
  · exact ha q h
  · exact hb q h

theorem dummies_out (a : List Wire) (ha : ∀ q∈a, q∈outside L ext control src dst) :
    wires (ParkCopy.dummies a)⊆(outside L ext control src dst).toFinset :=
  fun q u => List.mem_toFinset.mpr (ha q (List.mem_toFinset.mp (R2SqEp760.park_dummies_wires a u)))

theorem free_of_out (P : Program) (h : wires P⊆(outside L ext control src dst).toFinset)
    (off : ∀ q∈LowZero18LowK.ktmp L, q∉outside L ext control src dst) :
    ∀ q∈LowZero18LowK.ktmp L, q∉wires P :=
  fun q hq u => off q hq (List.mem_toFinset.mp (h u))


include hw hn hd hlen h128 in
theorem cache_out : LowZero18Square.cacheWire L dst∈outside L ext control src dst := by
  have hp : 0<dst.length := by omega
  rw [LowZero18Square.cacheWire_fixed L hw (List.nodup_cons.mp hn).2 dst hd hp]
  exact out_dst L control ext src dst _ (CachedSquareCopy.head_mem dst hp)

include hw hn hs hd h128 hlen hx hdx he in
/-- Park pieces of the B leaf (`ParkCopy.withLowK2P`) use no `ktmp` wire. -/
theorem tmp_park_free : ∀ q∈LowZero18LowK.ktmp L,
    q∉wires (ParkCopy.pA L control src) ∧ q∉wires (ParkCopy.pE1 L control src) ∧
    q∉wires (ParkCopy.pD ext) ∧ q∉wires (ParkCopy.pMI L ext src) ∧
    q∉wires (ParkCopy.pC1 L ext control src dst) ∧ q∉wires (ParkCopy.pMO L ext src) ∧
    q∉wires (ParkCopy.pE L control src) := by
  have off := tmp_off L control hn ext src dst hs hd hx hdx
  have hostsO : ∀ q∈ParkCopy.hosts ext, q∈outside L ext control src dst :=
    fun q h => out_ext L control ext src dst q (ParkCopy.hosts_sub ext he q h)
  have bl : 119≤(L.inputBank.take src.length).length := by
    simp only [List.length_take,(L.measured_bank_widths hw).1];omega
  have pc1 : wires (ParkCopy.pC1 L ext control src dst)⊆(outside L ext control src dst).toFinset := by
    intro q u
    have sub := InnerLinearCopy.copy_wires control (LowZero18Square.cacheWire L dst)
      (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)
      (src.take 119) ((L.inputBank.take src.length).take 119)
      (by simp only [List.length_take];omega) (by rw [List.length_take];exact Nat.min_eq_left bl) u
    apply List.mem_toFinset.mpr
    rcases Finset.mem_union.mp sub with u|r
    · rcases Finset.mem_union.mp (CachedSquareCopy.wires_subset _ _ _ _ u) with h|h
      · exact List.mem_toFinset.mp (copy_out L control ext src dst _ _ (src_take_out L control ext src dst 119)
          (bank_take_out L control ext src dst 119) h)
      · rw [Finset.mem_singleton.mp h]
        exact cache_out L hw control hn ext src dst hd h128 hlen
    · simp only [Finset.mem_insert,Finset.mem_singleton] at r
      rcases r with e|e|e <;> exact out_ext L control ext src dst q (e ▸ DiagSq.getD_in ext _ (by omega))
  intro q hq
  refine ⟨free_of_out L control ext src dst _ (copy_out L control ext src dst _ _
      (fun q h => out_src L control ext src dst q h) (fun q h => out_bank L control ext src dst q h)) off q hq,
    free_of_out L control ext src dst _ (erase_out L control ext src dst _ _ (src_take_out L control ext src dst 119)
      (bank_take_out L control ext src dst 119)) off q hq,
    free_of_out L control ext src dst _ (dummies_out L control ext src dst _ hostsO) off q hq,
    free_of_out L control ext src dst _ (move_out L control ext src dst _ _ (bank_drop_out L control ext src dst 119)
      hostsO) off q hq,
    free_of_out L control ext src dst _ pc1 off q hq,
    free_of_out L control ext src dst _ (move_out L control ext src dst _ _ hostsO
      (bank_drop_out L control ext src dst 119)) off q hq,
    free_of_out L control ext src dst _ (erase_out L control ext src dst _ _ (fun q h => out_src L control ext src dst q h)
      (fun q h => out_bank L control ext src dst q h)) off q hq⟩

include hw hn hs hd h128 hlen hx hdx he in
/-- Park pieces of the A leaf (`ParkCopy10.withLowK2P10`, extra parking wire `g ∉ ktmp`) use no `ktmp` wire. -/
theorem tmp_park10_free (g : Wire) (hg : g∉LowZero18LowK.ktmp L) : ∀ q∈LowZero18LowK.ktmp L,
    q∉wires (ParkCopy10.pA L control src) ∧ q∉wires (ParkCopy10.pE1 L control src) ∧
    q∉wires (ParkCopy10.pD ext g) ∧ q∉wires (ParkCopy10.pMI L ext src g) ∧
    q∉wires (ParkCopy10.pC1 L ext control src dst) ∧ q∉wires (ParkCopy10.pMO L ext src g) ∧
    q∉wires (ParkCopy10.pE L control src) := by
  have off := tmp_off L control hn ext src dst hs hd hx hdx
  have bl : 118≤(L.inputBank.take src.length).length := by
    simp only [List.length_take,(L.measured_bank_widths hw).1];omega
  have pc1 : wires (ParkCopy10.pC1 L ext control src dst)⊆(outside L ext control src dst).toFinset := by
    intro q u
    have sub := InnerLinearCopy.copy_wires118 control (LowZero18Square.cacheWire L dst)
      (ext.getD 198 0) (ext.getD 199 0) (ext.getD 233 0)
      (src.take 118) ((L.inputBank.take src.length).take 118)
      (by simp only [List.length_take];omega) (by rw [List.length_take];exact Nat.min_eq_left bl) u
    apply List.mem_toFinset.mpr
    rcases Finset.mem_union.mp sub with u|r
    · rcases Finset.mem_union.mp (CachedSquareCopy.wires_subset _ _ _ _ u) with h|h
      · exact List.mem_toFinset.mp (copy_out L control ext src dst _ _ (src_take_out L control ext src dst 118)
          (bank_take_out L control ext src dst 118) h)
      · rw [Finset.mem_singleton.mp h]
        exact cache_out L hw control hn ext src dst hd h128 hlen
    · simp only [Finset.mem_insert,Finset.mem_singleton] at r
      rcases r with e|e|e <;> exact out_ext L control ext src dst q (e ▸ DiagSq.getD_in ext _ (by omega))
  -- the parking list is `hosts ext ++ [g]`: hosts are `ext` wires, `g` is handled separately
  have hostsFree : ∀ q∈LowZero18LowK.ktmp L, q∉ParkCopy10.hosts10 ext g := by
    intro q hq h
    simp only [ParkCopy10.hosts10,List.mem_append,List.mem_singleton] at h
    rcases h with h|h
    · exact off q hq (out_ext L control ext src dst q (ParkCopy.hosts_sub ext he q h))
    · exact hg (h ▸ hq)
  intro q hq
  refine ⟨free_of_out L control ext src dst _ (copy_out L control ext src dst _ _
      (fun q h => out_src L control ext src dst q h) (fun q h => out_bank L control ext src dst q h)) off q hq,
    free_of_out L control ext src dst _ (erase_out L control ext src dst _ _ (src_take_out L control ext src dst 118)
      (bank_take_out L control ext src dst 118)) off q hq,
    fun u => hostsFree q hq (List.mem_toFinset.mp (R2SqEp760.park_dummies_wires _ u)),
    fun u => ?_,
    free_of_out L control ext src dst _ pc1 off q hq,
    fun u => ?_,
    free_of_out L control ext src dst _ (erase_out L control ext src dst _ _ (fun q h => out_src L control ext src dst q h)
      (fun q h => out_bank L control ext src dst q h)) off q hq⟩
  · rcases List.mem_append.mp (List.mem_toFinset.mp (R2SqEp760.park_move_wires _ _ u)) with h|h
    · exact off q hq (bank_drop_out L control ext src dst 118 q h)
    · exact hostsFree q hq h
  · rcases List.mem_append.mp (List.mem_toFinset.mp (R2SqEp760.park_move_wires _ _ u)) with h|h
    · exact hostsFree q hq h
    · exact off q hq (bank_drop_out L control ext src dst 118 q h)

include hw hn hs hd h128 hlen hx hdx he in
/-- Park pieces of the C leaf (`ParkCopyS`, the SumSaved leaf `SumSavedPark.withLowK2S`) use no `ktmp` wire. -/
theorem tmp_parkS_free : ∀ q∈LowZero18LowK.ktmp L,
    q∉wires (ParkCopyS.pA L control src) ∧ q∉wires (ParkCopyS.pE1 L control src) ∧
    q∉wires (ParkCopyS.pD ext) ∧ q∉wires (ParkCopyS.pMI L ext src) ∧
    q∉wires (ParkCopyS.pC1 L control src dst) ∧ q∉wires (ParkCopyS.pMO L ext src) ∧
    q∉wires (ParkCopyS.pE L control src) := by
  have off := tmp_off L control hn ext src dst hs hd hx hdx
  have hostsO : ∀ q∈ParkCopyS.hostsS ext, q∈outside L ext control src dst :=
    fun q h => out_ext L control ext src dst q (ParkCopyS.hostsS_sub ext he q h)
  have pc1 : wires (ParkCopyS.pC1 L control src dst)⊆(outside L ext control src dst).toFinset := by
    intro q u
    apply List.mem_toFinset.mpr
    rcases Finset.mem_union.mp (CachedSquareCopy.wires_subset _ _ _ _ u) with h|h
    · exact List.mem_toFinset.mp (copy_out L control ext src dst _ _ (src_take_out L control ext src dst 124)
        (bank_take_out L control ext src dst 124) h)
    · rw [Finset.mem_singleton.mp h]
      exact cache_out L hw control hn ext src dst hd h128 hlen
  intro q hq
  exact ⟨free_of_out L control ext src dst _ (copy_out L control ext src dst _ _
      (fun q h => out_src L control ext src dst q h) (fun q h => out_bank L control ext src dst q h)) off q hq,
    free_of_out L control ext src dst _ (erase_out L control ext src dst _ _ (src_take_out L control ext src dst 124)
      (bank_take_out L control ext src dst 124)) off q hq,
    free_of_out L control ext src dst _ (dummies_out L control ext src dst _ hostsO) off q hq,
    free_of_out L control ext src dst _ (move_out L control ext src dst _ _ (bank_drop_out L control ext src dst 124)
      hostsO) off q hq,
    free_of_out L control ext src dst _ pc1 off q hq,
    free_of_out L control ext src dst _ (move_out L control ext src dst _ _ hostsO
      (bank_drop_out L control ext src dst 124)) off q hq,
    free_of_out L control ext src dst _ (erase_out L control ext src dst _ _ (fun q h => out_src L control ext src dst q h)
      (fun q h => out_bank L control ext src dst q h)) off q hq⟩

end Leaf

end ECDSAAdd.Entrant.StairSquareKernel26
end Merge_StairSquareKernel26Support_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareKernel26Run_at_BOptimizations` -/
section Merge_StairSquareKernel26Run_at_BOptimizations

/-! # LT39: the kernel blocks `Q1` / `Q1c` hosted on the outer-S bits — leaf-level run equality (0 T)

`patch ps K` renames the kernel's clean-sum producer `Q1` and its cleanup `Q1c` by `hostRename ps`
(LT31's list of swaps). On top of the record's own pool-719 rename (`SquareCarryLoan719.patchKG`) this gives
`make2` / `clear2` / `sumSavedClear2`, and the three park leaves `withLowK2P2` (B), `withLowK2P10'` (A),
`withLowK2S2` (C).

`two_block_run_eq` is the abstract statement: renaming two blocks `Q1`, `Q1c` of `A ++ Q1 ++ Mid ++ Q1c ++ E` does not
change the run when the holes are zero after `Q1` and untouched by `Mid`, the hosts are untouched by both blocks, and
holes and hosts are zero at entry and at exit. For the leaves, "zero after `Q1`" is the kernel's own `mk1` invariant
(`invC`: inner S = 0) and "zero at exit" comes from the leaf's frame (`fin`, a hypothesis). -/

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic

namespace ECDSAAdd.Entrant.StairSquareKernel26
open Arithmetic.CuccaroStreamedSquareWideLayout StairSquareHolesCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## abstract two-block rename -/






/-! ## the renamed kernel -/


/-- New producer: the record's `LowZero18Square.make` with `Q1` further renamed by `ps`. -/
def make2 (ps : List (Wire × Wire)) (L : CuccaroStreamedSquareWideLayout) (K : KG) : Program :=
  LowZero18KG.make (patch ps (LowZero18Square.patchKG L K))

/-- New cleanup: the record's `LowZero18Square.clear` with `Q1c` further renamed by `ps`. -/
def clear2 (ps : List (Wire × Wire)) (L : CuccaroStreamedSquareWideLayout) (K : KG) : Program :=
  LowZero18KG.clear (patch ps (LowZero18Square.patchKG L K))


theorem mem_ps (L : CuccaroStreamedSquareWideLayout) (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L))
    (ab : Wire × Wire) (h : ab∈ps) : ab.1∈holes L ∧ ab.2∈hosts L :=
  List.of_mem_zip (hps.subset h)

theorem ps_nodup (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ps : List (Wire × Wire))
    (hps : List.Sublist ps (pairs L)) (hnd : (holes L++hosts L).Nodup) : (holesOf ps++hostsOf ps).Nodup := by
  have a : List.Sublist (holesOf ps) (holes L) := by
    rw [← holesOf_pairs L hw]; exact hps.map Prod.fst
  have b : List.Sublist (hostsOf ps) (hosts L) := by
    rw [← hostsOf_pairs L hw]; exact hps.map Prod.snd
  exact hnd.sublist (a.append b)

theorem holesOf_mem (L : CuccaroStreamedSquareWideLayout) (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L))
    (q : Wire) (hq : q∈holesOf ps) : ∃ ab∈ps, ab.1=q ∧ q∈holes L := by
  obtain ⟨ab,h,e⟩ := List.mem_map.mp hq
  exact ⟨ab,h,e,e ▸ (mem_ps L ps hps ab h).1⟩

/-! ## leaf section -/

section Leaf
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)

/-- The record's producer block (with the pool-719 rename). -/
abbrev Q1r : Program := renameProgram (SquareCarryLoan719.earlyPerm L) (LowZero18LowK.kg L ext src dst).Q1
/-- The record's cleanup block (with the pool-719 rename). -/
abbrev Q1cr : Program := renameProgram (SquareCarryLoan719.earlyPerm L) (LowZero18LowK.kg L ext src dst).Q1c

include hn hs hd hx hdx in
theorem pre_off : ∀ q∈L.core.cin::dst++L.leafPad++L.leafCarry++LowZero18LowK.ktmp L++ext,
    q∉control::(src++L.inputBank.take src.length) := by
  intro q hq
  apply kdis (LowZero18LowK.kbig2_nodup L control hn src dst hs hd ext hx hdx) _ q hq
  intro w
  simp only [LowZero18LowK.kbig2,List.count_append,List.count_cons]
  omega

include hn hs hd hx hdx in
theorem pA0_free : ∀ q∈LowZero18LowK.ktmp L, q∉wires (pA0 L control src) :=
  free_of_out L control ext src dst _ (copy_out L control ext src dst _ _
    (fun q h => out_src L control ext src dst q h) (fun q h => out_bank L control ext src dst q h))
    (tmp_off L control hn ext src dst hs hd hx hdx)

include hn hs hd hx hdx in
theorem pE0_free : ∀ q∈LowZero18LowK.ktmp L, q∉wires (pE0 L control src) :=
  free_of_out L control ext src dst _ (erase_out L control ext src dst _ _
    (fun q h => out_src L control ext src dst q h) (fun q h => out_bank L control ext src dst q h))
    (tmp_off L control hn ext src dst hs hd hx hdx)

theorem tmp_zero (s : State) (hc : L.PairClean s.basis) : ∀ q∈LowZero18LowK.ktmp L, s.basis q=false :=
  fun q h => (regValue_zero _ _).mp hc.pad q (List.mem_of_mem_drop h)

include hw hn hs hd h128 hsmax hlen hx hdx he in
/-- After the bank copy and the record's (pool-719 renamed) producer block, the holes are zero:
the kernel's `mk1` invariant `invC` says the inner sum register is zero. -/
theorem q1_holes_out (s : State) (hc : L.PairClean s.basis) (hzero : regValue dst s.basis=0)
    (hz : regValue ext s.basis=0) (r1 r2 : List Bool) :
    ∀ q∈holes L, (run (Q1r L ext src dst) r2 (run (pA0 L control src) r1 s)).basis q=false := by
  intro q hq
  have hall := LowZero18LowK.kg_nodup L control hn ext src dst hs hd hx hdx
  have sp := LowZero18LowK.kg_spec L hw ext src dst h128 hsmax hlen he hall
  have hKR := LowZero18LowK.kg_R L ext src dst
  have banks := L.measured_leaf_banks_clean s.basis hc src.length
  have tmp0 := tmp_zero L s hc
  have off := pre_off L control hn ext src dst hs hd hx hdx
  generalize hu : run (pA0 L control src) r1 s=u0
  have keep : ∀ w∈L.core.cin::dst++L.leafPad++L.leafCarry++LowZero18LowK.ktmp L++ext,
      u0.basis w=s.basis w := by
    intro w hw'
    rw [← hu]
    apply run_preserves_outside
    intro u
    have h := List.mem_toFinset.mp (copyRegister_wires_subset _ _ _ u)
    apply off w hw'
    simp only [Option.toList_some,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,
      or_false] at h ⊢
    tauto
  have kC : u0.basis L.core.cin=s.basis L.core.cin := keep _ (by simp)
  have kD (w : Wire) (h : w∈dst) : u0.basis w=s.basis w := keep w (by
    simp only [List.mem_cons,List.mem_append]; tauto)
  have kP (w : Wire) (h : w∈L.leafPad) : u0.basis w=s.basis w := keep w (by
    simp only [List.mem_cons,List.mem_append]; tauto)
  have kR (w : Wire) (h : w∈L.leafCarry) : u0.basis w=s.basis w := keep w (by
    simp only [List.mem_cons,List.mem_append]; tauto)
  have kT (w : Wire) (h : w∈LowZero18LowK.ktmp L) : u0.basis w=s.basis w := keep w (by
    simp only [List.mem_cons,List.mem_append]; tauto)
  have kE (w : Wire) (h : w∈ext) : u0.basis w=s.basis w := keep w (by
    simp only [List.mem_cons,List.mem_append]; tauto)
  have hd0 : regValue (LowZero18LowK.kg L ext src dst).R.dlo u0.basis=0 := by
    rw [hKR]
    apply (regValue_zero _ _).mpr
    intro w h
    have h' : w∈dst := List.mem_of_mem_take (h : w∈dst.take (2*64))
    rw [kD w h']
    exact (regValue_zero _ _).mp hzero w h'
  have hX0 : regValue (LowZero18LowK.kg L ext src dst).X1 u0.basis=0 := by
    apply (regValue_zero _ _).mpr
    intro w h
    have hX : w∈(LowZero18LowK.kg L ext src dst).X := by
      simp only [KG.X,List.mem_append]; tauto
    rcases LowZero18LowK.kg_X L ext src dst w hX with e|e
    · rw [kE w e]; exact (regValue_zero _ _).mp hz w e
    · have t : w∈LowZero18LowK.ktmp L := List.mem_of_mem_drop (List.mem_of_mem_take e)
      rw [kT w t]; exact tmp0 w t
  have hp0 : regValue (LowZero18LowK.kg L ext src dst).R.pad u0.basis=0 := by
    rw [hKR]
    apply (regValue_zero _ _).mpr
    intro w h
    have h' : w∈L.leafPad := h
    rw [kP w h']
    exact (regValue_zero _ _).mp banks.2.1 w h'
  have hc0 : regValue (LowZero18LowK.kg L ext src dst).R.carry u0.basis=0 := by
    rw [hKR]
    apply (regValue_zero _ _).mpr
    intro w h
    have h' : w∈L.leafCarry := List.mem_of_mem_take (h : w∈L.leafCarry.take 193)
    rw [kR w h']
    exact (regValue_zero _ _).mp banks.2.2 w h'
  have hz0 : regValue (LowZero18LowK.kg L ext src dst).R.z u0.basis=0 := by
    rw [hKR]
    apply (regValue_zero _ _).mpr
    intro w h
    have h' : w∈L.leafCarry :=
      List.mem_of_mem_drop (List.mem_of_mem_take (h : w∈(L.leafCarry.drop 193).take 62))
    rw [kR w h']
    exact (regValue_zero _ _).mp banks.2.2 w h'
  have hi0 : u0.basis (LowZero18LowK.kg L ext src dst).R.cin=false := by
    rw [hKR]
    exact kC.trans hc.cin
  have hostIn : u0.basis (SquareCarryLoan719.earlyHost L)=false := by
    have m : SquareCarryLoan719.earlyHost L∈LowZero18LowK.ktmp L := by
      change (LowZero18LowK.ktmp L).getD 1 0∈LowZero18LowK.ktmp L
      exact DiagSq.getD_in _ 1 (by rw [LowZero18LowK.ktmp_length L hw]; omega)
    rw [kT _ m]; exact tmp0 _ m
  have innerZero : ∀ v t, (LowZero18LowK.kg L ext src dst).I1 v t → t (SquareCarryLoan719.target L)=false := by
    intro v t inv
    rw [LowZero18LowK.kg_I1] at inv
    exact (regValue_zero _ _).mp inv.1 _ (SquareCarryLoan719Support.target_mem_inner L hw ext src dst)
  have eq := SquareCarryLoan719.q1_run_eq L hw (LowZero18LowK.kg L ext src dst) sp
    (LowZero18SquareSupport.target_mem_X1 L hw ext src dst)
    (LowZero18SquareSupport.earlyHost_Q1_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he).1
    innerZero u0 r2 hd0 hX0 hp0 hc0 hz0 hi0 hostIn
  rw [eq]
  have old := sp.mk1 u0 r2 hd0 hX0 hp0 hc0 hz0 hi0
  have i1 := old.2.2.1
  rw [LowZero18LowK.kg_I1] at i1
  exact (regValue_zero _ _).mp i1.1 q (holes_mem_inner L hw ext src dst q hq)

include hw hn hs hd h128 hsmax hlen hx hdx he in
/-- Leaf-level run equality, for any material `Mid0` between producer and cleanup and any clear prefix `C0`
that avoid the holes. `fin`: no `ktmp` wire is left non-zero by the original leaf. -/
theorem leaf_run_eq (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L)) (Mid0 C0 : Program)
    (hMid : ∀ ab∈ps, ab.1∉wires Mid0) (hC : ∀ ab∈ps, ab.1∉wires C0)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis) (hzero : regValue dst s.basis=0)
    (hz : regValue ext s.basis=0)
    (fin : ∀ q∈LowZero18LowK.ktmp L, (run (pA0 L control src++Q1r L ext src dst++
      (tail (LowZero18LowK.kg L ext src dst)++Mid0++C0)++Q1cr L ext src dst++pE0 L control src) m s).basis q=false) :
    run (pA0 L control src++hostRename ps (Q1r L ext src dst)++
      (tail (LowZero18LowK.kg L ext src dst)++Mid0++C0)++hostRename ps (Q1cr L ext src dst)++pE0 L control src) m s=
    run (pA0 L control src++Q1r L ext src dst++
      (tail (LowZero18LowK.kg L ext src dst)++Mid0++C0)++Q1cr L ext src dst++pE0 L control src) m s := by
  have mem := mem_ps L ps hps
  have tmp0 := tmp_zero L s hc
  have hT (ab : Wire × Wire) (h : ab∈ps) : ab.1∈LowZero18LowK.ktmp L ∧ ab.2∈LowZero18LowK.ktmp L :=
    ⟨holes_sub_ktmp L _ (mem ab h).1,hosts_sub_ktmp L _ (mem ab h).2⟩
  have pa := pA0_free L control hn ext src dst hs hd hx hdx
  have pe := pE0_free L control hn ext src dst hs hd hx hdx
  have hq1 := hosts_Q1_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have fix := early_fix L hw control hn ext src dst hs hd hx hdx
  apply two_block_run_eq ps _ _ _ _ _ s m
  · exact fun ab h => ⟨pa _ (hT ab h).1,pa _ (hT ab h).2⟩
  · exact fun ab h => ⟨tmp0 _ (hT ab h).1,tmp0 _ (hT ab h).2⟩
  · exact fun r1 r2 ab h => q1_holes_out L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he s hc hzero hz
      r1 r2 ab.1 (mem ab h).1
  · exact fun ab h => rename_fix_free _ _ _ (fix _ (Or.inr (mem ab h).2)) (hq1 _ (mem ab h).2).1
  · intro ab h u
    simp only [wires_append,Finset.mem_union] at u
    rcases u with (u|u)|u
    · exact holes_make_tail_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he _ (mem ab h).1 u
    · exact hMid ab h u
    · exact hC ab h u
  · exact fun ab h => rename_fix_free _ _ _ (fix _ (Or.inr (mem ab h).2)) (hq1 _ (mem ab h).2).2
  · exact fun ab h => ⟨pe _ (hT ab h).1,pe _ (hT ab h).2⟩
  · exact fun ab h => ⟨fin _ (hT ab h).1,fin _ (hT ab h).2⟩

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem leaf_avoids (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L)) (Mid0 C0 : Program)
    (hMid : ∀ ab∈ps, ab.1∉wires Mid0) (hC : ∀ ab∈ps, ab.1∉wires C0) :
    ∀ q∈holesOf ps, q∉wires (pA0 L control src++hostRename ps (Q1r L ext src dst)++
      (tail (LowZero18LowK.kg L ext src dst)++Mid0++C0)++hostRename ps (Q1cr L ext src dst)++pE0 L control src) := by
  have mem := mem_ps L ps hps
  have hnd := ps_nodup L hw ps hps (holes_hosts_nodup L hw control hn ext src dst hs hd hx hdx)
  have hq1 := hosts_Q1_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have fix := early_fix L hw control hn ext src dst hs hd hx hdx
  have pa := pA0_free L control hn ext src dst hs hd hx hdx
  have pe := pE0_free L control hn ext src dst hs hd hx hdx
  apply two_block_avoids ps _ _ _ _ _ hnd
  · exact fun ab h => rename_fix_free _ _ _ (fix _ (Or.inr (mem ab h).2)) (hq1 _ (mem ab h).2).1
  · exact fun ab h => rename_fix_free _ _ _ (fix _ (Or.inr (mem ab h).2)) (hq1 _ (mem ab h).2).2
  · intro q hq
    obtain ⟨ab,h,e,hh⟩ := holesOf_mem L ps hps q hq
    exact pa q (holes_sub_ktmp L q hh)
  · intro q hq u
    obtain ⟨ab,h,rfl,hh⟩ := holesOf_mem L ps hps q hq
    simp only [wires_append,Finset.mem_union] at u
    rcases u with (u|u)|u
    · exact holes_make_tail_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he _ hh u
    · exact hMid ab h u
    · exact hC ab h u
  · intro q hq
    obtain ⟨ab,h,e,hh⟩ := holesOf_mem L ps hps q hq
    exact pe q (holes_sub_ktmp L q hh)

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem leaf_wires (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L)) (Mid0 C0 : Program) :
    wires (pA0 L control src++hostRename ps (Q1r L ext src dst)++
      (tail (LowZero18LowK.kg L ext src dst)++Mid0++C0)++hostRename ps (Q1cr L ext src dst)++pE0 L control src)⊆
    wires (pA0 L control src++Q1r L ext src dst++
      (tail (LowZero18LowK.kg L ext src dst)++Mid0++C0)++Q1cr L ext src dst++pE0 L control src)∪
      (hostsOf ps).toFinset := by
  have mem := mem_ps L ps hps
  have hnd := ps_nodup L hw ps hps (holes_hosts_nodup L hw control hn ext src dst hs hd hx hdx)
  have hq1 := hosts_Q1_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have fix := early_fix L hw control hn ext src dst hs hd hx hdx
  exact two_block_wires ps _ _ _ _ _ hnd
    (fun ab h => rename_fix_free _ _ _ (fix _ (Or.inr (mem ab h).2)) (hq1 _ (mem ab h).2).1)
    (fun ab h => rename_fix_free _ _ _ (fix _ (Or.inr (mem ab h).2)) (hq1 _ (mem ab h).2).2)

end Leaf

end ECDSAAdd.Entrant.StairSquareKernel26
end Merge_StairSquareKernel26Run_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareKernel26Branches_at_BOptimizations` -/
section Merge_StairSquareKernel26Branches_at_BOptimizations

/-! # LT39 K1–K3: the three square branches with the kernel holes hosted on the outer-S bits (0 T, 0 M)

Record square core (`SumSavedB95Core.core L ext c bodyA bodyC`):
`SumSavedCBranch.branch (C) ++ B95PortResearch.branchBF760 (B) ++ A161Low4Branch.branch (A)`.
New branches, generic in the body and parametric in the hosted pairs `ps <+ pairs L`:
* `branchA2 ps L ext c B` — `A161Low4Branch.branch L ext c B` with the kernel `Q1`/`Q1c` renamed,
* `branchB2 ps L ext c B` — `ParkCopy.withLowK2P L ext c high (product.take 256) (bodySwap L ext B)` renamed
  (the record's `B95PortResearch.branchBF760 L ext c` is this program with `B := B95SelectorResearch.hostedSelectedBody …`),
* `branchC2 ps L ext c B` — `SumSavedCBranch.branch L ext c B` renamed.
For each: run equality with the record branch (body only has to avoid the hosted holes), hole avoidance,
equal Toffoli / measurement / gate-slot counts, physicality transfer, support ⊆ record support ∪ hosts. -/

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic

namespace ECDSAAdd.Entrant.StairSquareKernel26
open Arithmetic.CuccaroStreamedSquareWideLayout StairSquareHolesCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## the three park leaves with the renamed kernel -/

/-- B leaf (`ParkCopy.withLowK2P`) with the renamed kernel. -/
def withLowK2P2 (ps : List (Wire × Wire)) (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body : Program) : Program :=
  ParkCopy.pA L control src++make2 ps L (LowZero18LowK.kg L ext src dst)++ParkCopy.pE1 L control src++
    ParkCopy.pD ext++ParkCopy.pMI L ext src++ParkCopy.pB L ext body++ParkCopy.pC1 L ext control src dst++
    ParkCopy.pMO L ext src++clear2 ps L (LowZero18LowK.kg L ext src dst)++ParkCopy.pE L control src

/-- A leaf (`ParkCopy10.withLowK2P10`) with the renamed kernel. -/
def withLowK2P10' (ps : List (Wire × Wire)) (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (src dst : List Wire) (body : Program) (g : Wire) : Program :=
  ParkCopy10.pA L control src++make2 ps L (LowZero18LowK.kg L ext src dst)++ParkCopy10.pE1 L control src++
    ParkCopy10.pD ext g++ParkCopy10.pMI L ext src g++ParkCopy10.pB L ext body++ParkCopy10.pC1 L ext control src dst++
    ParkCopy10.pMO L ext src g++clear2 ps L (LowZero18LowK.kg L ext src dst)++ParkCopy10.pE L control src


def midP (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
    (body : Program) : Program :=
  ParkCopy.pE1 L control src++ParkCopy.pD ext++ParkCopy.pMI L ext src++ParkCopy.pB L ext body++
    ParkCopy.pC1 L ext control src dst++ParkCopy.pMO L ext src

def mid10 (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
    (body : Program) (g : Wire) : Program :=
  ParkCopy10.pE1 L control src++ParkCopy10.pD ext g++ParkCopy10.pMI L ext src g++ParkCopy10.pB L ext body++
    ParkCopy10.pC1 L ext control src dst++ParkCopy10.pMO L ext src g

def midS (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (src dst : List Wire)
    (body : Program) : Program :=
  ParkCopyS.pE1 L control src++ParkCopyS.pD ext++ParkCopyS.pMI L ext src++ParkCopyS.pB L ext body++
    ParkCopyS.pC1 L control src dst++ParkCopyS.pMO L ext src

/-! ### shapes -/

section Shapes
variable (ps : List (Wire × Wire)) (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
  (src dst : List Wire) (body : Program) (g : Wire)

theorem withLowK2P2_shape : withLowK2P2 ps L ext control src dst body=
    pA0 L control src++hostRename ps (Q1r L ext src dst)++
      (tail (LowZero18LowK.kg L ext src dst)++midP L ext control src dst body++
        LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))++
      hostRename ps (Q1cr L ext src dst)++pE0 L control src := by
  simp only [withLowK2P2,midP,make2,clear2,patch,LowZero18KG.make,LowZero18KG.clear,LowZero18Square.patchKG,
    SquareCarryLoan719.patchKG,tail,LowZero18Square.clearPrefix,pA0,pE0,Q1r,Q1cr,ParkCopy.pA,ParkCopy.pE,
    List.append_assoc]

theorem withLowK2P_shape : ParkCopy.withLowK2P L ext control src dst body=
    pA0 L control src++Q1r L ext src dst++
      (tail (LowZero18LowK.kg L ext src dst)++midP L ext control src dst body++
        LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))++
      Q1cr L ext src dst++pE0 L control src := by
  simp only [ParkCopy.withLowK2P,midP,ParkCopy.pM,ParkCopy.pCL,LowZero18Square.make,LowZero18Square.clear,
    LowZero18KG.make,LowZero18KG.clear,LowZero18Square.patchKG,SquareCarryLoan719.patchKG,tail,
    LowZero18Square.clearPrefix,pA0,pE0,Q1r,Q1cr,ParkCopy.pA,ParkCopy.pE,List.append_assoc]

theorem withLowK2P10'_shape : withLowK2P10' ps L ext control src dst body g=
    pA0 L control src++hostRename ps (Q1r L ext src dst)++
      (tail (LowZero18LowK.kg L ext src dst)++mid10 L ext control src dst body g++
        LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))++
      hostRename ps (Q1cr L ext src dst)++pE0 L control src := by
  simp only [withLowK2P10',mid10,make2,clear2,patch,LowZero18KG.make,LowZero18KG.clear,LowZero18Square.patchKG,
    SquareCarryLoan719.patchKG,tail,LowZero18Square.clearPrefix,pA0,pE0,Q1r,Q1cr,ParkCopy10.pA,ParkCopy10.pE,
    List.append_assoc]

theorem withLowK2P10_shape : ParkCopy10.withLowK2P10 L ext control src dst body g=
    pA0 L control src++Q1r L ext src dst++
      (tail (LowZero18LowK.kg L ext src dst)++mid10 L ext control src dst body g++
        LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst))++
      Q1cr L ext src dst++pE0 L control src := by
  simp only [ParkCopy10.withLowK2P10,mid10,ParkCopy10.pM,ParkCopy10.pCL,LowZero18Square.make,LowZero18Square.clear,
    LowZero18KG.make,LowZero18KG.clear,LowZero18Square.patchKG,SquareCarryLoan719.patchKG,tail,
    LowZero18Square.clearPrefix,pA0,pE0,Q1r,Q1cr,ParkCopy10.pA,ParkCopy10.pE,List.append_assoc]



end Shapes

/-! ### leaf facts -/

section Leaf
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
  (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L))

include hw hn hs hd hx hdx he hps in
theorem pB_free (body : Program) (hbody : ∀ ab∈ps, ab.1∉wires body) :
    ∀ ab∈ps, ab.1∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) body) :=
  fun ab h => rename_fix_free _ _ _
    (tmp_fold_fix L hw control hn ext src dst hs hd hx hdx he _ (Or.inl (mem_ps L ps hps ab h).1)).1 (hbody ab h)

include hw hn hs hd hx hdx he hps in
theorem bodySwap_free (B : Program) (hB : ∀ ab∈ps, ab.1∉wires B) :
    ∀ ab∈ps, ab.1∉wires (R2SqEp760.bodySwap L ext B) :=
  fun ab h => rename_fix_free _ _ _
    (tmp_fold_fix L hw control hn ext src dst hs hd hx hdx he _ (Or.inl (mem_ps L ps hps ab h).1)).2 (hB ab h)

include hw hn hs hd h128 hlen hx hdx he hps in
theorem midP_free (body : Program) (hbody : ∀ ab∈ps, ab.1∉wires body) :
    ∀ ab∈ps, ab.1∉wires (midP L ext control src dst body) := by
  intro ab h u
  have t := holes_sub_ktmp L _ (mem_ps L ps hps ab h).1
  have pf := tmp_park_free L hw control hn ext src dst hs hd h128 hlen hx hdx he _ t
  have pb := pB_free L hw control hn ext src dst hs hd hx hdx he ps hps body hbody ab h
  simp only [midP,wires_append,Finset.mem_union,or_assoc] at u
  rcases u with u|u|u|u|u|u
  · exact pf.2.1 u
  · exact pf.2.2.1 u
  · exact pf.2.2.2.1 u
  · exact pb u
  · exact pf.2.2.2.2.1 u
  · exact pf.2.2.2.2.2.1 u

include hw hn hs hd h128 hlen hx hdx he hps in
theorem mid10_free (body : Program) (g : Wire) (hg : g∉LowZero18LowK.ktmp L) (hbody : ∀ ab∈ps, ab.1∉wires body) :
    ∀ ab∈ps, ab.1∉wires (mid10 L ext control src dst body g) := by
  intro ab h u
  have t := holes_sub_ktmp L _ (mem_ps L ps hps ab h).1
  have pf := tmp_park10_free L hw control hn ext src dst hs hd h128 hlen hx hdx he g hg _ t
  have pb := pB_free L hw control hn ext src dst hs hd hx hdx he ps hps body hbody ab h
  simp only [mid10,wires_append,Finset.mem_union,or_assoc] at u
  rcases u with u|u|u|u|u|u
  · exact pf.2.1 u
  · exact pf.2.2.1 u
  · exact pf.2.2.2.1 u
  · exact pb u
  · exact pf.2.2.2.2.1 u
  · exact pf.2.2.2.2.2.1 u

include hw hn hs hd h128 hlen hx hdx he hps in
theorem midS_free (body : Program) (hbody : ∀ ab∈ps, ab.1∉wires body) :
    ∀ ab∈ps, ab.1∉wires (midS L ext control src dst body) := by
  intro ab h u
  have t := holes_sub_ktmp L _ (mem_ps L ps hps ab h).1
  have pf := tmp_parkS_free L hw control hn ext src dst hs hd h128 hlen hx hdx he _ t
  have pb := pB_free L hw control hn ext src dst hs hd hx hdx he ps hps body hbody ab h
  simp only [midS,wires_append,Finset.mem_union,or_assoc] at u
  rcases u with u|u|u|u|u|u
  · exact pf.2.1 u
  · exact pf.2.2.1 u
  · exact pf.2.2.2.1 u
  · exact pb u
  · exact pf.2.2.2.2.1 u
  · exact pf.2.2.2.2.2.1 u

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem clearPrefix_free : ∀ ab∈ps, ab.1∉wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst)) :=
  fun ab h => holes_clearPrefix_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he _
    (mem_ps L ps hps ab h).1


/-! #### B leaf -/

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem withLowK2P2_run_eq (body : Program) (hbody : ∀ ab∈ps, ab.1∉wires body)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis) (hzero : regValue dst s.basis=0)
    (hz : regValue ext s.basis=0)
    (fin : ∀ q∈LowZero18LowK.ktmp L, (run (ParkCopy.withLowK2P L ext control src dst body) m s).basis q=false) :
    run (withLowK2P2 ps L ext control src dst body) m s=run (ParkCopy.withLowK2P L ext control src dst body) m s := by
  rw [withLowK2P_shape] at fin
  rw [withLowK2P2_shape,withLowK2P_shape]
  exact leaf_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps _ _
    (midP_free L hw control hn ext src dst hs hd h128 hlen hx hdx he ps hps body hbody)
    (clearPrefix_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps) s m hc hzero hz fin

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem withLowK2P2_avoids (body : Program) (hbody : ∀ ab∈ps, ab.1∉wires body) :
    ∀ q∈holesOf ps, q∉wires (withLowK2P2 ps L ext control src dst body) := by
  rw [withLowK2P2_shape]
  exact leaf_avoids L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps _ _
    (midP_free L hw control hn ext src dst hs hd h128 hlen hx hdx he ps hps body hbody)
    (clearPrefix_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps)

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem withLowK2P2_wires (body : Program) :
    wires (withLowK2P2 ps L ext control src dst body)⊆
      wires (ParkCopy.withLowK2P L ext control src dst body)∪(hostsOf ps).toFinset := by
  rw [withLowK2P2_shape,withLowK2P_shape]
  exact leaf_wires L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps _ _

theorem withLowK2P2_counts (body : Program) :
    toffoliCount (withLowK2P2 ps L ext control src dst body)=toffoliCount (ParkCopy.withLowK2P L ext control src dst body) ∧
    measurementCount (withLowK2P2 ps L ext control src dst body)=
      measurementCount (ParkCopy.withLowK2P L ext control src dst body) ∧
    Challenge.gateSlots (withLowK2P2 ps L ext control src dst body)=
      Challenge.gateSlots (ParkCopy.withLowK2P L ext control src dst body) := by
  rw [withLowK2P2_shape,withLowK2P_shape]
  exact two_block_counts ps _ _ _ _ _

theorem withLowK2P2_physical (body : Program) (h : GatePhysical (ParkCopy.withLowK2P L ext control src dst body)) :
    GatePhysical (withLowK2P2 ps L ext control src dst body) := by
  rw [withLowK2P_shape] at h
  rw [withLowK2P2_shape]
  exact two_block_physical ps _ _ _ _ _ h

/-! #### A leaf -/

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem withLowK2P10'_run_eq (body : Program) (g : Wire) (hg : g∉LowZero18LowK.ktmp L)
    (hbody : ∀ ab∈ps, ab.1∉wires body)
    (s : State) (m : List Bool) (hc : L.PairClean s.basis) (hzero : regValue dst s.basis=0)
    (hz : regValue ext s.basis=0)
    (fin : ∀ q∈LowZero18LowK.ktmp L, (run (ParkCopy10.withLowK2P10 L ext control src dst body g) m s).basis q=false) :
    run (withLowK2P10' ps L ext control src dst body g) m s=
      run (ParkCopy10.withLowK2P10 L ext control src dst body g) m s := by
  rw [withLowK2P10_shape] at fin
  rw [withLowK2P10'_shape,withLowK2P10_shape]
  exact leaf_run_eq L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps _ _
    (mid10_free L hw control hn ext src dst hs hd h128 hlen hx hdx he ps hps body g hg hbody)
    (clearPrefix_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps) s m hc hzero hz fin

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem withLowK2P10'_avoids (body : Program) (g : Wire) (hg : g∉LowZero18LowK.ktmp L)
    (hbody : ∀ ab∈ps, ab.1∉wires body) :
    ∀ q∈holesOf ps, q∉wires (withLowK2P10' ps L ext control src dst body g) := by
  rw [withLowK2P10'_shape]
  exact leaf_avoids L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps _ _
    (mid10_free L hw control hn ext src dst hs hd h128 hlen hx hdx he ps hps body g hg hbody)
    (clearPrefix_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps)

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem withLowK2P10'_wires (body : Program) (g : Wire) :
    wires (withLowK2P10' ps L ext control src dst body g)⊆
      wires (ParkCopy10.withLowK2P10 L ext control src dst body g)∪(hostsOf ps).toFinset := by
  rw [withLowK2P10'_shape,withLowK2P10_shape]
  exact leaf_wires L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps _ _

theorem withLowK2P10'_counts (body : Program) (g : Wire) :
    toffoliCount (withLowK2P10' ps L ext control src dst body g)=
      toffoliCount (ParkCopy10.withLowK2P10 L ext control src dst body g) ∧
    measurementCount (withLowK2P10' ps L ext control src dst body g)=
      measurementCount (ParkCopy10.withLowK2P10 L ext control src dst body g) ∧
    Challenge.gateSlots (withLowK2P10' ps L ext control src dst body g)=
      Challenge.gateSlots (ParkCopy10.withLowK2P10 L ext control src dst body g) := by
  rw [withLowK2P10'_shape,withLowK2P10_shape]
  exact two_block_counts ps _ _ _ _ _

theorem withLowK2P10'_physical (body : Program) (g : Wire)
    (h : GatePhysical (ParkCopy10.withLowK2P10 L ext control src dst body g)) :
    GatePhysical (withLowK2P10' ps L ext control src dst body g) := by
  rw [withLowK2P10_shape] at h
  rw [withLowK2P10'_shape]
  exact two_block_physical ps _ _ _ _ _ h

/-! #### C leaf -/






end Leaf

end ECDSAAdd.Entrant.StairSquareKernel26
end Merge_StairSquareKernel26Branches_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareKernel26Square_at_BOptimizations` -/
section Merge_StairSquareKernel26Square_at_BOptimizations

/-! # LT39 K1–K3: branch-level run equalities for the kernel hosting (A, B, C branches of the record square)

* K1 `branchA_run_eq`  : `run (branchA2 ps L ext c B) = run (A161Low4Branch.branch L ext c B)`
* K2 `branchB_run_eq_of_frame` : `run (branchB2 ps L ext c B) = run (branchB L ext c B)` where
  `branchB L ext c B = ParkCopy.withLowK2P L ext c high (product.take 256) (bodySwap L ext B)`
  (the record's `B95PortResearch.branchBF760 L ext c` is `branchB` with `B := hostedSelectedBody …`, `branchBF760_eq`)
* K3 `branchC_run_eq`  : `run (branchC2 ps L ext c B) = run (SumSavedCBranch.branch L ext c B)`
The only new hypothesis is that the body avoids the hosted holes: `hB : ∀ ab ∈ ps, ab.1 ∉ wires B`.
Each comes with an `_of_frame` form (exit frame as hypothesis) and avoidance / counts / physicality / support. -/

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic

namespace ECDSAAdd.Entrant.StairSquareKernel26
open Arithmetic.CuccaroStreamedSquareWideLayout StairSquareHolesCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- K1 program: the record A branch with the kernel holes hosted. -/
def branchA2 (ps : List (Wire × Wire)) (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (B : Program) : Program :=
  withLowK2P10' ps L ext control L.core.low (L.core.product.take 256) (R2SqEp760.bodySwap L ext B)
    (ControlLoan1589BFFold.eU L)

/-- The record B branch shape, for a general body. -/
def branchB (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire) (B : Program) : Program :=
  ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256) (R2SqEp760.bodySwap L ext B)

/-- K2 program: the record B branch shape with the kernel holes hosted. -/
def branchB2 (ps : List (Wire × Wire)) (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (control : Wire)
    (B : Program) : Program :=
  withLowK2P2 ps L ext control L.core.high (L.core.product.take 256) (R2SqEp760.bodySwap L ext B)



/-! ## layout facts -/

section Facts
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)





include hw in
theorem eU_not_ktmp (nd : L.wires.Nodup) : ControlLoan1589BFFold.eU L∉LowZero18LowK.ktmp L :=
  fun h => InverseCarryDevelop.eU_off_aux L hw nd _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_of_mem_drop h))) rfl

include hw in
theorem ktmp_overflow (q : Wire) (h : q∈LowZero18LowK.ktmp L) : q∈L.overflowPad := by
  have h' : q∈(L.core.pad++L.overflowPad).drop 131 := h
  rw [List.drop_append,List.drop_eq_nil_of_le (by rw [hw.core.pad]; omega),List.nil_append] at h'
  exact List.mem_of_mem_drop h'

include hw in
theorem ktmp_not_core (control : Wire) (hn : (control::L.wires).Nodup) (q : Wire) (h : q∈LowZero18LowK.ktmp L) :
    q∉L.core.wires := by
  have dis := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
  exact fun used => dis q used q (ktmp_overflow L hw q h) rfl

include hw in
theorem ktmp_off_g (control : Wire) (hn : (control::L.wires).Nodup) (q : Wire) (h : q∈LowZero18LowK.ktmp L) :
    q∉wires (OwnDiagAll12Square.gPrep L) ∧ q∉wires (OwnDiagAll12Square.gClear L) := by
  have gs := R2SqEp760.g_core_support L hw
  have off := ktmp_not_core L hw control hn q h
  exact ⟨fun u => off (List.mem_toFinset.mp (gs.1 u)),fun u => off (List.mem_toFinset.mp (gs.2 u))⟩

end Facts

section Branch
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire) (control : Wire)
  (hn : (control::L.wires).Nodup) (he : ECDSAAdd.Entrant.ExtOK L control ext)
  (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L))

/-! ### K1: A branch -/

include hw hn he hps in
theorem branchA_run_eq_of_frame (B : Program) (hB : ∀ ab∈ps, ab.1∉wires B) (s : State) (m : List Bool)
    (hc : L.PairClean s.basis) (hp0 : regValue L.core.product s.basis=0) (hz : regValue ext s.basis=0)
    (frame : ∀ q, q∉L.core.out → (run (A161Low4Branch.branch L ext control B) m s).basis q=s.basis q) :
    run (branchA2 ps L ext control B) m s=run (A161Low4Branch.branch L ext control B) m s := by
  have nd := (List.nodup_cons.mp hn).2
  have hlow := L.core.low_length hw.core
  have tmp0 := tmp_zero L s hc
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  simp only [A161Low4Branch.branch] at frame
  simp only [branchA2,A161Low4Branch.branch]
  apply withLowK2P10'_run_eq L hw control hn ext L.core.low (L.core.product.take 256) (low_count L) (prod_count L)
    (by simp [hlow]) (by simp [hlow]) (by simp [hw.core.product,hlow]) he.nodup he.away he.len ps hps
    _ _ (eU_not_ktmp L hw nd)
    (bodySwap_free L hw control hn ext L.core.low (L.core.product.take 256) (low_count L) (prod_count L)
      he.nodup he.away he.len ps hps B hB) s m hc dstZero hz
  intro q hq
  have notOut : q∉L.core.out := fun ho => tmp_off L control hn ext L.core.low (L.core.product.take 256)
    (low_count L) (prod_count L) he.nodup he.away q hq (out_out L control ext _ _ q ho)
  exact (frame q notOut).trans (tmp0 q hq)

include hw hn he hps in
/-- **K1.** The record A branch and its kernel-hosted version run identically, under the hypotheses of
`A161Low4Branch.swapped_correct` plus "the body avoids the hosted holes". -/
theorem branchA_run_eq (A O : Nat) (hO : O<SquareReduction.p) (s : State) (records : List Bool)
    (ha : regValue L.core.low s.basis=A) (ho : regValue L.core.out s.basis=O)
    (hp0 : regValue L.core.product s.basis=0) (hc : L.PairClean s.basis) (hsum : s.basis L.core.sumCarry=false)
    (hz : regValue ext s.basis=0) (d : Wire) (hdW : d∉control::L.wires) (hdE : d∉ext) (hd0 : s.basis d=false)
    (B : Program) (aSupport : wires B⊆insert d (control::L.wires).toFinset)
    (eUfree : ControlLoan1589BFFold.eU L∉wires B)
    (bodyFrame : ∀ (base : BasisState) (M : Nat), M<2^128 → regValue L.core.product base=M^2 →
      L.PairClean base → base L.core.sumCarry=false → ∀ O, O<SquareReduction.p →
      (base control=false → M=0) → base d=false →
      Triple (SquareFrame L.core.out base O) B
       (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base control))))
    (hB : ∀ ab∈ps, ab.1∉wires B) :
    run (branchA2 ps L ext control B) records s=run (A161Low4Branch.branch L ext control B) records s :=
  branchA_run_eq_of_frame L hw ext control hn he ps hps B hB s records hc hp0 hz
    (A161Low4Branch.swapped_correct L hw ext control hn A O hO s records ha ho hp0 hc hsum he hz d hdW hdE hd0
      B aSupport eUfree bodyFrame).2.2

include hw hn he hps in
theorem branchA_avoids (B : Program) (hB : ∀ ab∈ps, ab.1∉wires B) :
    ∀ q∈holesOf ps, q∉wires (branchA2 ps L ext control B) := by
  have nd := (List.nodup_cons.mp hn).2
  have hlow := L.core.low_length hw.core
  exact withLowK2P10'_avoids L hw control hn ext L.core.low (L.core.product.take 256) (low_count L) (prod_count L)
    (by simp [hlow]) (by simp [hlow]) (by simp [hw.core.product,hlow]) he.nodup he.away he.len ps hps
    _ _ (eU_not_ktmp L hw nd)
    (bodySwap_free L hw control hn ext L.core.low (L.core.product.take 256) (low_count L) (prod_count L)
      he.nodup he.away he.len ps hps B hB)

include hw hn he hps in
theorem branchA_wires (B : Program) :
    wires (branchA2 ps L ext control B)⊆wires (A161Low4Branch.branch L ext control B)∪(hostsOf ps).toFinset := by
  have hlow := L.core.low_length hw.core
  exact withLowK2P10'_wires L hw control hn ext L.core.low (L.core.product.take 256) (low_count L) (prod_count L)
    (by simp [hlow]) (by simp [hlow]) (by simp [hw.core.product,hlow]) he.nodup he.away he.len ps hps _ _

theorem branchA_counts (B : Program) :
    toffoliCount (branchA2 ps L ext control B)=toffoliCount (A161Low4Branch.branch L ext control B) ∧
    measurementCount (branchA2 ps L ext control B)=measurementCount (A161Low4Branch.branch L ext control B) ∧
    Challenge.gateSlots (branchA2 ps L ext control B)=Challenge.gateSlots (A161Low4Branch.branch L ext control B) :=
  withLowK2P10'_counts L control ext L.core.low (L.core.product.take 256) ps _ _

theorem branchA_physical (B : Program) (h : GatePhysical (A161Low4Branch.branch L ext control B)) :
    GatePhysical (branchA2 ps L ext control B) :=
  withLowK2P10'_physical L control ext L.core.low (L.core.product.take 256) ps _ _ h

/-! ### K2: B branch -/

include hw hn he hps in
/-- **K2.** The record B branch shape (`ParkCopy.withLowK2P … (bodySwap L ext B)`) and its kernel-hosted version run
identically, given the branch's exit frame and "the body avoids the hosted holes". -/
theorem branchB_run_eq_of_frame (B : Program) (hB : ∀ ab∈ps, ab.1∉wires B) (s : State) (m : List Bool)
    (hc : L.PairClean s.basis) (hp0 : regValue L.core.product s.basis=0) (hz : regValue ext s.basis=0)
    (frame : ∀ q, q∉L.core.out → (run (branchB L ext control B) m s).basis q=s.basis q) :
    run (branchB2 ps L ext control B) m s=run (branchB L ext control B) m s := by
  have hhigh := L.core.high_length hw.core
  have tmp0 := tmp_zero L s hc
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  simp only [branchB] at frame
  simp only [branchB2,branchB]
  apply withLowK2P2_run_eq L hw control hn ext L.core.high (L.core.product.take 256) (high_count L) (prod_count L)
    (by simp [hhigh]) (by simp [hhigh]) (by simp [hw.core.product,hhigh]) he.nodup he.away he.len ps hps
    _ (bodySwap_free L hw control hn ext L.core.high (L.core.product.take 256) (high_count L) (prod_count L)
      he.nodup he.away he.len ps hps B hB) s m hc dstZero hz
  intro q hq
  have notOut : q∉L.core.out := fun ho => tmp_off L control hn ext L.core.high (L.core.product.take 256)
    (high_count L) (prod_count L) he.nodup he.away q hq (out_out L control ext _ _ q ho)
  exact (frame q notOut).trans (tmp0 q hq)

include hw hn he hps in
theorem branchB_avoids (B : Program) (hB : ∀ ab∈ps, ab.1∉wires B) :
    ∀ q∈holesOf ps, q∉wires (branchB2 ps L ext control B) := by
  have hhigh := L.core.high_length hw.core
  exact withLowK2P2_avoids L hw control hn ext L.core.high (L.core.product.take 256) (high_count L) (prod_count L)
    (by simp [hhigh]) (by simp [hhigh]) (by simp [hw.core.product,hhigh]) he.nodup he.away he.len ps hps
    _ (bodySwap_free L hw control hn ext L.core.high (L.core.product.take 256) (high_count L) (prod_count L)
      he.nodup he.away he.len ps hps B hB)

include hw hn he hps in
theorem branchB_wires (B : Program) :
    wires (branchB2 ps L ext control B)⊆wires (branchB L ext control B)∪(hostsOf ps).toFinset := by
  have hhigh := L.core.high_length hw.core
  exact withLowK2P2_wires L hw control hn ext L.core.high (L.core.product.take 256) (high_count L) (prod_count L)
    (by simp [hhigh]) (by simp [hhigh]) (by simp [hw.core.product,hhigh]) he.nodup he.away he.len ps hps _

theorem branchB_counts (B : Program) :
    toffoliCount (branchB2 ps L ext control B)=toffoliCount (branchB L ext control B) ∧
    measurementCount (branchB2 ps L ext control B)=measurementCount (branchB L ext control B) ∧
    Challenge.gateSlots (branchB2 ps L ext control B)=Challenge.gateSlots (branchB L ext control B) :=
  withLowK2P2_counts L control ext L.core.high (L.core.product.take 256) ps _

theorem branchB_physical (B : Program) (h : GatePhysical (branchB L ext control B)) :
    GatePhysical (branchB2 ps L ext control B) :=
  withLowK2P2_physical L control ext L.core.high (L.core.product.take 256) ps _ h

/-! ### K3: C branch -/







end Branch

end ECDSAAdd.Entrant.StairSquareKernel26
end Merge_StairSquareKernel26Square_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareKernel26Tail_at_BOptimizations` -/
section Merge_StairSquareKernel26Tail_at_BOptimizations

/-! # LT39: the renamed branches also avoid the `ktmp` tail (holes 751..759, 761..764)

The other 13 square holes are `ktmp[99..112]` minus `ktmp[108]` (= pool 760, the record's retired `sqRet`).
No kernel block, park piece, sum preparation or rename touches `ktmp[k]` for `99 ≤ k < 123`, `k ≠ 108`;
so the renamed branches avoid such a wire as soon as the body does. -/

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic

namespace ECDSAAdd.Entrant.StairSquareKernel26
open Arithmetic.CuccaroStreamedSquareWideLayout StairSquareHolesCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- A `ktmp` wire that no kernel block names: outside both sum blocks, the hosts and the two `earlyPerm` sites. -/
structure Quiet (L : CuccaroStreamedSquareWideLayout) (ext src dst : List Wire) (q : Wire) : Prop where
  tmp : q∈LowZero18LowK.ktmp L
  notI : q∉(LowZero18LowK.iregs L ext src dst).S
  notO : q∉(LowZero18LowK.oregs L ext src dst).S
  notH : q∉hosts L
  neT : q≠SquareCarryLoan719.target L
  neE : q≠SquareCarryLoan719.earlyHost L

section Leaf
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (control : Wire)
  (hn : (control::L.wires).Nodup) (ext src dst : List Wire)
  (hs : ∀q,src.count q≤(L.core.y++[L.core.sumCarry]).count q)
  (hd : ∀q,dst.count q≤L.core.product.count q)
  (h128 : 128≤src.length) (hsmax : src.length≤129) (hlen : dst.length=2*src.length)
  (hx : ext.Nodup) (hdx : ∀q∈ext,q∉control::L.wires) (he : 300≤ext.length)
  (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L))

include hw hn hs hd hx hdx in
theorem quiet_of_tail (k : Nat) (hk1 : 99≤k) (hk2 : k<123) :
    Quiet L ext src dst ((LowZero18LowK.ktmp L).getD k 0) := by
  have nd := ktmp_nodup L control hn ext src dst hs hd hx hdx
  have len := LowZero18LowK.ktmp_length L hw
  have kl : k<(LowZero18LowK.ktmp L).length := by omega
  refine ⟨DiagSq.getD_in _ k kl,?_,?_,?_,?_,?_⟩
  · intro u
    obtain ⟨j,jl,a,b,e⟩ := slice_index (LowZero18LowK.ktmp L) 66 33 _ u
    have := getD_index_inj _ nd j k jl kl e
    omega
  · intro u
    have u' : (LowZero18LowK.ktmp L).getD k 0∈((LowZero18LowK.ktmp L).take 66).take (src.length-63) := u
    obtain ⟨j,jl,a,b,e⟩ := slice_index (LowZero18LowK.ktmp L) 0 66 _
      (take_as_slice _ _ _ (List.mem_of_mem_take u'))
    have := getD_index_inj _ nd j k jl kl e
    omega
  · intro u
    obtain ⟨j,jl,a,b,e⟩ := hosts_index L _ u
    have := getD_index_inj _ nd j k jl kl e
    omega
  · intro e
    change (LowZero18LowK.ktmp L).getD k 0=(LowZero18LowK.ktmp L).getD 67 0 at e
    have := getD_index_inj _ nd k 67 kl (by omega) e
    omega
  · intro e
    change (LowZero18LowK.ktmp L).getD k 0=(LowZero18LowK.ktmp L).getD 1 0 at e
    have := getD_index_inj _ nd k 1 kl (by omega) e
    omega


include hn hs hd hx hdx in
theorem quiet_not_out (q : Wire) (hq : Quiet L ext src dst q) : q∉outside L ext control src dst :=
  tmp_off L control hn ext src dst hs hd hx hdx q hq.tmp

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem quiet_Q1_free (q : Wire) (hq : Quiet L ext src dst q) :
    q∉wires (Q1r L ext src dst) ∧ q∉wires (Q1cr L ext src dst) := by
  have sup := kg_Q1_support L hw ext src dst h128 hsmax hlen he
  have fix : SquareCarryLoan719.earlyPerm L q=q := by
    rw [SquareCarryLoan719.earlyPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne hq.neT hq.neE
  have off : q∉(LowZero18LowK.iregs L ext src dst).all.toFinset := by
    intro used
    rcases iregs_all_sub L control ext src dst q (List.mem_toFinset.mp used) with h|h
    · exact quiet_not_out L control hn ext src dst hs hd hx hdx q hq h
    · exact hq.notI h
  exact ⟨rename_fix_free _ _ _ fix (fun u => off (sup.1 u)),rename_fix_free _ _ _ fix (fun u => off (sup.2 u))⟩

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem quiet_hostRename_free (q : Wire) (hq : Quiet L ext src dst q) :
    q∉wires (hostRename ps (Q1r L ext src dst)) ∧ q∉wires (hostRename ps (Q1cr L ext src dst)) := by
  have mem := mem_ps L ps hps
  have hnd := ps_nodup L hw ps hps (holes_hosts_nodup L hw control hn ext src dst hs hd hx hdx)
  have hq1 := hosts_Q1_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he
  have fix := early_fix L hw control hn ext src dst hs hd hx hdx
  have h1 : ∀ ab∈ps, ab.2∉wires (Q1r L ext src dst) :=
    fun ab h => rename_fix_free _ _ _ (fix _ (Or.inr (mem ab h).2)) (hq1 _ (mem ab h).2).1
  have h2 : ∀ ab∈ps, ab.2∉wires (Q1cr L ext src dst) :=
    fun ab h => rename_fix_free _ _ _ (fix _ (Or.inr (mem ab h).2)) (hq1 _ (mem ab h).2).2
  have notHost : q∉(hostsOf ps).toFinset := by
    intro u
    obtain ⟨ab,h,e⟩ := List.mem_map.mp (List.mem_toFinset.mp u)
    exact hq.notH (e ▸ (mem ab h).2)
  have qf := quiet_Q1_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he q hq
  constructor
  · intro u
    rcases Finset.mem_union.mp (hostRename_support ps _ hnd h1 u) with h|h
    · exact qf.1 (Finset.mem_sdiff.mp h).1
    · exact notHost h
  · intro u
    rcases Finset.mem_union.mp (hostRename_support ps _ hnd h2 u) with h|h
    · exact qf.2 (Finset.mem_sdiff.mp h).1
    · exact notHost h

include hn hs hd hx hdx in
theorem quiet_not_outerSet (q : Wire) (hq : Quiet L ext src dst q) : q∉outerSet L control ext src dst := by
  intro used
  rcases List.mem_append.mp (List.mem_toFinset.mp used) with h|h
  · exact quiet_not_out L control hn ext src dst hs hd hx hdx q hq h
  · exact hq.notO h

include hw hn hs hd h128 hsmax hlen hx hdx he in
theorem quiet_rest_free (q : Wire) (hq : Quiet L ext src dst q) :
    q∉wires (tail (LowZero18LowK.kg L ext src dst)) ∧
      q∉wires (LowZero18Square.clearPrefix (LowZero18LowK.kg L ext src dst)) := by
  have r := kg_rest_support L hw control ext src dst h128 hsmax hlen he
  have off := quiet_not_outerSet L control hn ext src dst hs hd hx hdx q hq
  exact ⟨fun u => off (r.1 u),fun u => off (r.2 u)⟩


include hw hn hs hd hx hdx he in
theorem quiet_fold_free (q : Wire) (hq : Quiet L ext src dst q) (body : Program) (hbody : q∉wires body) :
    q∉wires (renameProgram (SquareCarryLoan719.foldPerm L ext) body) := by
  have offE : q∉ext := fun h => quiet_not_out L control hn ext src dst hs hd hx hdx q hq
    (out_ext L control ext src dst q h)
  have fix : SquareCarryLoan719.foldPerm L ext q=q := by
    rw [SquareCarryLoan719.foldPerm_eq L hw]
    exact Equiv.swap_apply_of_ne_of_ne hq.neT (fun e => offE (e ▸ DiagSq.getD_in ext 0 (by omega)))
  exact rename_fix_free _ _ _ fix hbody

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
/-- Leaf-level: a quiet wire avoided by the material between the kernel blocks and by the clear prefix is
avoided by the whole renamed leaf. -/
theorem leaf_quiet (Mid0 C0 : Program) (q : Wire) (hq : Quiet L ext src dst q)
    (hMid : q∉wires Mid0) (hC : q∉wires C0) :
    q∉wires (pA0 L control src++hostRename ps (Q1r L ext src dst)++
      (tail (LowZero18LowK.kg L ext src dst)++Mid0++C0)++hostRename ps (Q1cr L ext src dst)++pE0 L control src) := by
  have hr := quiet_hostRename_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps q hq
  have rest := quiet_rest_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he q hq
  intro u
  simp only [wires_append,Finset.mem_union,or_assoc] at u
  rcases u with u|u|u|u|u|u|u
  · exact pA0_free L control hn ext src dst hs hd hx hdx q hq.tmp u
  · exact hr.1 u
  · exact rest.1 u
  · exact hMid u
  · exact hC u
  · exact hr.2 u
  · exact pE0_free L control hn ext src dst hs hd hx hdx q hq.tmp u

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem withLowK2P2_quiet (body : Program) (q : Wire) (hq : Quiet L ext src dst q) (hbody : q∉wires body) :
    q∉wires (withLowK2P2 ps L ext control src dst body) := by
  have pf := tmp_park_free L hw control hn ext src dst hs hd h128 hlen hx hdx he q hq.tmp
  have pb := quiet_fold_free L hw control hn ext src dst hs hd hx hdx he q hq body hbody
  have mid : q∉wires (midP L ext control src dst body) := by
    intro u
    simp only [midP,wires_append,Finset.mem_union,or_assoc] at u
    rcases u with u|u|u|u|u|u
    · exact pf.2.1 u
    · exact pf.2.2.1 u
    · exact pf.2.2.2.1 u
    · exact pb u
    · exact pf.2.2.2.2.1 u
    · exact pf.2.2.2.2.2.1 u
  rw [withLowK2P2_shape]
  exact leaf_quiet L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps _ _ q hq mid
    (quiet_rest_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he q hq).2

include hw hn hs hd h128 hsmax hlen hx hdx he hps in
theorem withLowK2P10'_quiet (body : Program) (g : Wire) (hg : g∉LowZero18LowK.ktmp L) (q : Wire)
    (hq : Quiet L ext src dst q) (hbody : q∉wires body) :
    q∉wires (withLowK2P10' ps L ext control src dst body g) := by
  have pf := tmp_park10_free L hw control hn ext src dst hs hd h128 hlen hx hdx he g hg q hq.tmp
  have pb := quiet_fold_free L hw control hn ext src dst hs hd hx hdx he q hq body hbody
  have mid : q∉wires (mid10 L ext control src dst body g) := by
    intro u
    simp only [mid10,wires_append,Finset.mem_union,or_assoc] at u
    rcases u with u|u|u|u|u|u
    · exact pf.2.1 u
    · exact pf.2.2.1 u
    · exact pf.2.2.2.1 u
    · exact pb u
    · exact pf.2.2.2.2.1 u
    · exact pf.2.2.2.2.2.1 u
  rw [withLowK2P10'_shape]
  exact leaf_quiet L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he ps hps _ _ q hq mid
    (quiet_rest_free L hw control hn ext src dst hs hd h128 hsmax hlen hx hdx he q hq).2


end Leaf

/-! ## branch level: tail wires `ktmp[k]`, `99 ≤ k < 123`, `k ≠ 108` -/

theorem ktmp_nodup' (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (nd : L.wires.Nodup) :
    (LowZero18LowK.ktmp L).Nodup := by
  have e : LowZero18LowK.ktmp L=L.overflowPad.drop (131-L.core.pad.length) := by
    change (L.core.pad++L.overflowPad).drop 131=_
    rw [List.drop_append,List.drop_eq_nil_of_le (by rw [hw.core.pad]; omega),List.nil_append]
  rw [e]
  exact ((List.nodup_append.mp nd).2.1).sublist (List.drop_sublist _ _)

section Branch
variable (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (ext : List Wire) (control : Wire)
  (hn : (control::L.wires).Nodup) (he : ECDSAAdd.Entrant.ExtOK L control ext)
  (ps : List (Wire × Wire)) (hps : List.Sublist ps (pairs L))

include hw hn he in
theorem tail_bodySwap_free (k : Nat) (hk2 : k<123) (hk3 : k≠108) (B : Program)
    (hB : (LowZero18LowK.ktmp L).getD k 0∉wires B) :
    (LowZero18LowK.ktmp L).getD k 0∉wires (R2SqEp760.bodySwap L ext B) := by
  have len := LowZero18LowK.ktmp_length L hw
  have nd := (List.nodup_cons.mp hn).2
  have inT : (LowZero18LowK.ktmp L).getD k 0∈LowZero18LowK.ktmp L := DiagSq.getD_in _ k (by omega)
  have offE : (LowZero18LowK.ktmp L).getD k 0∉ext := fun h =>
    he.away _ h (List.mem_cons_of_mem _ (LowZero18LowK.ktmp_wires L _ inT))
  apply rename_fix_free _ _ _ _ hB
  unfold R2SqEp760.sqSwap
  apply Equiv.swap_apply_of_ne_of_ne
  · intro e
    rw [R2SqEp760.sqRet_ktmp L] at e
    have tnd := ktmp_nodup' L hw nd
    have := getD_index_inj _ tnd k 108 (by omega) (by omega) e
    omega
  · exact fun e => offE (e ▸ DiagSq.getD_in ext 130 (by have := he.len; omega))

include hw hn he hps in
theorem branchA_tail (k : Nat) (hk1 : 99≤k) (hk2 : k<123) (hk3 : k≠108) (B : Program)
    (hB : (LowZero18LowK.ktmp L).getD k 0∉wires B) :
    (LowZero18LowK.ktmp L).getD k 0∉wires (branchA2 ps L ext control B) := by
  have nd := (List.nodup_cons.mp hn).2
  have hlow := L.core.low_length hw.core
  exact withLowK2P10'_quiet L hw control hn ext L.core.low (L.core.product.take 256) (low_count L) (prod_count L)
    (by simp [hlow]) (by simp [hlow]) (by simp [hw.core.product,hlow]) he.nodup he.away he.len ps hps
    _ _ (eU_not_ktmp L hw nd) _
    (quiet_of_tail L hw control hn ext L.core.low (L.core.product.take 256) (low_count L) (prod_count L)
      he.nodup he.away k hk1 hk2)
    (tail_bodySwap_free L hw ext control hn he k hk2 hk3 B hB)

include hw hn he hps in
theorem branchB_tail (k : Nat) (hk1 : 99≤k) (hk2 : k<123) (hk3 : k≠108) (B : Program)
    (hB : (LowZero18LowK.ktmp L).getD k 0∉wires B) :
    (LowZero18LowK.ktmp L).getD k 0∉wires (branchB2 ps L ext control B) := by
  have hhigh := L.core.high_length hw.core
  exact withLowK2P2_quiet L hw control hn ext L.core.high (L.core.product.take 256) (high_count L) (prod_count L)
    (by simp [hhigh]) (by simp [hhigh]) (by simp [hw.core.product,hhigh]) he.nodup he.away he.len ps hps
    _ _
    (quiet_of_tail L hw control hn ext L.core.high (L.core.product.take 256) (high_count L) (prod_count L)
      he.nodup he.away k hk1 hk2)
    (tail_bodySwap_free L hw ext control hn he k hk2 hk3 B hB)


end Branch

end ECDSAAdd.Entrant.StairSquareKernel26
end Merge_StairSquareKernel26Tail_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareKernel26Contract_at_BOptimizations` -/
section Merge_StairSquareKernel26Contract_at_BOptimizations

/-! # LT39 → LT40 (U6): K1–K3 in the shapes of `StairSquareContract`

For a hole list `hs ⊆ holes39`, `psOf hs` are the kernel pairs (hole `ktmp[73..98]` = pool 725..750 ↦ host
`ktmp[2..27]` = pool 654..679) whose hole is in `hs`. The new branches `newBrC/newBrB/newBrA hs body` are the record
branch wrappers `recBrC/recBrB/recBrA body` with the kernel blocks `Q1`, `Q1c` renamed by `psOf hs`.

* `kC_run_eq`, `kA_run_eq` — exactly the contract shape (`BodyXOK body`, body avoids `hs`, `BranchPre t`).
* `kB_run_eq_of_frame` — the B branch needs the exit frame of `recBrB body` (the generic-body B correctness is U6's;
  the frame is its third component).
* `kX_avoids` — every member of `hs` (kernel holes AND the ktmp-tail holes 751..759, 761..764) is avoided.
* `kX_counts` (T, M and gate slots equal), `kX_physical`, `kX_support` (⊆ record wrapper ∪ `hostsK`). -/

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic

namespace ECDSAAdd.Entrant.StairSquareKernel26C
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout StairSquareHolesCore StairSquareKernel26
  StairSquareContract

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires Baselines.layout

/-! ## generic facts (variable layout), instantiated below for the square -/





theorem ktmp_getD_of (L : ControlledPointLayout) (hw : L.Widths) (j : Nat) (hj : j<123) :
    (LowZero18LowK.ktmp L.dialogStreamedSquareWide).getD j 0=L.core.poolWire (652+j) := by
  change (OwnDiagLowK.ktmp L.dialogStreamedSquareWide).getD j 0=L.core.poolWire (652+j)
  rw [SquareCarryLoan719Inventory.ktmp_layout L hw,List.getD_eq_getElem _ _ (by
    simp only [List.length_take,List.length_drop,L.dialogPool_length hw]
    omega)]
  simp only [List.getElem_take,List.getElem_drop]
  have bound : 652+j<L.dialogPool.length := by rw [L.dialogPool_length hw];omega
  have same := pool_getD_of L hw (652+j) (by omega)
  rw [List.getD_eq_getElem L.dialogPool 0 bound] at same
  exact same

theorem holes_pool_of (L : ControlledPointLayout) (hw : L.Widths) (n : Nat) (h1 : 720 ≤ n) (h2 : n < 751) :
    L.core.poolWire n∈holes L.dialogStreamedSquareWide := by
  have len := LowZero18LowK.ktmp_length L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
  have e : L.core.poolWire n=(LowZero18LowK.ktmp L.dialogStreamedSquareWide).getD (n-652) 0 := by
    rw [ktmp_getD_of L hw (n-652) (by omega)]
    congr 1
    omega
  rw [e]
  exact slice_mem _ 68 31 (n-652) (by omega) (by omega) (by omega)

theorem holes39_cases_of (L : ControlledPointLayout) (hw : L.Widths) (q : Wire)
    (hq : q∈(List.range' 725 35++List.range' 761 4).map L.core.poolWire) :
    q∈holes L.dialogStreamedSquareWide ∨
      ∃ k, 99 ≤ k ∧ k < 123 ∧ k ≠ 108 ∧ q=(LowZero18LowK.ktmp L.dialogStreamedSquareWide).getD k 0 := by
  obtain ⟨n,hi,rfl⟩ := List.mem_map.mp hq
  simp only [List.mem_append,List.mem_range'_1] at hi
  by_cases c : n < 751
  · exact Or.inl (holes_pool_of L hw n (by omega) c)
  · refine Or.inr ⟨n-652,by omega,by omega,by omega,?_⟩
    rw [ktmp_getD_of L hw (n-652) (by omega)]
    congr 1
    omega

theorem hosts_pool_of (L : ControlledPointLayout) (hw : L.Widths) :
    ∀ q∈hosts L.dialogStreamedSquareWide, ∃ n, 654 ≤ n ∧ n < 685 ∧ q=L.core.poolWire n := by
  intro q hq
  have len := LowZero18LowK.ktmp_length L.dialogStreamedSquareWide (L.dialogStreamedSquareWide_widths hw)
  obtain ⟨k,kl,a,b,e⟩ := hosts_index L.dialogStreamedSquareWide q hq
  refine ⟨652+k,by omega,by omega,?_⟩
  rw [← e,ktmp_getD_of L hw k (by omega)]

/-! ## the square instance -/





/-- Every hole site is a kernel hole (`ktmp[73..98]`) or a quiet tail wire (`ktmp[99..112]`, not 108). -/
theorem holes39_cases (q : Wire) (hq : q∈holes39) :
    q∈holes K0 ∨ ∃ k, 99 ≤ k ∧ k < 123 ∧ k ≠ 108 ∧ q=(LowZero18LowK.ktmp K0).getD k 0 :=
  holes39_cases_of L0 hw0 q hq

/-- Hosted pairs for a hole list: the kernel pairs whose hole is in `hs`. -/
def psOf (hs : List Wire) : List (Wire × Wire) := (pairs K0).filter (fun ab => decide (ab.1∈hs))

/-- The explicit host list (pool 654..679). -/
def hostsK : List Wire := hosts K0

theorem psOf_sub (hs : List Wire) : List.Sublist (psOf hs) (pairs K0) := by
  apply List.filter_sublist

theorem psOf_mem (hs : List Wire) (ab : Wire × Wire) (h : ab∈psOf hs) : ab.1∈hs := by
  simpa using (List.mem_filter.mp h).2

theorem psOf_holes (hs : List Wire) (q : Wire) (hq : q∈hs) (hk : q∈holes K0) : q∈holesOf (psOf hs) := by
  have m : q∈holesOf (pairs K0) := by rw [holesOf_pairs K0 hwK]; exact hk
  obtain ⟨ab,h,e⟩ := List.mem_map.mp m
  exact List.mem_map.mpr ⟨ab,List.mem_filter.mpr ⟨h,by simp [e,hq]⟩,e⟩

theorem psOf_hosts (hs : List Wire) : ∀ q∈(hostsOf (psOf hs)).toFinset, q∈hostsK.toFinset := by
  intro q u
  obtain ⟨ab,h,e⟩ := List.mem_map.mp (List.mem_toFinset.mp u)
  exact List.mem_toFinset.mpr (e ▸ (mem_ps K0 (psOf hs) (psOf_sub hs) ab h).2)

def newBrB (hs : List Wire) (B : Program) : Program := branchB2 (psOf hs) K0 E0 G0 B
def newBrA (hs : List Wire) (A : Program) : Program := branchA2 (psOf hs) K0 E0 G0 A

theorem recBrB_eq (B : Program) : recBrB B=branchB K0 E0 G0 B := rfl
theorem recBrA_eq (A : Program) : recBrA A=A161Low4Branch.branch K0 E0 G0 A := rfl
theorem newBrB_eq (hs : List Wire) (B : Program) : newBrB hs B=branchB2 (psOf hs) K0 E0 G0 B := rfl
theorem newBrA_eq (hs : List Wire) (A : Program) : newBrA hs A=branchA2 (psOf hs) K0 E0 G0 A := rfl

/-! ## run equalities (proofs first rewrite to the generic programs, so all unification is syntactic) -/


theorem kA_run_eq (hs : List Wire) (hsub : ∀ q∈hs, q∈holes39) (body : Program) (hb : BodyAOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t) :
    run (newBrA hs body) m t=run (recBrA body) m t := by
  have p := B3CarryPort.pool1540_facts L0 hw0 hn0
  rw [newBrA_eq,recBrA_eq]
  exact branchA_run_eq K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs)
    (regValue K0.core.low t.basis) (regValue K0.core.out t.basis) pre.outLt t m
    rfl rfl pre.prod0 pre.clean pre.sum0 pre.ext0 D0 p.1 p.2.1 pre.d0 body hb.support hb.eUfree hb.frame
    (fun ab h => hav _ (psOf_mem hs ab h))

/-- B branch: needs the exit frame of the record wrapper (third component of the generic-body B correctness). -/
theorem kB_run_eq_of_frame (hs : List Wire) (hsub : ∀ q∈hs, q∈holes39) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t)
    (frame : ∀ q, q∉K0.core.out → (run (recBrB body) m t).basis q=t.basis q) :
    run (newBrB hs body) m t=run (recBrB body) m t := by
  rw [newBrB_eq,recBrB_eq]
  rw [recBrB_eq] at frame
  exact branchB_run_eq_of_frame K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
    (fun ab h => hav _ (psOf_mem hs ab h)) t m pre.clean pre.prod0 pre.ext0 frame

/-! ## avoidance (all of `hs`, kernel holes and tail holes) -/


theorem kB_avoids (hs : List Wire) (hsub : ∀ q∈hs, q∈holes39) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) : ∀ q∈hs, q∉wires (newBrB hs body) := by
  rw [newBrB_eq]
  intro q hq
  rcases holes39_cases q (hsub q hq) with hk|⟨k,k1,k2,k3,rfl⟩
  · exact branchB_avoids K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
      (fun ab h => hav _ (psOf_mem hs ab h)) q (psOf_holes hs q hq hk)
  · exact branchB_tail K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) k k1 k2 k3 body (hav _ hq)

theorem kA_avoids (hs : List Wire) (hsub : ∀ q∈hs, q∈holes39) (body : Program) (hb : BodyAOK body)
    (hav : ∀ q∈hs, q∉wires body) : ∀ q∈hs, q∉wires (newBrA hs body) := by
  rw [newBrA_eq]
  intro q hq
  rcases holes39_cases q (hsub q hq) with hk|⟨k,k1,k2,k3,rfl⟩
  · exact branchA_avoids K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
      (fun ab h => hav _ (psOf_mem hs ab h)) q (psOf_holes hs q hq hk)
  · exact branchA_tail K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) k k1 k2 k3 body (hav _ hq)

/-! ## counts, physicality, support -/


theorem kB_counts (hs : List Wire) (body : Program) :
    toffoliCount (newBrB hs body)=toffoliCount (recBrB body) ∧
    measurementCount (newBrB hs body)=measurementCount (recBrB body) ∧
    Challenge.gateSlots (newBrB hs body)=Challenge.gateSlots (recBrB body) := by
  rw [newBrB_eq,recBrB_eq]
  exact branchB_counts K0 E0 G0 (psOf hs) body

theorem kA_counts (hs : List Wire) (body : Program) :
    toffoliCount (newBrA hs body)=toffoliCount (recBrA body) ∧
    measurementCount (newBrA hs body)=measurementCount (recBrA body) ∧
    Challenge.gateSlots (newBrA hs body)=Challenge.gateSlots (recBrA body) := by
  rw [newBrA_eq,recBrA_eq]
  exact branchA_counts K0 E0 G0 (psOf hs) body


theorem kB_physical (hs : List Wire) (body : Program) (h : GatePhysical (recBrB body)) :
    GatePhysical (newBrB hs body) := by
  rw [recBrB_eq] at h
  rw [newBrB_eq]
  exact branchB_physical K0 E0 G0 (psOf hs) body h

theorem kA_physical (hs : List Wire) (body : Program) (h : GatePhysical (recBrA body)) :
    GatePhysical (newBrA hs body) := by
  rw [recBrA_eq] at h
  rw [newBrA_eq]
  exact branchA_physical K0 E0 G0 (psOf hs) body h


theorem kB_support (hs : List Wire) (body : Program) :
    wires (newBrB hs body)⊆wires (recBrB body)∪hostsK.toFinset := by
  rw [newBrB_eq,recBrB_eq]
  have w := branchB_wires K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
  intro q u
  rcases Finset.mem_union.mp (w u) with h|h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (psOf_hosts hs q h)

theorem kA_support (hs : List Wire) (body : Program) :
    wires (newBrA hs body)⊆wires (recBrA body)∪hostsK.toFinset := by
  rw [newBrA_eq,recBrA_eq]
  have w := branchA_wires K0 hwK E0 G0 controlND extOK0 (psOf hs) (psOf_sub hs) body
  intro q u
  rcases Finset.mem_union.mp (w u) with h|h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (psOf_hosts hs q h)

/-- The hosts are pool 654..679. -/
theorem hostsK_pool : ∀ q∈hostsK, ∃ n, 654 ≤ n ∧ n < 685 ∧ q=L0.core.poolWire n := hosts_pool_of L0 hw0

end ECDSAAdd.Entrant.StairSquareKernel26C
end Merge_StairSquareKernel26Contract_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareKernel26BCorrect_at_BOptimizations` -/
section Merge_StairSquareKernel26BCorrect_at_BOptimizations

/-! # LT39: correctness of the record B-branch wrapper for a generic body, and K2 in the contract shape

`branchBG_unswapped_correct` is the record's `B95PortResearch.branchBFP3_correct` with the selected body replaced by
any body `B` with the support and frame of `B95SelectorResearch.selected_support` / `selected_frame` (= LT40's
`BodyBOK`). `branchBG_correct` adds the record's 760 swap (`R2SqEp760.withLowK2P_swap_run_eq`), i.e. it is the
correctness of `branchB L ext c B = ParkCopy.withLowK2P … (bodySwap L ext B)`. Its frame closes K2 without an exit-frame
hypothesis: `StairSquareKernel26C.kB_run_eq` (exact contract shape). -/

open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic

namespace ECDSAAdd.Entrant.StairSquareKernel26
open Arithmetic.CuccaroStreamedSquareWideLayout StairSquareHolesCore

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

/-- The record B leaf (no 760 swap) for a generic body with the selected-body support and frame. -/
theorem branchBG_unswapped_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Bv O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=Bv)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum : s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0)
    (B : Program) (support : wires B⊆(control::L.wires).toFinset)
    (frame : ∀ (base : BasisState) (M : Nat), M<2^128 → regValue L.core.product base=M^2 →
      L.PairClean base → base L.core.sumCarry=false → ∀ O, O<SquareReduction.p →
      (base control=false → M=0) → (M=if base control then regValue L.core.high base else 0) →
      Triple (SquareFrame L.core.out base O) B
        (SquareFrame L.core.out base (ControlLoan1589BFFold.bO4 (M^2) (base control) O))) :
    (run (ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256) B) records s).phase=s.phase ∧
    regValue L.core.out (run (ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256) B) records s).basis=
      ControlLoan1589BFFold.resBF ((if s.basis control then Bv else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out →
      (run (ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256) B) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have hcw : control∉L.wires := (List.nodup_cons.mp hn).1
  let M := if s.basis control then Bv else 0
  have bb : Bv<2^128 := by simpa [L.core.high_length hw.core,hb] using regValue_lt L.core.high s.basis
  have mb : M<2^128 := by cases h : s.basis control <;> simp [M,h]; omega
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have hbody : ∀q∈ext,q∉ECDSAAdd.wires B := fun q hq hw' =>
    he.away q hq (List.mem_toFinset.mp (support hw'))
  apply ParkCopy.withLowK2P_correct L hw control hn L.core.high (L.core.product.take 256) (high_count L) (prod_count L)
    (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) (L.core.high_length hw.core) ext he.nodup he.away he.len
    B hbody s records hc dstZero hz
  intro t m dstValue same
  rw [hb] at dstValue
  change regValue (L.core.product.take 256) t.basis=M^2 at dstValue
  have full : regValue L.core.product t.basis=M^2 :=
    L.measured_partial_product_value nd s.basis t.basis hp0 (M^2) dstValue same
  have clean := L.measured_product_frame_clean nd (L.core.product.take 256) (prod_count L) s.basis t.basis hc same
  have outAway (q : Wire) (hq : q∈L.core.out) : q∉L.core.product.take 256 := by
    intro bad
    exact List.disjoint_left.mp (L.product_out_disjoint nd) (List.mem_of_mem_take bad) hq
  have outO : regValue L.core.out t.basis=O :=
    (regValue_congr _ _ _ (fun q hq => same q (outAway q hq))).trans ho
  have ctrlProd : control∉L.core.product.take 256 := fun h => hcw (by
    simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,List.mem_of_mem_take h])
  have ctrlT : t.basis control=s.basis control := same control ctrlProd
  have hg : t.basis control=false → M=0 := by
    intro h; rw [ctrlT] at h; simp [M,h]
  have sumProd : L.core.sumCarry∉L.core.product.take 256 := by
    intro h
    apply ParkCarryDevelop.sumCarry_away L nd
    simp [ParkCarryDevelop.restWires,List.mem_of_mem_take h]
  have hsumT : t.basis L.core.sumCarry=false := (same _ sumProd).trans hsum
  have sourceT : regValue L.core.high t.basis=Bv := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hb
    intro q hq
    apply same q
    intro bad
    have vy : q∈L.core.y := List.mem_of_mem_drop (List.mem_of_mem_take hq)
    have yp := List.count_pos_iff.mpr vy
    have pp := List.count_pos_iff.mpr (List.mem_of_mem_take bad)
    have lc := ControlLoan1589BFFold.layoutCount L nd q
    omega
  have hSource : M=if t.basis control then regValue L.core.high t.basis else 0 := by
    rw [sourceT,ctrlT]
  have fr := frame t.basis M mb full clean hsumT O hO hg hSource t m ⟨outO,fun _ _ => rfl⟩
  rw [ControlLoan1589BFFold.bO4_eq M O (t.basis control) mb hg hO,ctrlT] at fr
  exact ⟨fr.1,fr.2.1,fr.2.2⟩

/-- Correctness of the record B-branch wrapper `branchB L ext c B` (with the 760 body swap) for a generic body. -/
theorem branchBG_correct (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
    (ext : List Wire) (control : Wire) (hn : (control::L.wires).Nodup) (Bv O : Nat) (hO : O<SquareReduction.p)
    (s : State) (records : List Bool) (hb : regValue L.core.high s.basis=Bv)
    (ho : regValue L.core.out s.basis=O) (hp0 : regValue L.core.product s.basis=0)
    (hc : L.PairClean s.basis) (hsum : s.basis L.core.sumCarry=false)
    (he : ECDSAAdd.Entrant.ExtOK L control ext) (hz : regValue ext s.basis=0)
    (B : Program) (support : wires B⊆(control::L.wires).toFinset)
    (frame : ∀ (base : BasisState) (M : Nat), M<2^128 → regValue L.core.product base=M^2 →
      L.PairClean base → base L.core.sumCarry=false → ∀ O, O<SquareReduction.p →
      (base control=false → M=0) → (M=if base control then regValue L.core.high base else 0) →
      Triple (SquareFrame L.core.out base O) B
        (SquareFrame L.core.out base (ControlLoan1589BFFold.bO4 (M^2) (base control) O))) :
    (run (branchB L ext control B) records s).phase=s.phase ∧
    regValue L.core.out (run (branchB L ext control B) records s).basis=
      ControlLoan1589BFFold.resBF ((if s.basis control then Bv else 0)^2) O (s.basis control) ∧
    ∀q,q∉L.core.out → (run (branchB L ext control B) records s).basis q=s.basis q := by
  have nd := (List.nodup_cons.mp hn).2
  have newC := branchBG_unswapped_correct L hw ext control hn Bv O hO s records hb ho hp0 hc hsum he hz B support frame
  have fin := newC.2.2 (R2SqEp760.sqRet L) (R2SqEp760.sqRet_not_out L hw nd)
  rw [R2SqEp760.sqRet_clean L hw _ hc] at fin
  have dstZero : regValue (L.core.product.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun q hq => (regValue_zero _ _).mp hp0 q (List.mem_of_mem_take hq))
  have eq := R2SqEp760.withLowK2P_swap_run_eq L hw control hn L.core.high (L.core.product.take 256)
    (high_count L) (prod_count L) (by simp [L.core.high_length hw.core]) (by simp [L.core.high_length hw.core])
    (by simp [hw.core.product,L.core.high_length hw.core]) ext he.nodup he.away he.len B support s records hc dstZero hz fin
  rw [show branchB L ext control B=ParkCopy.withLowK2P L ext control L.core.high (L.core.product.take 256)
    (R2SqEp760.bodySwap L ext B) from rfl,eq]
  exact newC

end ECDSAAdd.Entrant.StairSquareKernel26

namespace ECDSAAdd.Entrant.StairSquareKernel26C
open Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout StairSquareHolesCore StairSquareKernel26
  StairSquareContract

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires Baselines.layout

/-- Correctness of the record B wrapper for any `BodyBOK` body, at every branch boundary. -/
theorem recBrB_correct (body : Program) (hb : BodyBOK body) (t : State) (m : List Bool) (pre : BranchPre t) :
    (run (recBrB body) m t).phase=t.phase ∧
    regValue K0.core.out (run (recBrB body) m t).basis=
      ControlLoan1589BFFold.resBF ((if t.basis G0 then regValue K0.core.high t.basis else 0)^2)
        (regValue K0.core.out t.basis) (t.basis G0) ∧
    ∀q,q∉K0.core.out → (run (recBrB body) m t).basis q=t.basis q := by
  rw [recBrB_eq]
  exact branchBG_correct K0 hwK E0 G0 controlND (regValue K0.core.high t.basis) (regValue K0.core.out t.basis)
    pre.outLt t m rfl rfl pre.prod0 pre.clean pre.sum0 extOK0 pre.ext0 body hb.support hb.frame

/-- **K2 in the contract shape** (no exit-frame hypothesis). -/
theorem kB_run_eq (hs : List Wire) (hsub : ∀ q∈hs, q∈holes39) (body : Program) (hb : BodyBOK body)
    (hav : ∀ q∈hs, q∉wires body) (t : State) (m : List Bool) (pre : BranchPre t) :
    run (newBrB hs body) m t=run (recBrB body) m t :=
  kB_run_eq_of_frame hs hsub body hb hav t m pre (recBrB_correct body hb t m pre).2.2

end ECDSAAdd.Entrant.StairSquareKernel26C
end Merge_StairSquareKernel26BCorrect_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareFinal_at_BOptimizations` -/
section Merge_StairSquareFinal_at_BOptimizations

/-! # LT40 U6: the hole-free square (drop-in for `A161Generic.squareEntry`)

For every sublist `hl` of the 39 holes (`hl.Sublist StairSqLoopA.holes`, the same list as
`StairCertificate.holes39`), the new square
`square hl k = place L0 (newBrC hl (bodyC hl) ++ newBrB hl (bodyB hl) ++ newBrA hl (bodyA hl)) ++ entryRH (k - delta)`
* is run-equal to the record square on every state the record square is used on (`square_base`, the exact
  conclusion of `A161Generic.squareEntry_base`; `square_run_eq`);
* costs 157 more Toffolis and the same measurements (`square_counts`);
* is physical (`square_physical`);
* is field 12's `square` piece for the holes `hl` (`StairSquareFinalSites.square_pieceOK`).
`squareEntryHL hl L k` is the layout-generic drop-in (record square on every other layout). -/

section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareFinal

open ECDSAAdd Arithmetic ControlledPointLayout Secp256k1 CompressedPointDialog
  StairSquareContract StairSquareAssembly

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def brA (hl : List Wire) : Program := StairSquareKernel26C.newBrA hl (StairSquareBodyA.bodyA hl)




section Holes

variable (hl : List Wire) (hsub : hl.Sublist StairSqLoopA.holes)
include hsub




theorem kA : ∀ (t : State) (m : List Bool), BranchPre t →
    run (brA hl) m t = run (recBrA (StairSquareBodyA.bodyA hl)) m t := fun t m pre =>
  StairSquareKernel26C.kA_run_eq hl (mem39 hl hsub) _ (StairSquareBodyOK.bodyA_ok hl hsub)
    (StairSquareBodyA.bodyA_avoids hl hsub) t m pre




end Holes

end ECDSAAdd.Entrant.StairSquareFinal

end
end Merge_StairSquareFinal_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareFinalControl_at_BOptimizations` -/
section Merge_StairSquareFinalControl_at_BOptimizations

/-! # LT40 U6: the new square never touches the control wire

`square_control` replaces the square conjunct of the record's `ControlSupportDevelop.genericN_control`
for the hosted program.  Program-side file: no field-12 site machinery is imported. -/

section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareFinal

open ECDSAAdd Arithmetic ControlledPointLayout Secp256k1 CompressedPointDialog
  StairSquareContract StairSquareAssembly

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

/-! ## The control wire against pool wires, the placement and the body maps -/




theorem bodyMap_control :
    LowZero18Square.foldPerm K0 E0 (R2SqEp760.sqSwap K0 E0 L0.control) = L0.control := by
  decide +kernel




/-- The image of a body under the wrapper's body maps misses the control wire. -/
theorem control_not_bodyImage (X : Program) (hX : wires X ⊆ insert D0 (G0 :: K0.wires).toFinset) :
    L0.control ∉ ((wires X).image (R2SqEp760.sqSwap K0 E0)).image (LowZero18Square.foldPerm K0 E0) := by
  intro h
  simp only [Finset.mem_image] at h
  obtain ⟨z, ⟨x, hx, rfl⟩, e⟩ := h
  have ex : x = L0.control :=
    (R2SqEp760.sqSwap K0 E0).injective ((LowZero18Square.foldPerm K0 E0).injective
      (e.trans bodyMap_control.symm))
  exact control_not_bodyDomain (hX (ex ▸ hx))

/-! ## Record wrappers: wires = wrapper wires + the mapped body -/


theorem recBrB_split' (X Y : Program) :
    wires (recBrB X) ⊆ wires (recBrB Y) ∪
      ((wires X).image (R2SqEp760.sqSwap K0 E0)).image (LowZero18Square.foldPerm K0 E0) := by
  intro q hq
  simp only [recBrB, ParkCopy.withLowK2P, ParkCopy.pB, R2SqEp760.bodySwap, wires_append,
    renameProgram_support, Finset.mem_union] at hq ⊢
  tauto

theorem recBrA_split (X Y : Program) :
    wires (recBrA X) ⊆ wires (recBrA Y) ∪
      ((wires X).image (R2SqEp760.sqSwap K0 E0)).image (LowZero18Square.foldPerm K0 E0) := by
  intro q hq
  simp only [recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10, ParkCopy10.pB, R2SqEp760.bodySwap,
    wires_append, renameProgram_support, Finset.mem_union] at hq ⊢
  tauto

/-! ## The record square's own branches (from the record's control lemma) -/


theorem hostsK_control : L0.control ∉ StairSquareKernel26C.hostsK.toFinset := by
  intro h
  obtain ⟨n, -, h2, e⟩ := StairSquareKernel26C.hostsK_pool _ (List.mem_toFinset.mp h)
  exact pool_ne_control n (by omega) e.symm

/-! ## The new square -/


/-- The record tail `entryR` never touches the control wire (any constant). -/
theorem entryR_control (k : Fp) : L0.control ∉ wires (E1ReflectedPlacement.entryR L0 k) := by
  intro h
  simp only [E1ReflectedPlacement.entryR, renameProgram_support, Finset.mem_image] at h
  obtain ⟨y, hy, e⟩ := h
  have yS : y ∈ E1QubitPlacement.S := E1ReflectedPlacement.mergedR_S k.val hy
  by_cases hx : y ∈ wireBlock MappedCompressed.base 770 256
  · apply control_not_x
    rw [← E1QubitPlacement.pmap_x L0 hw0 hn0, ← e]
    exact List.mem_map_of_mem hx
  · by_cases hg : y = MappedCompressed.base 2400
    · subst hg
      rw [E1QubitPlacement.pmap_g L0 hw0 hn0] at e
      exact control_ne_generic e.symm
    · exact control_not_pool (e ▸ E1QubitPlacement.pmap_pool L0 hw0 hn0 y yS hx hg)

theorem entryRH_control (k : Fp) : L0.control ∉ wires (StairSquareEntryR.entryRH k) := by
  intro h
  have s := StairSquareHolesCore.hostRename_support StairSquareEntryR.entryPairs
    (E1ReflectedPlacement.entryR L0 k) StairSquareEntryR.entryPairs_nodup
    (StairSquareEntryR.entryPairs_hostFree k)
  rcases Finset.mem_union.mp (s h) with h | h
  · exact entryR_control k (Finset.mem_sdiff.mp h).1
  · simp only [StairSquareEntryR.entryPairs, StairSquareHolesCore.hostsOf, List.map_cons, List.map_nil,
      List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false] at h
    exact control_not_pool (h ▸ StairSquareEntryR.host_pool)


end ECDSAAdd.Entrant.StairSquareFinal

end
end Merge_StairSquareFinalControl_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareFinalPhysW_at_BOptimizations` -/
section Merge_StairSquareFinalPhysW_at_BOptimizations

/-! # LT40 U6: physicality of the record wrappers for any body -/

section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareFinal

open ECDSAAdd Arithmetic ControlledPointLayout Secp256k1 CompressedPointDialog
  StairSquareContract StairSquareAssembly

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires ECDSAAdd.Arithmetic.GatePhysical

/-! ## Counts and physicality -/

/-! Physicality of a record wrapper only depends on the body's physicality.  Proved for a variable
layout (so that no concrete program is ever unfolded), then instantiated. -/


theorem brB_physicalG (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (c : Wire)
    (src dst : List Wire) (X Y : Program)
    (hY : GatePhysical (ParkCopy.withLowK2P L ext c src dst (R2SqEp760.bodySwap L ext Y)))
    (hX : GatePhysical X) :
    GatePhysical (ParkCopy.withLowK2P L ext c src dst (R2SqEp760.bodySwap L ext X)) := by
  simp only [ParkCopy.withLowK2P, ParkCopy.pB, R2SqEp760.bodySwap, gatePhysical_append,
    R2SqEp760.gatePhysical_rename_iff] at hY ⊢
  tauto

theorem brA_physicalG (L : CuccaroStreamedSquareWideLayout) (ext : List Wire) (c : Wire) (X Y : Program)
    (hY : GatePhysical (A161Low4Branch.branch L ext c Y)) (hX : GatePhysical X) :
    GatePhysical (A161Low4Branch.branch L ext c X) := by
  simp only [A161Low4Branch.branch, ParkCopy10.withLowK2P10, ParkCopy10.pB, R2SqEp760.bodySwap,
    gatePhysical_append, R2SqEp760.gatePhysical_rename_iff] at hY ⊢
  tauto


theorem recBrB_physical (X Y : Program) (hY : GatePhysical (recBrB Y)) (hX : GatePhysical X) :
    GatePhysical (recBrB X) := brB_physicalG K0 E0 G0 _ _ X Y hY hX

theorem recBrA_physical (X Y : Program) (hY : GatePhysical (recBrA Y)) (hX : GatePhysical X) :
    GatePhysical (recBrA X) := brA_physicalG K0 E0 G0 X Y hY hX

end ECDSAAdd.Entrant.StairSquareFinal

end
end Merge_StairSquareFinalPhysW_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareFinalSlots_at_BOptimizations` -/
section Merge_StairSquareFinalSlots_at_BOptimizations

/-! # LT40 U6: slots and generic counts of the new square -/

section

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareFinal

open ECDSAAdd Arithmetic ControlledPointLayout Secp256k1 CompressedPointDialog
  StairSquareContract StairSquareAssembly

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

/-! ## Counts and physicality -/

/-! ## Slots and the layout-generic counts -/


theorem recBrB_slots (X Y : Program) :
    Challenge.gateSlots (recBrB X) + Challenge.gateSlots Y =
      Challenge.gateSlots (recBrB Y) + Challenge.gateSlots X := by
  simp only [recBrB, ParkCopy.withLowK2P, ParkCopy.pB, R2SqEp760.bodySwap,
    Challenge.gateSlots_append, Baselines.rename_gateSlots]
  omega

theorem recBrA_slots (X Y : Program) :
    Challenge.gateSlots (recBrA X) + Challenge.gateSlots Y =
      Challenge.gateSlots (recBrA Y) + Challenge.gateSlots X := by
  simp only [recBrA, A161Low4Branch.branch, ParkCopy10.withLowK2P10, ParkCopy10.pB, R2SqEp760.bodySwap,
    Challenge.gateSlots_append, Baselines.rename_gateSlots]
  omega



end ECDSAAdd.Entrant.StairSquareFinal

end
end Merge_StairSquareFinalSlots_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairTerminalV3_at_BOptimizations` -/
section Merge_StairTerminalV3_at_BOptimizations

/-!
# CANON v3 terminal blocks (LT14 audit defects D, E, F)

In the record, the terminal integer blocks run in the phase context
(`Rolling1588Lifetime.phaseHost`) on the record walk rails:

* division, end of `Six505.stackForward6 true`:
  `Six505.merged6 ++ Six505.packP true ++ ForwardSixPlacement.after true`,
  followed (in `firstPhase`) by `skywalkArithmeticClear base`;
* multiplication, start of `lastXN`: `skywalkArithmeticClear base`, then the
  head of `InverseFive23.stackReverse15 true`:
  `renameProgram (OB5.sig 511) tickR ++
   renameProgram (OB5.sig 510) (Rolling1588.unpackAtTick true 510 ++ InverseFive23.candidate15)`.

In the staircase they run inside the borrowed field tail, right after the moved
ticks `500 .. 504` (division) and right before the moved unticks `505 .. 500`
(multiplication).  `terminalPerm` is the one relabelling that makes them correct
there.  It is a product of 22 disjoint exchanges:

* the record rail-`b` bits `base (770 + k)`, `k < 20`, go to the moved rail-`b`
  sites `StairPhysicalLayout.bSite k` (= `segMap 500 505 (770 + k)`, defect D);
* letter `g 511` (`base 511`) goes to its field-tail label `base 2409`, whose
  kernel image is `base 511`, the record's wire (defect E);
* history `s 510` (`base 1543` after `OB5.sig 510`) goes to the raw field-tail
  label `base 1797`, whose kernel image is `base 1543` (field-tail `base 1543`
  would be the old omission pool 769);
* every other wire (letters `500 .. 510`, the a-word bits `512`, `513`, the
  bank bit `514`, the sig-placed histories `s 500 .. s 509`) keeps its label:
  for them the field-tail label already has the record's kernel image and is
  the moved walk's own site.

The terminal rail clear (defect F) is part of the relabelled blocks: it runs at
the end of `forwardTerminalV3` (after `SegLast`) and at the start of
`reverseTerminalV3` (before `RSegLast`), in moved coordinates; the copies in
`StairSchedule.firstPhase`, `StairSchedule.lastXN`,
`StairHostsSchedule.lastXN` and `StairConcreteAssembly.hostedEntryRest` must be
deleted.  The record's own phases (`Rolling1588TickGap.firstPhase false`,
`InverseFive23.lastPhase15 false`) are unchanged.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairTerminalV3

open ECDSAAdd Arithmetic MappedCompressed

/-! ## The relabelling -/




/-! ## Record blocks and the v3 programs -/

/-- Record division terminal blocks (the `StairPrimitives.forwardTerminal`
default) followed by the record terminal clear. -/
def forwardRecord : Program :=
  (Six505.merged6 ++ Six505.packP true ++ ForwardSixPlacement.after true) ++
    skywalkArithmeticClear base



/-- `StairPrimitives.forwardTerminal` for CANON v3. -/
def forwardTerminalV3 : Program := renameProgram terminalPerm forwardRecord





/-! ## Helpers -/






/-! ## Exact counts (δT = 0, δM = 0 against the record terminal blocks) -/










/-- δT = δM = 0: the v3 division terminal has exactly the counts of the
`StairPrimitives.forwardTerminal` default (the record blocks). -/
theorem forwardTerminalV3_counts_eq :
    toffoliCount forwardTerminalV3 =
        toffoliCount (Six505.merged6 ++ Six505.packP true ++ ForwardSixPlacement.after true) ∧
      measurementCount forwardTerminalV3 =
        measurementCount
          (Six505.merged6 ++ Six505.packP true ++ ForwardSixPlacement.after true) := by
  have hr := renameProgram_counts terminalPerm forwardRecord
  have cl := clear_counts
  rw [forwardTerminalV3, hr.1, hr.2]
  refine ⟨?_, ?_⟩ <;>
    simp only [forwardRecord, toffoliCount_append, measurementCount_append, cl.1, cl.2] <;>
    omega




theorem forwardTerminalV3_slots :
    Challenge.gateSlots forwardTerminalV3 = Challenge.gateSlots forwardRecord := by
  rw [forwardTerminalV3, Baselines.rename_gateSlots]


/-! ## Physicality -/

theorem forwardRecord_physical : GatePhysical forwardRecord := by
  have m6 : GatePhysical Six505.merged6 :=
    gatePhysical_rename (OB5.sig 510) (OB5.sig_injective 510 (by decide)) _ Six505.physical
  have pp : GatePhysical (Six505.packP true) := gatePhysical_of_all _ (by decide +kernel)
  have af : GatePhysical (ForwardSixPlacement.after true) :=
    gatePhysical_of_all _ (by decide +kernel)
  have cl : GatePhysical (skywalkArithmeticClear base) := gatePhysical_of_all _ (by decide +kernel)
  simp only [forwardRecord, gatePhysical_append]
  exact ⟨⟨⟨m6, pp⟩, af⟩, cl⟩


theorem forwardTerminalV3_physical : GatePhysical forwardTerminalV3 :=
  gatePhysical_rename terminalPerm terminalPerm.injective _ forwardRecord_physical


/-! ## Exact supports of the two large record blocks (block by block) -/

/-! ## K4-D (replay budget): one linear pass over the instructions

`decide` on `wires P ⊆ S` / `∀ x ∈ wires P, …` evaluates the `Finset` unions of `wires P` (quadratic);
`K4DT.allK c P` checks `c` on every wire of every instruction once, and `allK_sound` turns it into the
`wires P` statement for a variable program. -/
namespace K4DT








end K4DT




theorem cand6_support : wires Six505.cand6 ⊆ cand6Sites.toFinset := by
  -- K4-D (replay budget): one pass per block (no `Finset` unions, no nested appends)
  apply K4DT.sub_of_allK K4DT.c6_mem
  simp only [Six505.cand6, K4DT.allK, List.all_append]
  decide +kernel





/-! ## Support and avoidance -/






/-! ## LT50 (replay budget): kernel-fast form of `TermOK`

`decide` on `TermOK` walked the pool for every placement and scanned the 2,318-element caller list
and the 1,600-element arena (≈ 0.3 s per wire).  `termOKB` uses the closed-form placements of
`StairPlaceFast`, interval tests and literal exchanges; `termOK_of_B` is its soundness. -/













theorem forwardRecord_ok : ∀ x ∈ wires forwardRecord, TermOK forwardSites x := by
  -- LT50 (replay budget): decided on `termOKB` (closed-form placements), then `termOK_of_B`
  have m6B : cand6Sites.all (fun y => termOKB forwardSites (OB5.sig 510 y)) = true := by
    decide +kernel
  -- K4-D (replay budget): one pass over the instructions instead of `decide` over `wires P`
  have ppB : ∀ x ∈ wires (Six505.packP true), termOKB forwardSites x = true :=
    K4DT.allK_sound _ _ (by decide +kernel)
  have afB : ∀ x ∈ wires (ForwardSixPlacement.after true), termOKB forwardSites x = true :=
    K4DT.allK_sound _ _ (by decide +kernel)
  have clB : ∀ x ∈ wires (skywalkArithmeticClear base), termOKB forwardSites x = true :=
    K4DT.allK_sound _ _ (by decide +kernel)
  have m6 : ∀ y ∈ cand6Sites, TermOK forwardSites (OB5.sig 510 y) :=
    fun y hy => termOK_of_B (List.all_eq_true.mp m6B y hy)
  have pp : ∀ x ∈ wires (Six505.packP true), TermOK forwardSites x :=
    fun x hx => termOK_of_B (ppB x hx)
  have af : ∀ x ∈ wires (ForwardSixPlacement.after true), TermOK forwardSites x :=
    fun x hx => termOK_of_B (afB x hx)
  have cl : ∀ x ∈ wires (skywalkArithmeticClear base), TermOK forwardSites x :=
    fun x hx => termOK_of_B (clB x hx)
  intro x hx
  simp only [forwardRecord, wires_append, Finset.mem_union] at hx
  rcases hx with ((hm | hp) | ha) | hc
  · rw [Six505.merged6, renameProgram_support, Finset.mem_image] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    exact m6 y (List.mem_toFinset.mp (cand6_support hy))
  · exact pp x hp
  · exact af x ha
  · exact cl x hc


theorem forwardTerminalV3_wires : wires forwardTerminalV3 ⊆ forwardSites.toFinset := by
  intro q hq
  rw [forwardTerminalV3, renameProgram_support, Finset.mem_image] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  exact List.mem_toFinset.mpr (forwardRecord_ok x hx).2.2



/-- Support/avoidance of the division terminal: every wire is a final-arena
site, avoids the 15 old and 44 new omissions under `place`, avoids the 44
exclusive roles (raw and under `fieldPlace`), and lies in the caller domain. -/
theorem forwardTerminalV3_support : ∀ q ∈ wires forwardTerminalV3,
    StairPhysicalInventory.place q ∈ StairHoleSupport.recordArena ∧
      StairPhysicalInventory.place q ∉ StairHoleSupport.oldHoles ∧
      StairPhysicalInventory.place q ∉ StairPhysicalInventory.physicalHoles ∧
      q ∉ StairPhysicalInventory.exclusiveSites ∧
      StairOuterPlacement.fieldPlace q ∉ StairPhysicalInventory.exclusiveSites ∧
      StairOuterPlacement.fieldPlace q ∈ callerList := by
  intro q hq
  rw [forwardTerminalV3, renameProgram_support, Finset.mem_image] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  exact siteOK_spec (forwardRecord_ok x hx).2.1


/-! ## Placement of the relabelling -/





/-! ## Run-level transport (the replay form for the field-2 chain) -/




theorem forwardTerminalV3_replay (s r : State) (m n : List Bool)
    (agree : ∀ q ∈ wires forwardRecord, s.basis (terminalPerm q) = r.basis q) :
    (∀ q ∈ wires forwardRecord,
        (run forwardTerminalV3 m s).basis (terminalPerm q) = (run forwardRecord n r).basis q) ∧
      (((run forwardTerminalV3 m s).phase ^^ s.phase) =
        ((run forwardRecord m r).phase ^^ r.phase)) ∧
      (∀ q, q ∉ wires forwardTerminalV3 →
        (run forwardTerminalV3 m s).basis q = s.basis q) := by
  -- K4-D (replay budget): unfold the program name first (the kernel otherwise unfolds `run`)
  rw [show forwardTerminalV3 = renameProgram terminalPerm forwardRecord from rfl]
  exact rename_replay terminalPerm forwardRecord s r m n agree


end ECDSAAdd.Entrant.StairTerminalV3

end
end Merge_StairTerminalV3_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitTermRecord_at_BOptimizations` -/
section Merge_StairField2V3ExitTermRecord_at_BOptimizations

/-!
# Terminal round trip in record coordinates (LT24, field 2 exit, obligation 3(b))

The record terminal blocks, with the record terminal clear on both sides
(`StairTerminalV3.forwardRecord` / `reverseRecord`), followed by the record
untick `505` (`step505`), undo each other on every state of the record
trajectory at tick 505:

`run (reverseRecord ++ step505) a (run forwardRecord c ρ) = ρ`,
`ρ = run (Rolling1588TickGap.forward true 1 504) m s1`, `s1` a stage-1 state.

Forward side: the record's whole-walk `stackForward = regularForward 1 511`.
Reverse side: the record's head-level replacements are chained
(`TerminalFive` → `InverseFour15` → `tickMR8` → regular unticks), then
`reverse_gen 505 7` and `regularReverse_roundtrip`.  No program run is
evaluated; every state is a variable.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairExitLT24Term

open ECDSAAdd Arithmetic MappedCompressed Secp256k1 OB5
open Rolling1588.Integer

attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward

/-! ## Generic helpers -/




/-! ## Forward side -/

/-- The record forward ticks `1 .. 504` are tape independent. -/
theorem fwd504 (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (m : List Bool) :
    run (Rolling1588TickGap.forward true 1 504) m s1 =
      pullState (sig 504) (run (regularForward base true 1 504) [] s1) := by
  have init := stage_one base true x p s1 first
  have pre := Rolling1588TickGap.forward_gen true x hx0 hx 504 1 (le_refl _) (by omega) s1 m init
  rw [start_pull] at pre
  rw [pre, Six505.regular_indep true x hx0 hx 504 1 (by omega) s1 m [] init]

theorem fwd_whole (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (M : List Bool) :
    run (Rolling1588TickGap.stackForward true) M s1 =
      pullState (sig 511) (run (regularForward base true 1 511) M s1) := by
  rw [Rolling1588TickGap.stackForward_run_eq true x hx0 hx s1 M first,
    ← Rolling1588.Integer.stackForward_eq_packets,
    Rolling1588.Integer.stackForwardT_run true Six505.shared_nodup StackOB5.historyAbove
      x hx0 hx s1 M first,
    Rolling1588.Integer.forward_run true x hx0 hx s1 M first]

/-- The record forward terminal blocks (without the clear) from tick 505. -/
abbrev fwdBlocks : Program :=
  Six505.merged6 ++ Six505.packP true ++ ForwardSixPlacement.after true

/-- K4-A (replay budget): the split of `stackForward` by rewriting (a `rfl` here makes the
kernel re-associate the terminal blocks by evaluation). -/
theorem stackForward_split_k4a :
    Rolling1588TickGap.stackForward true = Rolling1588TickGap.forward true 1 504 ++ fwdBlocks := by
  rw [Rolling1588TickGap.stackForward, Six505.stackForward6]
  simp only [fwdBlocks, List.append_assoc]

theorem fwd_terminal (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (m mF : List Bool) :
    run fwdBlocks mF (run (Rolling1588TickGap.forward true 1 504) m s1) =
      pullState (sig 511) (run (regularForward base true 1 511)
        (List.replicate (measurementCount (Rolling1588TickGap.forward true 1 504)) false ++ mF) s1) := by
  rw [← fwd_whole x hx0 hx s1 first]
  generalize hK : measurementCount (Rolling1588TickGap.forward true 1 504) = K
  have e : Rolling1588TickGap.stackForward true =
      Rolling1588TickGap.forward true 1 504 ++ fwdBlocks := stackForward_split_k4a
  rw [e, run_append (Rolling1588TickGap.forward true 1 504), hK, List.drop_left' (by simp), fwd504 x hx0 hx s1 first,
    fwd504 x hx0 hx s1 first]

/-! ## Reverse side: program shapes and counts -/



abbrev Q1 : Program :=
  renameProgram (sig 510) (Rolling1588.unpackAtTick true 510 ++ InverseFour15.candidate15)


theorem PE2 :
    renameProgram (sig 510) (Rolling1588.unpackAtTick true 510 ++ InverseFour15.old15) =
      Z1 ++ Z2 := by
  rw [InverseFour15.unpack51015]
  simp only [Z1, Z2, InverseFour15.same50715, InverseFour15.old15, Six505.rename_append,
    List.append_assoc]


/-! K4-A (replay budget): the three count equations share their blocks; each block is
counted once, and the two terminal candidates come from their recorded resources. -/






theorem cQ : measurementCount Q1 = measurementCount (Y ++ Z2) := by
  rw [measurementCount_append, mcY_k4a, mcZ2_k4a]
  show measurementCount (renameProgram (sig 510)
    (Rolling1588.unpackAtTick true 510 ++ InverseFour15.candidate15)) = 9 + 4
  rw [Six505.rename_append, measurementCount_append, StairTerminalV3.unpack510_counts.2,
    (renameProgram_counts _ _).2, InverseFour15.resources.2.1]


/-! ## Reverse side: the `tickMR8` block (copied from the record's
`Rolling1588.Integer.stackReverse510_run`, head part `key`) -/


/-! ## Reverse side: the regular forward split at 505 / 506 / 507 -/


theorem split507 : Rolling1588.Integer.regularForward base true 1 510 =
    Rolling1588.Integer.regularForward base true 1 506 ++
      ((MorningFour.tick507 ++ tripF) ++ Rolling1588.Integer.packAfter base true 510) := by
  rw [Rolling1588.Integer.regularForward_snoc base true 1 509,show (1:Nat)+509=510 by rfl,
    Rolling1588.Integer.regularForward_snoc base true 1 508,show (1:Nat)+508=509 by rfl,
    Rolling1588.Integer.regularForward_snoc base true 1 507,show (1:Nat)+507=508 by rfl,
    Rolling1588.Integer.regularForward_snoc base true 1 506,show (1:Nat)+506=507 by rfl,
    MorningPlacement.pack507,Rolling1588.Integer.pack508,Rolling1588.Integer.pack509,
    MorningFour.explicit507,tick508ExF_explicit,tick509ExF_explicit,tick510ExF_explicit]
  simp only [tripF,List.append_assoc,List.append_nil]




/-! ## Reverse side: the head chain -/


/-! ## Reverse side: assembly -/


/-! ## The record terminal round trip -/


theorem clear_twice (t : State) (mc : List Bool) :
    run (skywalkArithmeticClear base) [] (run (skywalkArithmeticClear base) mc t) = t := by
  simpa only [skywalkArithmeticClear] using skywalkTerminalClear_twice
    (base 511) (base 512) (base 770) (DirectSkywalk.arith_clear_gates base Six505.shared_nodup) t mc []


/-! ## From any tick `i ≤ 505` (the record part of `closeRef ∘ refJ0 = id`) -/

theorem tickgap_forward_add (isA : Bool) :
    ∀ (n k i : Nat), Rolling1588TickGap.forward isA i (n + k) =
      Rolling1588TickGap.forward isA i n ++ Rolling1588TickGap.forward isA (i + n) k
  | 0, k, i => by simp [Rolling1588TickGap.forward]
  | n + 1, k, i => by
      rw [show n + 1 + k = (n + k) + 1 by omega]
      simp only [Rolling1588TickGap.forward]
      rw [tickgap_forward_add isA n k (i + 1), show i + 1 + n = i + (n + 1) by omega]
      simp only [List.append_assoc]


theorem fwdN (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (n : Nat) (hn : n ≤ 511) (m : List Bool) :
    run (Rolling1588TickGap.forward true 1 n) m s1 =
      pullState (sig n) (run (Rolling1588.Integer.regularForward base true 1 n) [] s1) := by
  have init := Rolling1588.Integer.stage_one base true x p s1 first
  have pre := Rolling1588TickGap.forward_gen true x hx0 hx n 1 (le_refl _) (by omega) s1 m init
  rw [start_pull] at pre
  have e : 1 + n - 1 = n := by omega
  rw [pre, Six505.regular_indep true x hx0 hx n 1 (by omega) s1 m [] init, e]


end ECDSAAdd.Entrant.StairExitLT24Term

end
end Merge_StairField2V3ExitTermRecord_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitTermCarryD_at_BOptimizations` -/
section Merge_StairField2V3ExitTermCarryD_at_BOptimizations

/-!
# Carry cleanliness on the record trajectory around tick 505 (LT24)

The moved untick 505 of the terminal row keeps its carry ancillas on the moved
c-rail (`cSite 0 .. 4`), while the record blocks relabelled by `terminalPerm` keep
theirs at the record carry bits `base 1540 .. 1544`.  The two programs agree
because both sets of carries are clean at the junction.  Record side: the
record `Stage` has a zero carry block (`regValue (wireBlock base 1540 257) = 0`),
both at tick 505 (`ρ`) and after the record reverse terminal blocks (stage 506).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairExitLT24Term

open ECDSAAdd Arithmetic MappedCompressed Secp256k1 OB5
open Rolling1588.Integer

attribute [local irreducible] run wires toffoliCount measurementCount Challenge.gateSlots Rolling1588.forward Rolling1588.reverse Rolling1588.Integer.forward


/-- Carries are clean on the record state at tick 505. -/
theorem rho_carry (x : Nat) (hx0 : 0 < x) (hx : x < p) (s1 : State)
    (first : W.CompactSkywalkStage base (SkywalkRails.encode false false (x:Int) (p:Int)) 1 s1.basis)
    (m : List Bool) (k : Nat) (hk : k < 5) :
    (run (Rolling1588TickGap.forward true 1 504) m s1).basis (base (1540 + k)) = false := by
  have st5 : Rolling1588.Integer.Stage base true x p 505
      (run (Rolling1588.Integer.regularForward base true 1 504) [] s1).basis :=
    stage_after x hx0 hx s1 first 504 (by omega) []
  have h1 := congrArg (fun st : State => st.basis (base (1540 + k))) (fwd504 x hx0 hx s1 first m)
  have h2 := stage_carry x 505 (by omega) _ st5 k (by omega) (by omega)
  have h3 := (sig_fix_carry k hk).1
  exact h1.trans ((pull_basis _ _ _).trans ((congrArg _ h3).trans h2))

end ECDSAAdd.Entrant.StairExitLT24Term

end
end Merge_StairField2V3ExitTermCarryD_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairCountWalk_at_BOptimizations` -/
section Merge_StairCountWalk_at_BOptimizations

/-!
# Count ledger, part 1: packets, ticks, moved walks, record-walk additivity
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairCountLedger

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly

/-! ## Packets and ticks cost the same on every duplicate-free map -/



theorem forwardTick_counts_eq (w w' : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (hn' : (skywalkPoolWires w').Nodup)
    (i : Nat) (h0 : 385 ≤ i) (h1 : i ≤ 509) :
    toffoliCount (ECDSAAdd.Entrant.TickRanges.tick w i) =
        toffoliCount (ECDSAAdd.Entrant.TickRanges.tick w' i) ∧
      measurementCount (ECDSAAdd.Entrant.TickRanges.tick w i) =
        measurementCount (ECDSAAdd.Entrant.TickRanges.tick w' i) := by
  have a := StairSegment.forward_tick_counts w i h0 h1 hn
  have b := StairSegment.forward_tick_counts w' i h0 h1 hn'
  exact ⟨a.1.trans b.1.symm, a.2.trans b.2.symm⟩


/-! ## Moved walks against the record walks -/

theorem movedForward_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) : ∀ i, 385 ≤ i → i + n ≤ 510 →
      toffoliCount (StairReplay.movedForward w i n) =
          toffoliCount (Rolling1588TickGap.forward true i n) ∧
        measurementCount (StairReplay.movedForward w i n) =
          measurementCount (Rolling1588TickGap.forward true i n) := by
  induction n with
  | zero =>
    intro i _ _
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro i h0 hb
    obtain ⟨r1, r2⟩ := ih (i + 1) (by omega) (by omega)
    obtain ⟨t1, t2⟩ := forwardTick_counts_eq w base hn base_pool_nodup i h0
      (by omega)
    obtain ⟨p1, p2⟩ := packFirst_counts_eq w base true i (by omega)
    simp only [StairReplay.movedForward, Rolling1588TickGap.forward,
      toffoliCount_append, measurementCount_append, renameProgram_counts]
    constructor <;> omega

theorem movedReverse_counts (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) : ∀ i, 385 ≤ i → i + n ≤ 510 →
      toffoliCount (StairReplay.movedReverse w i n) =
          toffoliCount (Rolling1588.reverse true i n) ∧
        measurementCount (StairReplay.movedReverse w i n) =
          measurementCount (Rolling1588.reverse true i n) := by
  induction n with
  | zero =>
    intro i _ _
    exact ⟨rfl, rfl⟩
  | succ n ih =>
    intro i h0 hb
    obtain ⟨r1, r2⟩ := ih (i + 1) (by omega) (by omega)
    obtain ⟨t1, t2⟩ := reverseTick_counts_eq w base hn base_pool_nodup i h0
      (by omega)
    obtain ⟨u1, u2⟩ := unpackFirst_counts_eq w true i (by omega)
    simp only [StairReplay.movedReverse, Rolling1588.reverse,
      toffoliCount_append, measurementCount_append, renameProgram_counts]
    constructor <;> omega

/-! ## Additivity of the record walks and packet sequences -/

theorem forward_succ_counts (isA : Bool) (i n j k : Nat) (hj : j = i + 1)
    (hk : k = n + 1) :
    toffoliCount (Rolling1588TickGap.forward isA i k) =
        toffoliCount (ECDSAAdd.Entrant.TickRanges.tick base i) +
          toffoliCount (Rolling1588.Integer.packFirst base isA i) +
          toffoliCount (Rolling1588TickGap.forward isA j n) ∧
      measurementCount (Rolling1588TickGap.forward isA i k) =
        measurementCount (ECDSAAdd.Entrant.TickRanges.tick base i) +
          measurementCount (Rolling1588.Integer.packFirst base isA i) +
          measurementCount (Rolling1588TickGap.forward isA j n) := by
  subst hj
  subst hk
  refine ⟨?_, ?_⟩ <;>
    simp only [Rolling1588TickGap.forward, toffoliCount_append,
      measurementCount_append, renameProgram_counts]


theorem forward_counts_add (isA : Bool) (n : Nat) :
    ∀ i m j k : Nat, j = i + n → k = n + m →
      toffoliCount (Rolling1588TickGap.forward isA i k) =
          toffoliCount (Rolling1588TickGap.forward isA i n) +
            toffoliCount (Rolling1588TickGap.forward isA j m) ∧
        measurementCount (Rolling1588TickGap.forward isA i k) =
          measurementCount (Rolling1588TickGap.forward isA i n) +
            measurementCount (Rolling1588TickGap.forward isA j m) := by
  induction n with
  | zero =>
    intro i m j k hj hk
    rw [hj, hk]
    have z1 : toffoliCount (Rolling1588TickGap.forward isA i 0) = 0 := rfl
    have z2 : measurementCount (Rolling1588TickGap.forward isA i 0) = 0 := rfl
    simp only [Nat.add_zero, Nat.zero_add]
    constructor <;> omega
  | succ n ih =>
    intro i m j k hj hk
    subst hj
    subst hk
    obtain ⟨r1, r2⟩ := ih (i + 1) m (i + (n + 1)) (n + m) (by omega) rfl
    rw [show n + 1 + m = (n + m) + 1 by omega]
    simp only [Rolling1588TickGap.forward, toffoliCount_append,
      measurementCount_append, renameProgram_counts]
    constructor <;> omega





end ECDSAAdd.Entrant.StairCountLedger

end
end Merge_StairCountWalk_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3Core_at_BOptimizations` -/
section Merge_StairField2V3Core_at_BOptimizations

/-!
# LT21: field 2 on CANON v3 — reduction to the two arithmetic cores

v3 port of LT14's `StairChainWitness.compositionOfCores` (which imported the
old-layout `StairChainPredicates`).  Everything except the two arithmetic run
equalities is proved here:

* `compositionOfCores entryCore exitCore : ConcreteComposition concreteAssembly`
* `field2_of_cores entryCore exitCore :
    CodecFunctionalSpec concreteAssembly → CheckpointReplaySpec concreteAssembly`
  (= the certificate's `checkpoint_composition` field type).

Each core is further split (`entryCore_of_split`, `exitCore_of_split`) into a
*basis* simulation with the empty tape and a *phase* statement.  The basis
evolution of `run` ignores the tape (`run_basis_records`), so the basis part is
a purely classical simulation; the record side is tape-free on the relevant
states, so only the staircase phase has to be matched.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3Core

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField



def ExitMiddle (k : Nat) (t : State) : Prop :=
  ∃ s, StairConcreteAssembly.ExitPre k s ∧
    ∃ records, t = run StairField2V3Replay.exitReferenceOpening records s



theorem exitOpening_run_eq (k : Nat) (s : State)
    (hs : StairConcreteAssembly.ExitPre k s) (fresh old : List Bool) :
    run StairField2V3Replay.exitReferenceOpening fresh s =
      run StairField2V3Replay.exitReferenceOpening old s := by
  rcases hs with ⟨frame⟩
  have clean := Rolling1588Lifetime.caller_phase_clean frame.x frame.Y.val s
    frame.input
  have hosted (m : List Bool) :=
    Rolling1588TickGap.first_hosted_run_eq false frame.sharedNodup frame.x
      frame.Y.val frame.x_pos frame.x_lt s m frame.input
  rw [StairField2V3Replay.exitReferenceOpening, hosted fresh, hosted old]
  apply ECDSAAdd.Arithmetic.MappedCompressed.pullState_perm_injective
    Rolling1588Lifetime.phaseHost
  rw [ECDSAAdd.run_rename _ Rolling1588Lifetime.phaseHost.injective,
    ECDSAAdd.run_rename _ Rolling1588Lifetime.phaseHost.injective,
    Rolling1588Lifetime.pull_phase_clean s clean]
  exact run_eq_of_phase (Rolling1588.firstPhase false)
    s fresh old
    (Rolling1588Lifetime.first_phase false frame.sharedNodup
      frame.historyAbove frame.x frame.Y.val frame.x_pos frame.x_lt
      s fresh frame.input)
    (Rolling1588Lifetime.first_phase false frame.sharedNodup
      frame.historyAbove frame.x frame.Y.val frame.x_pos frame.x_lt
      s old frame.input)









/-! ## Basis / phase split of a core -/



end ECDSAAdd.Entrant.StairField2V3Core

end
end Merge_StairField2V3Core_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3Entry_at_BOptimizations` -/
section Merge_StairField2V3Entry_at_BOptimizations

/-!
# LT21: the division core of field 2 as a coupled chain (generic in the primitives)

Both arithmetic programs are cut into the same list of pieces
(`selArith_shape`, `refArith_shape`):

```
selected  : W ++ J0sel ++ FP ++ G(1,84) ++ S425 ++ G(85,5) ++ S450 ++ G(90,3) ++ S465 ++ G(93,3)
              ++ S480 ++ G(96,2) ++ S490 ++ G(98,2) ++ LAST ++ TAIL
reference : W ++ J0ref ++ FP ++ G(1,84) ++        G(85,5) ++        G(90,3) ++        G(93,3)
              ++        G(96,2) ++        G(98,2) ++         TAIL
```
`W` = native forward + record ticks 1..424 (shared), `FP` = placed first packet + scratch
clear (shared), `G` = lifted record packet groups (shared), `TAIL` = lifted suffix
(groups 100..101, endpoint, copy, canon) + unprefix + X + setup (shared).
`J0sel` = `phaseHost firstPack` (the clear is inside the v3 terminal block), `J0ref` = `phaseHost (ticks 425..504 ++ record
terminal ++ clear) ++ setup ++ X`; `S…` = lifted staircase segments; `LAST` = lifted
`forwardLast ++ setup ++ X`.

`EntryPlan p` collects exactly the remaining obligations: one junction, five segment
steps, the last segment, the avoidance of the six group blocks and the first packet, and
the locality of the side conditions.  `entryArith_of_plan` turns a plan into the run
equality for independent tapes.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3Entry

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple

/-! ## Pieces -/




def prefixW : Program :=
  ph (FrontierEntry1591Native.forward base ++ Rolling1588TickGap.forward true 1 424)


def refJ0 : Program :=
  ph (Rolling1588TickGap.forward true 425 80 ++
      (Six505.merged6 ++ (Six505.packP true ++ ForwardSixPlacement.after true)) ++
      skywalkArithmeticClear base) ++
    StairSchedule.paritySetup ++ StairSchedule.hostedX







/-! ## Shape lemmas (variable programs only) -/


theorem forward_add (isA : Bool) :
    ∀ (a b i : Nat), Rolling1588TickGap.forward isA i (a + b) =
      Rolling1588TickGap.forward isA i a ++ Rolling1588TickGap.forward isA (i + a) b
  | 0, b, i => by simp [Rolling1588TickGap.forward]
  | a + 1, b, i => by
      have h : a + 1 + b = (a + b) + 1 := by omega
      rw [h]
      simp only [Rolling1588TickGap.forward, List.append_assoc]
      rw [forward_add isA a b (i + 1)]
      have hi : i + 1 + a = i + (a + 1) := by omega
      rw [hi]




theorem forward_504 : Rolling1588TickGap.forward true 1 504 =
    Rolling1588TickGap.forward true 1 424 ++ Rolling1588TickGap.forward true 425 80 := by
  rw [show (504 : Nat) = 424 + 80 from rfl, forward_add]



theorem refArith_shape :
    entryReferenceArithmetic =
      prefixW ++ (refJ0 ++ (firstPkt ++ (grp 1 84 ++ (grp 85 5 ++ (grp 90 3 ++ (grp 93 3 ++
        (grp 96 2 ++ (grp 98 2 ++ tailP)))))))) := by
  simp only [entryReferenceArithmetic, Rolling1588TickGap.firstPhase,
    Rolling1588TickGap.tailPhase, Rolling1588TickGap.stackForward, Six505.stackForward6,
    forward_504, Rolling1588.entryFieldHosted, ParityField1591.program,
    ParityHostTransport5.program, FrontierEntry1591Field.hosted, Rolling1588.entryField,
    Rolling1588.entryTail, groups_101, StairSchedule.paritySetup, StairSchedule.hostedX,
    StairSchedule.entryTailSuffix, StairSchedule.placedGroups,
    StairSchedule.placedEndPacket, StairSchedule.recordLoans,
    StairSchedule.fieldRename, StairSchedule.parityRename,
    prefixW, refJ0, firstPkt, grp, tailP, liftF, ph, rename_append', parity_X,
    List.append_assoc]

/-! ## The plan -/


/-- Shared walk prefix reached from a division input. -/
def J0 (s t : State) : Prop :=
  s = t ∧ Reach prefixW s

/-- Record prefixes reached before each staircase segment (left-nested, as produced by
`crel_track`). -/
def R0 : Program := prefixW ++ refJ0
def R1 : Program := (R0 ++ firstPkt) ++ grp 1 84
def R2 : Program := R1 ++ grp 85 5
def R3 : Program := R2 ++ grp 90 3
def R4 : Program := R3 ++ grp 93 3
def R5 : Program := R4 ++ grp 96 2
def R6 : Program := R5 ++ grp 98 2














end ECDSAAdd.Entrant.StairField2V3Entry

end
end Merge_StairField2V3Entry_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitPlan_at_BOptimizations` -/
section Merge_StairField2V3ExitPlan_at_BOptimizations

/-!
# LT21: the multiplication core of field 2 as a coupled chain

Both remainders are cut into the same pieces (`selRem_shape`, `refRem_shape`):

```
selected  : HEAD ++ FIRST ++ g(98,2) ++ R490 ++ g(96,2) ++ R480 ++ g(93,3) ++ R465 ++ g(90,3)
              ++ R450 ++ g(85,5) ++ R425 ++ g(1,84) ++ LOW ++ CLOSEsel ++ CLOSE
reference : HEAD ++         g(98,2) ++        g(96,2) ++        g(93,3) ++        g(90,3)
              ++        g(85,5) ++        g(1,84) ++ LOW ++ CLOSEref ++ CLOSE
```
`HEAD` = setup + X + scratch clear + lifted (center, copy, endpoint, groups 101..100)
(shared); `FIRST` = setup + X + lifted `reverseLast`; `R…` = lifted reverse segments;
`LOW` = unprefix + first packet (shared); `CLOSEsel` = `phaseHost (clear ++ firstUnpack)`,
`CLOSEref` = X + setup + `phaseHost (clear ++ tickR ++ unpack 510 ++ candidate15 ++ unticks
505..425)`; `CLOSE` = `phaseHost (unticks 424..1 ++ x1N k)` (shared).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3ExitPlan

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry

/-! ## The plan -/

def JE (k : Nat) (s t : State) : Prop :=
  s = t ∧ ∃ s0 m, StairField2V3Core.ExitMiddle k s0 ∧ s = run headE m s0







end ECDSAAdd.Entrant.StairField2V3ExitPlan

end
end Merge_StairField2V3ExitPlan_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitMiddle_at_BOptimizations` -/
section Merge_StairField2V3ExitMiddle_at_BOptimizations

/-!
# Moved middle round trip (LT24; ported verbatim from LT14's
`StairNamedReplay`, built there on CANON 1319)

`movedMiddle_roundtrip`: on a genuine `Rolling1588.Integer.Stage w true x p i`
state, the moved receiver block `StairReplay.movedReverse w i n` undoes the
moved forward block `StairReplay.movedForward w i n`, for independent tapes.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3ExitMiddle

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField

theorem integer_tick_run_eq (w : Nat → Wire) (isA : Bool)
    (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat) (hx0 : 0 < x) (hx : x < p) (hcop : x.Coprime p)
    (hi : i < 512) (s : State) (m : List Bool)
    (stage : Rolling1588.Integer.Stage w isA x p i s.basis) :
    run (TickRanges.tick w i) m s = run (W.repairedTick w i) m s := by
  obtain ⟨raw, rawStage, bits⟩ := stage
  have dis := Rolling1588.Integer.prefix_disjoint_layout w isA hn i i
    (Nat.le_refl i) hi
  have read : ∀ q ∈ (W.compactSkywalkTickLayout w i).wires.toFinset,
      s.basis q = raw.basis q := by
    intro q hq
    rw [bits]
    exact run_preserves_outside _ _ _ q
      (fun used => Finset.disjoint_left.mp dis used hq)
  have old := W.repairedTick_support w i hi hn
  have fresh := (TickRanges.tick_support w i hi hn).trans old
  exact Stack5.local_replace _ _ _ fresh old s raw m m read
    (TickRanges.tick_eq w hn x i hx0 hx hcop hi raw m rawStage)

theorem integer_block_run_eq (w : Nat → Wire) (isA : Bool)
    (hn : (skywalkPoolWires w).Nodup)
    (x i : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hodd : p % 2 = 1)
    (hp : p < 2 ^ 256) (hgap : p + 2 ^ 32 ≤ 2 ^ 256)
    (hx : x < p) (hcop : x.Coprime p)
    (hi0 : 385 ≤ i) (hi1 : i < 512)
    (s : State) (fresh old : List Bool)
    (stage : Rolling1588.Integer.Stage w isA x p i s.basis) :
    run (TickRanges.tick w i ++ Rolling1588.Integer.packFirst w isA i)
        fresh s =
      run (W.repairedTick w i ++ Rolling1588.Integer.packAfter w isA i)
        old s := by
  have sameTape :
      run (TickRanges.tick w i ++ Rolling1588.Integer.packFirst w isA i)
          fresh s =
        run (W.repairedTick w i ++ Rolling1588.Integer.packFirst w isA i)
          fresh s := by
    rw [run_append (TickRanges.tick w i),
      run_append (W.repairedTick w i),
      run_take (TickRanges.tick w i), run_take (W.repairedTick w i),
      integer_tick_run_eq w isA hn x i hx0 hx hcop hi1 s fresh stage,
      (TickRanges.tick_counts w i hi1 hn).2]
  have firstIsRegular : Rolling1588.Integer.packFirst w isA i =
      Rolling1588.Integer.packAfter w isA i := by
    simp only [Rolling1588.Integer.packFirst, if_neg (by omega : i ≠ 5)]
  have freshCompact := Rolling1588.Integer.step_eq w isA hn x p i
    hp0 hx0 hodd hp hgap hx hcop hi1 s fresh [] stage
  have oldCompact := Rolling1588.Integer.step_eq w isA hn x p i
    hp0 hx0 hodd hp hgap hx hcop hi1 s old [] stage
  calc
    run (TickRanges.tick w i ++ Rolling1588.Integer.packFirst w isA i)
        fresh s =
        run (W.repairedTick w i ++ Rolling1588.Integer.packFirst w isA i)
          fresh s := sameTape
    _ = run (W.repairedTick w i ++ Rolling1588.Integer.packAfter w isA i)
          fresh s := by rw [firstIsRegular]
    _ = run (W.compactSkywalkTick w i ++
          Rolling1588.Integer.packAfter w isA i) [] s := freshCompact
    _ = run (W.repairedTick w i ++ Rolling1588.Integer.packAfter w isA i)
          old s := oldCompact.symm

/-- Literal selected middle block versus the record's generic unplaced
`regularForward`, with independent tapes. -/
theorem movedForward_run_eq_regular (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (history : History5.HistoryAbove w)
    (x i n : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hodd : p % 2 = 1)
    (hp : p < 2 ^ 256) (hgap : p + 2 ^ 32 ≤ 2 ^ 256)
    (hx : x < p) (hcop : x.Coprime p)
    (hi0 : 385 ≤ i) (bound : i + n ≤ 512)
    (s : State) (fresh old : List Bool)
    (stage : Rolling1588.Integer.Stage w true x p i s.basis) :
    run (StairReplay.movedForward w i n) fresh s =
      run (Rolling1588.Integer.regularForward w true i n) old s := by
  induction n generalizing i s fresh old with
  | zero => rfl
  | succ n ih =>
      let selected := TickRanges.tick w i ++
        Rolling1588.Integer.packFirst w true i
      let reference := W.repairedTick w i ++
        Rolling1588.Integer.packAfter w true i
      let next := run reference (old.take (measurementCount reference)) s
      have first :
          run selected (fresh.take (measurementCount selected)) s = next := by
        change run (TickRanges.tick w i ++
            Rolling1588.Integer.packFirst w true i)
            (fresh.take (measurementCount selected)) s =
          run (W.repairedTick w i ++
            Rolling1588.Integer.packAfter w true i)
            (old.take (measurementCount reference)) s
        exact integer_block_run_eq w true hn x i hp0 hx0 hodd hp hgap
          hx hcop hi0 (by omega) s _ _ stage
      have nextStage :
          Rolling1588.Integer.Stage w true x p (i + 1) next.basis := by
        exact (Rolling1588.Integer.step_spec w true hn history x p i
          hp0 hx0 hodd hp hgap hx hcop (by omega) s
          (old.take (measurementCount reference)) stage).2
      have rest := ih (i + 1) (by omega) (by omega) next
        (fresh.drop (measurementCount selected))
        (old.drop (measurementCount reference)) nextStage
      change run (selected ++ StairReplay.movedForward w (i + 1) n)
          fresh s =
        run (reference ++ Rolling1588.Integer.regularForward w true (i + 1) n)
          old s
      rw [run_append selected, run_append reference]
      rw [first]
      exact rest

/-- At stair indices `unpackFirst` is definitionally the ordinary packet
decoder, so the literal selected receiver list is the record's generic
receiver list. -/
theorem movedReverse_eq_regular (w : Nat → Wire)
    (i n : Nat) (hi : 385 ≤ i) :
    StairReplay.movedReverse w i n =
      Rolling1588.Integer.regularReverse w true i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      rw [StairReplay.movedReverse, Rolling1588.Integer.regularReverse,
        ih (i + 1) (by omega)]
      simp only [Rolling1588.Integer.unpackFirst,
        if_neg (by omega : i ≠ 5)]

/-- The actual multiplication-side interleaved receiver restores the exact
state consumed by the actual selected middle block. -/
theorem movedMiddle_roundtrip (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (history : History5.HistoryAbove w)
    (x i n : Nat)
    (hp0 : 0 < p) (hx0 : 0 < x) (hodd : p % 2 = 1)
    (hp : p < 2 ^ 256) (hgap : p + 2 ^ 32 ≤ 2 ^ 256)
    (hx : x < p) (hcop : x.Coprime p)
    (hi : 385 ≤ i) (bound : i + n ≤ 512)
    (s : State) (forwardRecords reverseRecords : List Bool)
    (stage : Rolling1588.Integer.Stage w true x p i s.basis) :
    run (StairReplay.movedReverse w i n) reverseRecords
        (run (StairReplay.movedForward w i n) forwardRecords s) = s := by
  have forwardEq := movedForward_run_eq_regular w hn history x i n
    hp0 hx0 hodd hp hgap hx hcop hi bound s forwardRecords [] stage
  rw [forwardEq, movedReverse_eq_regular w i n hi]
  exact Rolling1588.Integer.regularReverse_roundtrip w true hn history x p
    hp0 hx0 hodd hp hgap hx hcop n i bound s [] reverseRecords stage

end ECDSAAdd.Entrant.StairField2V3ExitMiddle

end
end Merge_StairField2V3ExitMiddle_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitTerminal_at_BOptimizations` -/
section Merge_StairField2V3ExitTerminal_at_BOptimizations

/-!
# Terminal row round trip `WT ∘ FT = id`, reduced to the terminal blocks (LT24)

`FT = wrap (unpack 12 · tick 500 · middleForward 501 4 · forwardTerminalV3)`,
`WT = wrap (reverseTerminalV3 · middleReverseFix 501 5 · untick 500 · pack 12)`.
Peeling the top moved untick off `middleReverseFix 501 5` gives the mirror
pairing `termPieces`; `termTrip` reduces `WT ∘ FT = id` to a `TripChain` whose
only non-generic link is the terminal-block fact
`(reverseTerminalV3 · untick 505) ∘ forwardTerminalV3 = id`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairExitLT24

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3ExitAlgebra StairPhysicalLayout








/-- The two middle maps of the terminal row agree on the four moved unticks
`501 .. 504`. -/
theorem terminal_middle_maps :
    StairReplay.movedReverse wRev 501 4 =
      StairReplay.movedReverse (StairPhysicalPrimitives.midSegmentMap 12) 501 4 := by
  decide +kernel


end ECDSAAdd.Entrant.StairExitLT24

end
end Merge_StairField2V3ExitTerminal_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitTermLink_at_BOptimizations` -/
section Merge_StairField2V3ExitTermLink_at_BOptimizations

/-!
# Terminal link of the terminal row, staircase coordinates (LT24, obligation 3(b))

`termTrip` (StairField2V3ExitTerminal) reduces the terminal row round trip
`WT ∘ FT = id` to four links.  The last one is the terminal-block link

`run (reverseTerminalV3 ++ movedReverse wRev 505 1) a (run forwardTerminalV3 c σ) = σ`.

All three programs are the record programs relabelled by `terminalPerm`
(`step505_moved`), so the link follows from the record round trip
`StairExitLT24Term.terminal_record_trip` on a *virtual* record state: the
state pulled back through `terminalPerm` has to agree with a record state at
tick 505 of some stage-1 trajectory, on the wires of the record blocks only.
No phase hypothesis is needed (the virtual trajectory's phase is adjusted).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairExitLT24

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1




/-- The moved untick 505 of the terminal row is the record untick 505,
relabelled by `terminalPerm`, with its five carry ancillas moved to the moved
c-rail. -/
theorem step505_moved :
    StairReplay.movedReverse wRev 505 1 =
      renameProgram carrySwap (renameProgram StairTerminalV3.terminalPerm StairExitLT24Term.step505) := by
  decide +kernel






/-- Record blocks of the terminal link. -/
abbrev linkF : Program := StairTerminalV3.forwardRecord






end ECDSAAdd.Entrant.StairExitLT24

end
end Merge_StairField2V3ExitTermLink_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitClose_at_BOptimizations` -/
section Merge_StairField2V3ExitClose_at_BOptimizations

/-!
# Obligation 3(c): the record round trip `closeRef ∘ refJ0 = id` (LT24)

LT21's division junction runs the record piece `refJ0` (record ticks 425..504,
terminal blocks, clear, setup, X) and the multiplication close runs `closeRef`
(X, setup, clear, record reverse terminal blocks, unticks 505..425).  On every
state whose `phaseHost` pull-back is the record trajectory state at tick 425
(`run (Rolling1588TickGap.forward true 1 424) m s1`, `s1` stage 1), the two
cancel for all tapes.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairExitLT24

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1

theorem refJ0_eq : StairField2V3Entry.refJ0 =
    StairField2V3Entry.ph (Rolling1588TickGap.forward true 425 (505 - 425) ++
      StairTerminalV3.forwardRecord) ++ SX := by
  simp only [StairField2V3Entry.refJ0, StairTerminalV3.forwardRecord, SX, List.append_assoc]



end ECDSAAdd.Entrant.StairExitLT24

end
end Merge_StairField2V3ExitClose_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitPlanR_at_BOptimizations` -/
section Merge_StairField2V3ExitPlanR_at_BOptimizations

/-!
# LT43: the multiplication plan with reachability and a pinned input

`ExitPlanV3` relates the two exit runs by `Rel (Δrow i) (C i)` only.  Every exit
step, however, needs a fact about the *reference* (multiplication record) state
that a `Δ`-local side condition cannot express: the reverse segments need the
record transcript on the whole `futurePayload B` (LT24's `ExitRowRel`), the exit
junction needs the last-step predicate of the record state, and the close needs
the record state at row 425 (for `close_record_trip`).

`ExitPlanR p k x` therefore carries, like the division plan, the reachability of the
reference state (`ReachE k x Y t`: reached from a multiplication middle state of
input `x` by the reference prefix `Y`), and pins the input `x` in the side
condition (`CvX x B`), so that the selected partner of a reference state is unique.

`field2_of_entryD_R` is field 2 from LT21's `EntryPlanV3d` and this plan.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3ExitPlanR

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg
open StairPhysicalLayout StairOuterPlacement

/-! ## Multiplication middle states with a pinned input -/

def ExitMiddleX (k x : Nat) (t : State) : Prop :=
  ∃ s, ∃ f : StairConcreteAssembly.ExitFrame k s, f.x = x ∧
    ∃ records, t = run StairField2V3Replay.exitReferenceOpening records s

theorem exitMiddle_x (k : Nat) (t : State) (h : StairField2V3Core.ExitMiddle k t) :
    ∃ x, ExitMiddleX k x t := by
  obtain ⟨s, ⟨f⟩, records, ht⟩ := h
  exact ⟨f.x, s, f, rfl, records, ht⟩

theorem exitMiddle_of_x (k x : Nat) (t : State) (h : ExitMiddleX k x t) :
    StairField2V3Core.ExitMiddle k t := by
  obtain ⟨s, f, _, records, ht⟩ := h
  exact ⟨s, ⟨f⟩, records, ht⟩

/-- Reference state reached from a multiplication middle state of input `x` by `Y`. -/
abbrev ReachE (k x : Nat) (Y : Program) (t : State) : Prop :=
  ReachBy (ExitMiddleX k x) Y t

/-! ## Side condition with the input pinned -/








/-- Relation before an exit step: pinned side condition and reachability. -/
def RowRelE (k x B : Nat) (Y : Program) (s t : State) : Prop :=
  RelX x B s t ∧ ReachE k x Y t




/-! ## Exit pieces of the reference prefix (left-nested, as produced by `crel_track`) -/

def JEX (k x : Nat) (s t : State) : Prop :=
  s = t ∧ ReachE k x headE s



/-! ## The chain -/

theorem crel_headX (k x : Nat) :
    CRel (fun s t => ExitMiddleX k x s ∧ s = t) (JEX k x) headE headE := by
  rintro s t ⟨hs, rfl⟩ fresh
  exact ⟨fresh, rfl, s, fresh, hs, rfl⟩

theorem sharedE (k x B : Nat) (P X : Program) (away : ∀ q ∈ Δv B, q ∉ wires P) :
    CRel (RowRelE k x B X) (RowRelE k x B (X ++ P)) P P :=
  crel_track (shared_step (Δv B) (CvX x B) (cvX_local x B) P away) (ExitMiddleX k x) X

theorem segE {k x B B' : Nat} {P X : Program}
    (h : CRel (RowRelE k x B X) (RelX x B') P []) :
    CRel (RowRelE k x B X) (RowRelE k x B' X) P [] :=
  crel_sel_reach (ExitMiddleX k x) X h








end ECDSAAdd.Entrant.StairField2V3ExitPlanR

end
end Merge_StairField2V3ExitPlanR_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3EntryPlanR_at_BOptimizations` -/
section Merge_StairField2V3EntryPlanR_at_BOptimizations

/-!
# LT43g: the division plan with reachability and a pinned input

LT21's `EntryPlan` relates the two division runs by `Rel (Δv B) (Cv B)`, where
`Cv B` only knows *some* input consistent with the record transcript on
`futurePayload B`.  The last step, however, needs the history letter `s 510` of the
*genuine* input (LT43c, finding F3).  `EntryPlanR p x` is the pinned mirror of
`EntryPlan`, exactly as `ExitPlanR` on the multiplication side: the reference state is
reached from a division input of input `x` (`ReachEn x X t`), and the side condition
is `CvX x B`.

`entryArith_of_planR` / `entryCore_of_planR` turn one plan per input into the
division core of field 2.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3EntryPlanR

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR
open StairPhysicalLayout StairOuterPlacement

/-! ## Division inputs with a pinned input -/







/-- Shared walk prefix reached from a division input of input `x`. -/
def J0X (x : Nat) (s t : State) : Prop :=
  s = t ∧ ReachEn x prefixW s





/-! ## The chain -/

theorem crel_prefixX (x : Nat) :
    CRel (fun s t => EntryPreX x s ∧ s = t) (J0X x) prefixW prefixW :=
  crel_prefix_gen _ _








/-! ## Segment steps from the pure spec and the record fact (pinned `seg_of_spec`) -/



end ECDSAAdd.Entrant.StairField2V3EntryPlanR

end
end Merge_StairField2V3EntryPlanR_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitStepsR_at_BOptimizations` -/
section Merge_StairField2V3ExitStepsR_at_BOptimizations

/-!
# LT43: the steps of `ExitPlanR` from pure staircase facts and record facts

* `rsegR` — reverse segment `B' → B` from LT24's pure mirror spec `RSegSpecT`
  (= `rspec_of_spec` of LT21/LT42's `SegSpecT` and the row round trip `RowTripT`)
  and the record fact that the multiplication reference state carries the
  transcript on `futurePayload B` and is clean on `scratchT B B'`.
* `junctionR` — the exit junction from the division last step in LT21's
  "pure spec + record predicate" form (`lastSpec`), the terminal round trip on the
  same states, and the record fact that the multiplication reference state after
  `headE` satisfies the predicate and carries the transcript on `futurePayload 12`.
* `closeR` — the close from the generic row-425 junction (`selJ0` vs `refJ0` on
  any admissible tick-424 state), the first-row round trip, LT24's record round
  trip `close_record_trip`, and the record fact that the multiplication reference
  state at row 425 is a `refJ0` image of an admissible state.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3ExitStepsR

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR
open StairPhysicalLayout StairOuterPlacement

/-! ## Reverse segments -/

/-- Record fact for a reverse segment `B' → B` reached by the reference prefix `Y`. -/
def RowRecE (k x B B' : Nat) (Y : Program) : Prop :=
  ∀ t, ReachE k x Y t → ∃ origin, TraceOK x origin ∧
    (∀ r ∈ futurePayload B, t.basis (fieldPlace r) = recVal origin r) ∧
    (∀ r ∈ scratchT B B', t.basis (fieldPlace r) = false)


/-! ## Exit junction -/

/-- Record fact for the exit junction: after `headE` the multiplication reference
state satisfies the last-step predicate `Φ` and carries the transcript on
`futurePayload 12`. -/
def JuncRecE (k x : Nat) (Φ : BasisState → Prop) : Prop :=
  ∀ t, ReachE k x headE t → Φ t.basis ∧ ∃ origin, TraceOK x origin ∧
    ∀ r ∈ futurePayload 12, t.basis (fieldPlace r) = recVal origin r


/- LT47: the unpinned exit junction was removed: on the defect-2-fixed program the
selected setup sits between two windows and is not an unconditional involution; the
pinned junction is `StairField2V3Field2R.junctionRX`. -/

/-! ## Close -/




end ECDSAAdd.Entrant.StairField2V3ExitStepsR

end
end Merge_StairField2V3ExitStepsR_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3Walk_at_BOptimizations` -/
section Merge_StairField2V3Walk_at_BOptimizations

/-!
# LT21: the moved walk of a v3 forward segment

* `walk_stage`: from LT30's `Decoded` checkpoint, the first moved tick and the
  moved middle reach — on the middle's wires — a VIRTUAL state carrying the
  record's `Rolling1588.Integer.Stage (midSegmentMap B) … (startFor B + 1 + n)`
  (LT30 `middle_virtual_provider` + LT14 `movedForward_run_eq_regular` + the
  record's `regularForward_spec`).
* `stage_end_values`: at a row end `e = startFor B'` such a stage puts the RAW
  rails `realRails x p e` on `fullS B'` / `fullD B'` and the raw letter on
  `letterSite (e - 1)` — exactly the premises of
  `StairField2V3End.codecInput_after_orient`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3Walk

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairPhysicalLayout StairField2V3End



/-- **Walk with full agreement off the virtual sites.** -/
theorem walk_full (B : Nat) (hB : B ∈ budgets) (x : Nat) (h : StairFirstTickV3.RealHyp x ECDSAAdd.p)
    (y : State) (hy : StairFirstTickV3.Decoded B x ECDSAAdd.p y.basis) (c m : List Bool) (n : Nat)
    (hn : startFor B + 1 + n ≤ 512) :
    ∃ z : State,
      (run (StairPhysicalPrimitives.middleForward (startFor B + 1) n) m
        (run (StairPhysicalPrimitives.tickForward (startFor B)) c y)).phase = z.phase ∧
      (∀ q, ¬ StairFirstTickV3.virtualSites B q →
        (run (StairPhysicalPrimitives.middleForward (startFor B + 1) n) m
          (run (StairPhysicalPrimitives.tickForward (startFor B)) c y)).basis q = z.basis q) ∧
      Rolling1588.Integer.Stage (StairPhysicalPrimitives.midSegmentMap B) true x ECDSAAdd.p
        (startFor B + 1 + n) z.basis ∧ z.phase = y.phase := by
  obtain ⟨tph, tstage⟩ := StairFirstTickV3.tick_forward B hB x ECDSAAdd.p h y hy c
  obtain ⟨t', hph, hagree, hstage⟩ :=
    StairFirstTickV3.virtual_stage B hB x ECDSAAdd.p h true _ tstage
  have hseg := (StairFirstTickV3.budget_range B hB)
  have eF : StairPhysicalPrimitives.middleForward (startFor B + 1) n =
      StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1) n := by
    unfold StairPhysicalPrimitives.middleForward
    rw [hseg.2.2.2.2.2]
  have hnod := StairPhysicalPrimitives.midSegmentMap_pool_nodup B hB
  have hhist := StairPhysicalPrimitives.midSegmentMap_historyAbove B hB
  have hreg := StairField2V3MidFwd.movedForward_run_eq_regular
    (StairPhysicalPrimitives.midSegmentMap B) hnod hhist x (startFor B + 1) n
    h.p0 h.x0 h.odd h.lt h.gap h.xlt h.cop (by omega) hn t' m [] hstage
  have spec := Rolling1588.Integer.regularForward_spec (StairPhysicalPrimitives.midSegmentMap B) true
    hnod hhist x ECDSAAdd.p (startFor B + 1) n h.p0 h.x0 h.odd h.lt h.gap h.xlt h.cop hn t' [] hstage
  rw [eF]
  have clean : ∀ q ∈ wires (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B)
      (startFor B + 1) n), ¬ StairFirstTickV3.virtualSites B q :=
    fun q hq => StairFirstTickV3.middle_wires_clean B hB n hn q (Or.inl hq)
  have readP : ∀ q ∈ wires (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B)
      (startFor B + 1) n),
      (run (StairPhysicalPrimitives.tickForward (startFor B)) c y).basis q = t'.basis q :=
    fun q hq => hagree q (clean q hq)
  have inc := ECDSAAdd.Arithmetic.run_local_increment _ _ t' m readP
  refine ⟨run (Rolling1588.Integer.regularForward (StairPhysicalPrimitives.midSegmentMap B) true
    (startFor B + 1) n) [] t', ?_, ?_, spec.2, ?_⟩
  · have hz := spec.1
    have h1 := inc.1
    rw [hph, hreg, hz] at h1
    rw [hz]
    revert h1
    generalize (run (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B) (startFor B + 1) n) m
      (run (StairPhysicalPrimitives.tickForward (startFor B)) c y)).phase = a
    generalize t'.phase = b
    intro h1
    cases a <;> cases b <;> simp at h1 ⊢
  · intro q hq
    by_cases hw : q ∈ wires (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B)
        (startFor B + 1) n)
    · rw [inc.2 q hw, hreg]
    · rw [run_preserves_outside _ _ _ q hw, ← hreg, run_preserves_outside _ _ _ q hw]
      exact hagree q hq
  · rw [spec.1, ← hph, tph]

/-! ## Values at the row end -/








end ECDSAAdd.Entrant.StairField2V3Walk

end
end Merge_StairField2V3Walk_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3RecScratch_at_BOptimizations` -/
section Merge_StairField2V3RecScratch_at_BOptimizations

/-!
# LT42: the record fact `RecordScratch` for the five middle rows

The genuine record state after the record division prefix `R1 … R5` is zero on
the segment scratch `scratchT B B'` (pulled through `fieldPlace`).

Route (LT32's `StairLoanField7Values.entryGroups_inner`): after the record first
phase, the hosted wrapper and the first packet, the field view of the actual
state agrees off `EP = E ∪ payload0` with a placed record state carrying
`Rolling1588.CutFrame 1`; every record group avoids `EP`, so the agreement and
the frame (`groups_cut_frame`) move to `CutFrame (1+N)` at every segment cut
(`Inv`).  On a `CutFrame` every scratch label is zero (`frame_zero`): it is a
work/hole label, or an origin-clean label off the r/y words and the history
(`Env`), or the selector `base 2409` (`Context.hg0`); the per-row membership is a
finite check (`recFacts_*`, `decide +kernel`).

Sections "Exceptional sites" … "R0_shape" are verbatim copies of LT32's helpers
(`StairLoanField7Values`, which is not in this tree).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3RecScratch

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairOuterPlacement

attribute [local irreducible] wires run

/-! ## Exceptional sites -/







/-! ## The scratch window -/









/-! ## The host/parity wrapper -/





/-! ## Record facts (copies of LT10's private helpers) -/





theorem first_phase_hosted (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase isA)) m s =
      run (Rolling1588.firstPhase isA) m s := by
  refine (Rolling1588TickGap.first_hosted_run_eq isA hn x y hx0 hx s m input).trans ?_
  have before := Rolling1588Lifetime.caller_phase_clean x y s input
  apply Rolling1588Lifetime.phase_run_eq _ s m before
  intro q hq
  have work := Rolling1588Lifetime.first_clean isA hn hlo x y hx0 hx s m input
  rw [lf_eq] at work
  have hostsFree : ∀ r ∈ Rolling1588Lifetime.phaseHosts,
      r ∉ wires (Rolling1588.firstPhase isA) := by
    intro r hr
    have h := Rolling1588Lifetime.first_hosts_free isA r hr
    rw [lf_eq] at h
    exact h
  rw [phase_sites_split] at hq
  rcases Finset.mem_union.mp hq with w | h
  · exact work q w
  · exact (run_preserves_outside _ _ _ _ (hostsFree q h)).trans
      (before q (by rw [phase_sites_split]; exact Finset.mem_union_right _ h))

/-! ## Membership walks (variable programs) -/














/-! ## Entry: the loaned groups on the record trajectory -/

theorem R0_shape :
    R0 ++ firstPkt =
      renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
        (StairSchedule.paritySetup ++ StairSchedule.hostedX) ++
        StairSchedule.fieldRename (Rolling1588.placedFirstPacket true ++
          FourScratchWindow.clearProgram) := by
  simp only [R0, prefixW, refJ0, firstPkt, ph, Rolling1588TickGap.firstPhase,
    Rolling1588TickGap.tailPhase, Rolling1588TickGap.stackForward, Six505.stackForward6,
    forward_504, rename_append', List.append_assoc]

/-! ## LT42: record frames along the division groups -/











theorem inv_first (s0 : State) (h0 : StairConcreteAssembly.EntryPre s0) (m : List Bool) :
    Inv 1 (run (R0 ++ firstPkt) m s0) := by
  rcases h0 with ⟨f⟩
  have actual := FrontierEntry1591Kernel.paired_input f.x f.Y.val f.source s0 f.input
    f.outsideNumerator
  rw [R0_shape,
    run_append (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
      (StairSchedule.paritySetup ++ StairSchedule.hostedX)),
    run_append (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true)),
    first_phase_hosted true f.sharedNodup f.historyAbove f.x _ f.x_pos f.x_lt s0 _ actual]
  exact inv_inner s0 f _ _ _

theorem reach_R1 (t : State) (h : Reach R1 t) : Inv 85 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold R1
  rw [run_append (R0 ++ firstPkt) (grp 1 84)]
  exact inv_step 1 84 le_rfl (by norm_num) _ (inv_first s0 hs0 _) _

theorem reach_R2 (t : State) (h : Reach R2 t) : Inv 90 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold R2
  rw [run_append R1 (grp 85 5)]
  exact inv_step 85 5 (by norm_num) (by norm_num) _ (reach_R1 _ ⟨s0, _, hs0, rfl⟩) _

theorem reach_R3 (t : State) (h : Reach R3 t) : Inv 93 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold R3
  rw [run_append R2 (grp 90 3)]
  exact inv_step 90 3 (by norm_num) (by norm_num) _ (reach_R2 _ ⟨s0, _, hs0, rfl⟩) _

theorem reach_R4 (t : State) (h : Reach R4 t) : Inv 96 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold R4
  rw [run_append R3 (grp 93 3)]
  exact inv_step 93 3 (by norm_num) (by norm_num) _ (reach_R3 _ ⟨s0, _, hs0, rfl⟩) _

theorem reach_R5 (t : State) (h : Reach R5 t) : Inv 98 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold R5
  rw [run_append R4 (grp 96 2)]
  exact inv_step 96 2 (by norm_num) (by norm_num) _ (reach_R4 _ ⟨s0, _, hs0, rfl⟩) _

/-! ## Zero labels of a record `CutFrame` -/







/-! ## RecordScratch -/



/-! K4 (replay budget): the per-row checks used list scans of `ryL` (512), `histL` (1024),
`cleanL` (777) and `EP` per scratch label (quadratic, ≈ 3.5 s per row).  Each list is now a
literal bit mask checked once (`*_maskK_eq`), the row check `recCheck` is one linear pass with
`Nat.testBit` tests, and `recFacts_of` bridges it back to `RecFacts`. -/













theorem rec0 : StairField2V3Seg.RecordScratch 87 62 R1 := rec_of_inv 87 62 85 R1 recFacts0 reach_R1
theorem rec1 : StairField2V3Seg.RecordScratch 62 47 R2 := rec_of_inv 62 47 90 R2 recFacts1 reach_R2
theorem rec2 : StairField2V3Seg.RecordScratch 47 32 R3 := rec_of_inv 47 32 93 R3 recFacts2 reach_R3
theorem rec3 : StairField2V3Seg.RecordScratch 32 22 R4 := rec_of_inv 32 22 96 R4 recFacts3 reach_R4
theorem rec4 : StairField2V3Seg.RecordScratch 22 12 R5 := rec_of_inv 22 12 98 R5 recFacts4 reach_R5

end ECDSAAdd.Entrant.StairField2V3RecScratch

end
end Merge_StairField2V3RecScratch_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3SegSpec_at_BOptimizations` -/
section Merge_StairField2V3SegSpec_at_BOptimizations

/-!
# LT42: the forward-segment spec `SegSpecT` for the five middle rows

Assembly of LT21's segment ingredients (codec unpack, LT30's first moved tick
and virtual middle stage, orientation at the row end, the closing packet, the
codec pack) into `StairField2V3Seg.SegSpecT` for the concrete CANON v3
provider and the five row pairs `(87,62) (62,47) (47,32) (32,22) (22,12)`.

* `core`: the spec on states that are clean on the shadow labels `≥ base 4000`;
* `low_reduce`: every label of a segment is below `base 4000`, so arbitrary
  shadow contents are irrelevant;
* `segSpec`: the spec itself; `spec0 … spec4`: the five instances.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3SegSpec

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairPhysicalLayout StairField2V3Seg StairField2V3Codec StairField2V3Unpack StairField2V3Pack
open StairField2V3End StairField2V3Decode StairField2V3Walk StairField2V3SegFacts StairField2V3SegFacts2

/-! ## Generic helpers -/











/-- After the first moved tick the spare `zeroWire` (the tick's previous letter) is still 0. -/
theorem tick_zeroWire (B : Nat) (hB : B ∈ budgets) (x : Nat)
    (h : StairFirstTickV3.RealHyp x ECDSAAdd.p) (y : State)
    (hy : StairFirstTickV3.Decoded B x ECDSAAdd.p y.basis) (hz : y.basis zeroWire = false)
    (c : List Bool) :
    (run (StairPhysicalPrimitives.tickForward (startFor B)) c y).basis zeroWire = false := by
  obtain ⟨h0, h1, _, _, _, _⟩ := StairFirstTickV3.budget_range B hB
  have valid := SkywalkNat.iter_valid (startFor B) (SkywalkNat.init x ECDSAAdd.p) h.p0 h.odd
  have fit := StairBridgeDomain.canonical_real_fit x ECDSAAdd.p (startFor B) h.p0 h.x0 h.odd
    h.lt h.gap h.xlt h.cop (by omega)
  have hnod := segmentMap_pool_nodup B hB
  unfold StairFirstTickV3.Decoded at hy
  rw [StairBridgeDomain.orient_realRails x ECDSAAdd.p _ h.p0 h.odd] at hy
  have fit' : StairSegment.Fits (startFor B)
      (StairSegment.railAt (SkywalkRails.encode false
        (StairBridgeDomain.realSign x ECDSAAdd.p (startFor B))
        ((StairBridgeDomain.realNatState x ECDSAAdd.p (startFor B)).u : Int)
        ((StairBridgeDomain.realNatState x ECDSAAdd.p (startFor B)).v : Int))
        (startFor B - startFor B)) := by
    rw [Nat.sub_self]
    exact fit
  rw [StairFirstTickV3.tickForward_eq B hB,
    StairSegment.tick_run_eq (segmentMap B) (startFor B) (startFor B)
      (StairBridgeDomain.realSign x ECDSAAdd.p (startFor B))
      (StairBridgeDomain.realNatState x ECDSAAdd.p (startFor B)) (by omega) (by omega)
      hnod valid.1 valid.2.1 y c hy fit']
  have input := StairSegment.local_input (segmentMap B) (startFor B) (startFor B) _ (by omega)
    y.basis hy
  have res := W.compactSkywalkTickOutput_spec (segmentMap B) (startFor B) (by omega) hnod _ _ _
    fit'.odd fit'.halfMin fit'.halfMax fit'.otherMin fit'.otherMax y [] input
  have hout := res.2.2.2.2.2.1
  have hin := hy.previous
  rw [← segmentMap_previous B hB]
  exact hout.trans (hin.symm.trans ((congrArg y.basis (segmentMap_previous B hB)).trans hz))

/-! ## Walk frames -/

theorem walk_rows (B : Nat) (hB : B ∈ budgets) (c m : List Bool) (y : State) (q : Wire)
    (hq : q ∉ rowSites B) :
    (run (StairPhysicalPrimitives.middleForward (startFor B + 1) (endFor B - startFor B - 1)) m
      (run (StairPhysicalPrimitives.tickForward (startFor B)) c y)).basis q = y.basis q := by
  obtain ⟨s1, s2, -, s4, s5, s6⟩ := StairPhysicalPrimitives.budget_shape B hB
  have hT : q ∉ wires (StairPhysicalPrimitives.tickForward (startFor B)) := by
    intro h
    unfold StairPhysicalPrimitives.tickForward at h
    rw [s1] at h
    exact hq (StairPhysicalPrimitives.tick_rowSites B hB (startFor B) s6 le_rfl q
      (StairPhysicalPrimitives.tick_layout _ _ (by omega) (segmentMap_pool_nodup B hB) q h))
  have hM : q ∉ wires (StairPhysicalPrimitives.middleForward (startFor B + 1)
      (endFor B - startFor B - 1)) := by
    intro h
    unfold StairPhysicalPrimitives.middleForward at h
    rw [s2] at h
    exact hq (StairPhysicalPrimitives.movedForward_sub (StairPhysicalPrimitives.midSegmentMap B)
      (rowSites B) (StairPhysicalPrimitives.midSegmentMap_pool_nodup B hB) _ _ (by omega) s5
      (fun j h1 h2 => StairPhysicalPrimitives.midTick_rowSites B hB j (by omega) (by omega))
      (fun j h1 h2 due => StairPhysicalPrimitives.midPacket_rowSites B hB j (by omega) (by omega) due)
      q h)
  rw [run_preserves_outside _ _ _ q hM, run_preserves_outside _ _ _ q hT]

theorem mid_sub (B : Nat) (hB : B ∈ budgets) (q : Wire)
    (h : q ∈ wires (StairReplay.movedForward (StairPhysicalPrimitives.midSegmentMap B)
      (startFor B + 1) (endFor B - startFor B - 1))) : q ∈ midTicks B ++ midPackets B := by
  obtain ⟨-, -, -, s4, s5, s6⟩ := StairPhysicalPrimitives.budget_shape B hB
  refine StairPhysicalPrimitives.movedForward_sub (StairPhysicalPrimitives.midSegmentMap B)
    (midTicks B ++ midPackets B) (StairPhysicalPrimitives.midSegmentMap_pool_nodup B hB) _ _
    (by omega) s5 ?_ ?_ q h
  · intro j h1 h2 q' hq'
    apply List.mem_append_left
    unfold midTicks
    exact List.mem_flatMap.mpr ⟨j, List.mem_range'_1.mpr ⟨h1, by unfold midN; omega⟩, hq'⟩
  · intro j h1 h2 due k
    apply List.mem_append_right
    unfold midPackets
    refine List.mem_flatMap.mpr ⟨j, List.mem_range'_1.mpr ⟨h1, by unfold midN; omega⟩, ?_⟩
    simp only [due, ↓reduceIte]
    exact List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩

theorem walk_frame (B : Nat) (hB : B ∈ budgets) (c m : List Bool) (y : State) (q : Wire)
    (hq : q ∉ walkSites B) :
    (run (StairPhysicalPrimitives.middleForward (startFor B + 1) (endFor B - startFor B - 1)) m
      (run (StairPhysicalPrimitives.tickForward (startFor B)) c y)).basis q = y.basis q := by
  obtain ⟨s1, s2, -, s4, -, s6⟩ := StairPhysicalPrimitives.budget_shape B hB
  rw [walkSites_eq] at hq
  have hT : q ∉ wires (StairPhysicalPrimitives.tickForward (startFor B)) := by
    intro h
    unfold StairPhysicalPrimitives.tickForward at h
    rw [s1] at h
    exact hq (List.mem_append_left _ (List.mem_append_left _
      (StairPhysicalPrimitives.tick_layout _ _ (by omega) (segmentMap_pool_nodup B hB) q h)))
  have hM : q ∉ wires (StairPhysicalPrimitives.middleForward (startFor B + 1)
      (endFor B - startFor B - 1)) := by
    intro h
    unfold StairPhysicalPrimitives.middleForward at h
    rw [s2] at h
    rcases List.mem_append.mp (mid_sub B hB q h) with h1 | h1
    · exact hq (List.mem_append_left _ (List.mem_append_right _ h1))
    · exact hq (List.mem_append_right _ h1)
  rw [run_preserves_outside _ _ _ q hM, run_preserves_outside _ _ _ q hT]

theorem zeroWire_mid (B B' : Nat) (hpair : (B, B') ∈ rowPairs) (hB : B ∈ budgets) :
    zeroWire ∉ wires (StairPhysicalPrimitives.middleForward (startFor B + 1)
      (endFor B - startFor B - 1)) := by
  have fZT := FactsZeroT_ok B B' hpair
  have fZP := FactsZeroP_ok B B' hpair
  intro h
  unfold StairPhysicalPrimitives.middleForward at h
  rw [(StairPhysicalPrimitives.budget_shape B hB).2.1] at h
  rcases List.mem_append.mp (mid_sub B hB _ h) with h1 | h1
  · exact fZT h1
  · exact fZP h1

/-! ## The segment program -/




/-! ## The spec on shadow-clean states -/


/-! ## The spec -/

section
/- K4C (build budget): keep the elaborator from unfolding the codec programs while it matches
the `*_rows` lemmas against the hypotheses (as in `StairField2V3LastTraj.rev_low`). -/
attribute [local irreducible] StairPhysicalPrimitives.pack StairPhysicalPrimitives.unpack



end






end ECDSAAdd.Entrant.StairField2V3SegSpec

end
end Merge_StairField2V3SegSpec_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3LastStage_at_BOptimizations` -/
section Merge_StairField2V3LastStage_at_BOptimizations

/-!
# LT43c: the moved stage of row 500 against the record stage at tick 505

The moved walk of the terminal row ends (virtually) in a record integer stage on
the moved map `midSegmentMap 12` at tick 505.  The record walk
`Rolling1588TickGap.forward true 1 504` ends in the same stage on `base`
(placed by `OB5.sig 504`).  Both are determined by the input `x` on every stage
id that the terminal blocks read:

* `stage_agree`: id-wise agreement of the two stages (past letters, retained
  rail words, released pools, future letters, carries);
* `stage1_exists`: a record stage-1 state exists for every `0 < x < p`;
* `rec505`: the record state after ticks `1 .. 504` as a placed stage.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3LastStage

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairPhysicalLayout











/-! ## A record stage-1 state for every input -/


theorem stage1_exists (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) :
    ∃ s1 : State, W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)) 1 s1.basis := by
  have hnD : (skywalkArithmeticDivisor base).Nodup := by
    unfold skywalkArithmeticDivisor wireBlock
    exact List.Nodup.map base_injective List.nodup_range'
  have hlen : (skywalkArithmeticDivisor base).length = 256 := by
    unfold skywalkArithmeticDivisor wireBlock
    simp
  have hp : ECDSAAdd.p < 2 ^ 256 := by norm_num [ECDSAAdd.p]
  have input : SkywalkArithmeticInput base x 0
      (⟨false, StairCodec.registerBasis (skywalkArithmeticDivisor base) x⟩ : State).basis := by
    refine ⟨?_, ?_, ?_⟩
    · show regValue (skywalkArithmeticDivisor base)
        (StairCodec.registerBasis (skywalkArithmeticDivisor base) x) = x
      rw [StairField2V3Codec.regValue_of_bits _ _ x
        (fun i hi => StairField2V3Codec.registerBasis_get _ hnD x i hi), hlen]
      exact Nat.mod_eq_of_lt (by omega)
    · show regValue (skywalkArithmeticNumerator base)
        (StairCodec.registerBasis (skywalkArithmeticDivisor base) x) = 0
      rw [regValue_zero]
      intro q hq
      apply rb_out
      intro hd
      unfold skywalkArithmeticNumerator at hq
      unfold skywalkArithmeticDivisor at hd
      obtain ⟨i, hi1, hi2, rfl⟩ := StairField2V3SegSpec.mem_wireBlock hq
      obtain ⟨j, hj1, hj2, he⟩ := StairField2V3SegSpec.mem_wireBlock hd
      have := base_injective he
      omega
    · intro q _ hd _
      exact rb_out _ _ _ hd
  exact ⟨_, FrontierEntry1591Native.caller_first_stageW base Six505.shared_nodup x 0 hx0 hx
    ⟨false, StairCodec.registerBasis (skywalkArithmeticDivisor base) x⟩ [] input⟩

/-- The record state after ticks `1 .. 504`: a stage at tick 505 placed by `sig 504`. -/
theorem rec505 (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)) 1 s1.basis)
    (m : List Bool) :
    ∃ ρ : BasisState, Rolling1588.Integer.Stage base true x ECDSAAdd.p 505 ρ ∧
      ∀ q, (run (Rolling1588TickGap.forward true 1 504) m s1).basis q = ρ (OB5.sig 504 q) := by
  refine ⟨_, StairExitLT24Term.stage_after x hx0 hx s1 first 504 (by omega) [], fun q => ?_⟩
  rw [StairExitLT24Term.fwd504 x hx0 hx s1 first m]
  exact StairExitLT24Term.pull_basis _ _ _

end ECDSAAdd.Entrant.StairField2V3LastStage

end
end Merge_StairField2V3LastStage_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3LastRec_at_BOptimizations` -/
section Merge_StairField2V3LastRec_at_BOptimizations

/-!
# LT43c: the record terminal blocks from tick 505 — closed form of the values

`G = run forwardRecord n (run (TickGap.forward true 1 504) m s1)` (record
coordinates, `s1` a stage-1 state of `x`) is the cleared sig-511 placement of the
A-encoded complete walk.  `rec_values` lists its values on the wires the moved
terminal reads back: the two last packets (= `recVal origin`), `g 510`, `g 511 = 1`,
the cleared rail words `base 512 .. 1027`, and the history letter `s 510` on
`base 1543` (the parity host).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3LastRec

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairPhysicalLayout StairField2V3Seg










/-- The record state after the terminal blocks (without the clear). -/
theorem rec_final (x : Nat) (hx0 : 0 < x) (hxp : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)) 1 s1.basis)
    (m mF : List Bool) :
    ∃ R : State, W.CompactSkywalkStage base
        (SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)) 512 R.basis ∧
      run StairExitLT24Term.fwdBlocks mF (run (Rolling1588TickGap.forward true 1 504) m s1) =
        pullState (OB5.sig 511) (run (Rolling1588.allEncode base true 102) [] R) := by
  obtain ⟨hp0, hpo, hp, cop⟩ := StackOB5.prime_facts x hx0 hxp
  have hgap : ECDSAAdd.p + 2 ^ 32 ≤ 2 ^ 256 := by norm_num [ECDSAAdd.p]
  refine ⟨run (W.compactSkywalkForward base 1 511) [] s1,
    (W.compactSkywalkForward_spec base base_pool_nodup x ECDSAAdd.p 1 511 hp0 hx0 hpo hp hgap hxp
      cop (by omega) s1 [] first).2, ?_⟩
  generalize hK : measurementCount (Rolling1588TickGap.forward true 1 504) = K
  have b := Rolling1588.stackForward_boundary true Six505.shared_nodup StackOB5.historyAbove
    x hx0 hxp s1 (List.replicate K false ++ mF) first
  rw [← Rolling1588TickGap.stackForward0_run_eq true x hx0 hxp s1 _ first,
    ← Six505.stackForward6_run_eq true x hx0 hxp s1 _ first] at b
  have e : Six505.stackForward6 true =
      Rolling1588TickGap.forward true 1 504 ++ StairExitLT24Term.fwdBlocks := by
    simp only [Six505.stackForward6, StairExitLT24Term.fwdBlocks, List.append_assoc]
  rw [e, run_append, hK, List.take_left' (by simp), List.drop_left' (by simp),
    StairExitLT24Term.fwd504 x hx0 hxp s1 first] at b
  rw [StairExitLT24Term.fwd504 x hx0 hxp s1 first m]
  exact b

/-- **Values of the record state after the terminal blocks and the clear.** -/
theorem rec_values (x : Nat) (origin : BasisState) (hx : TraceOK x origin) (s1 : State)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)) 1 s1.basis)
    (m n : List Bool) :
    (run StairTerminalV3.forwardRecord n
        (run (Rolling1588TickGap.forward true 1 504) m s1)).phase =
      (run (Rolling1588TickGap.forward true 1 504) m s1).phase ∧
    (∀ k ∈ ([100, 101] : List Nat), ∀ i : Fin 10,
      (run StairTerminalV3.forwardRecord n
        (run (Rolling1588TickGap.forward true 1 504) m s1)).basis
          (StairField2V3Packet.packetSite k i) =
        recVal origin (StairField2V3Packet.packetSite k i)) ∧
    (run StairTerminalV3.forwardRecord n
      (run (Rolling1588TickGap.forward true 1 504) m s1)).basis (base 510) = origin (base 510) ∧
    (run StairTerminalV3.forwardRecord n
      (run (Rolling1588TickGap.forward true 1 504) m s1)).basis (base 511) = true ∧
    (∀ id, 512 ≤ id → id < 1028 →
      (run StairTerminalV3.forwardRecord n
        (run (Rolling1588TickGap.forward true 1 504) m s1)).basis (base id) = false) ∧
    (run StairTerminalV3.forwardRecord n
      (run (Rolling1588TickGap.forward true 1 504) m s1)).basis (base 1543) =
        origin (base 1538) := by
  have hx0 : 0 < x := hx.1
  have hxp : x < ECDSAAdd.p := hx.2.1
  obtain ⟨hp0, hpo, hp, cop⟩ := StackOB5.prime_facts x hx0 hxp
  have hgap : ECDSAAdd.p + 2 ^ 32 ≤ 2 ^ 256 := by norm_num [ECDSAAdd.p]
  have eFR : StairTerminalV3.forwardRecord =
      StairExitLT24Term.fwdBlocks ++ skywalkTerminalClear (base 511) (base 512) (base 770) := rfl
  obtain ⟨R, st, hF⟩ := rec_final x hx0 hxp s1 first m
    (n.take (measurementCount StairExitLT24Term.fwdBlocks))
  obtain ⟨cp, ce, ca, cb⟩ := skywalkTerminalClear_correct (base 511) (base 512) (base 770)
    (by decide) (pullState (OB5.sig 511) (run (Rolling1588.allEncode base true 102) [] R))
    (n.drop (measurementCount StairExitLT24Term.fwdBlocks))
  rw [eFR, run_append, hF]
  -- the raw stage at tick 512
  obtain ⟨-, -, -, rpast, -, -, -, -, -⟩ :=
    (W.compactSkywalkStage_fields_iff base _ 512 (by omega) base_pool_nodup R.basis).mp st
  have tw := (Arithmetic.compactSkywalkStage_terminal base base_pool_nodup x ECDSAAdd.p hp0 hx0 hpo
    hp hxp cop _ ((W.compactSkywalkStage_eq base _ 512
      W.narrowSkywalkRouteWidth_endpoints.2.2.1 _).mp st)).2
  obtain ⟨wa, wb⟩ := DirectSkywalk.arith_terminal_words base x hx0 hxp R.basis tw
  have R511 : R.basis (base 511) = true := (rpast 511 (by omega)).1.trans (code511 x hx0 hxp)
  rw [R511, if_pos rfl] at wa wb
  have za : ∀ id, 512 ≤ id → id < 770 → R.basis (base id) = false := fun id h1 h2 =>
    (regValue_zero _ _).mp wa _
      (List.mem_map.mpr ⟨id, List.mem_range'_1.mpr ⟨h1, by omega⟩, rfl⟩)
  have eB : wireBlock base 770 258 = base 770 :: wireBlock base 771 257 := rfl
  rw [eB] at wb
  obtain ⟨b770, zb'⟩ := reg_one _ _ _ wb
  have zb : ∀ id, 771 ≤ id → id < 1028 → R.basis (base id) = false := fun id h1 h2 =>
    zb' _ (List.mem_map.mpr ⟨id, List.mem_range'_1.mpr ⟨h1, by omega⟩, rfl⟩)
  have avoid : ∀ id, (510 ≤ id ∧ id < 1028) ∨ 1538 ≤ id →
      (run (Rolling1588.allEncode base true 102) [] R).basis (base id) = R.basis (base id) :=
    fun id h => run_preserves_outside _ _ _ _
      (StairField2V3SegSpec.allEncode_avoid base base_injective 102 id (by omega))
  have F0 : ∀ id, 510 ≤ id → id < 1028 →
      (pullState (OB5.sig 511) (run (Rolling1588.allEncode base true 102) [] R)).basis (base id) =
        R.basis (base id) := by
    intro id h1 h2
    rw [StairExitLT24Term.pull_basis, sig_low id h2]
    exact avoid id (Or.inl ⟨h1, h2⟩)
  have ne512 : ∀ id, id ≠ 512 → base id ≠ base 512 := fun id h e => h (base_injective e)
  have ne770 : ∀ id, id ≠ 770 → base id ≠ base 770 := fun id h e => h (base_injective e)
  have hp1 := ((Rolling1588.Integer.regularForward_spec base true base_pool_nodup
    StackOB5.historyAbove x ECDSAAdd.p 1 504 hp0 hx0 hpo hp hgap hxp cop (by omega)) s1 []
    (Rolling1588.Integer.stage_one base true x ECDSAAdd.p s1 first)).1
  have hp2 := fun M => ((Rolling1588.Integer.regularForward_spec base true base_pool_nodup
    StackOB5.historyAbove x ECDSAAdd.p 1 511 hp0 hx0 hpo hp hgap hxp cop (by omega)) s1 M
    (Rolling1588.Integer.stage_one base true x ECDSAAdd.p s1 first)).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cp, ← hF, StairExitLT24Term.fwd_terminal x hx0 hxp s1 first m,
      StairExitLT24Term.fwd504 x hx0 hxp s1 first m]
    rw [StairExitLT24.pull_phase, StairExitLT24.pull_phase]
    exact (hp2 _).trans hp1.symm
  · intro k hk i
    obtain ⟨n1, n2⟩ := pk_off k hk i
    rw [ce _ n1 n2]
    have hk' : k < 102 ∧ 5 * k + 5 ≤ 512 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl <;> omega
    have hmem : History5.historyMap base (5 * k) i ∈ wires (Rolling1588.encodeGroup base true k) :=
      Rolling1588.history_site_mem base true k i
    have agree : ∀ q ∈ wires (Rolling1588.encodeGroup base true k),
        R.basis q = (⟨false, origin⟩ : State).basis q := by
      intro q hq
      rw [Rolling1588.encodeGroup_support_eq] at hq
      obtain ⟨j, rfl⟩ := NewHistory5.history_gate_mem base (5 * k) _ (Or.inl rfl) _ hq
      exact raw_packet_base x origin hx R.basis rpast k hk'.2 j
    have loc := (run_local_increment (Rolling1588.encodeGroup base true k) R ⟨false, origin⟩ []
      agree).2 _ hmem
    rw [StairExitLT24Term.pull_basis]
    rw [recVal_defLR]
    rw [show StairField2V3Packet.packetSite k i = OB5.sig 511 (History5.historyMap base (5 * k) i) from rfl]
    rw [OB5.sig_invol 511 (by decide),
      StairField2V3Trace.allEncode_packet base base_pool_nodup k 102 hk'.1 (by omega) R _ hmem,
      StairField2V3Trace.allEncode_packet base base_pool_nodup k 102 hk'.1 (by omega) _ _ hmem]
    exact loc
  · rw [ce _ (ne512 510 (by omega)) (ne770 510 (by omega)), F0 510 (by omega) (by omega),
      (rpast 510 (by omega)).1]
    exact (StairField2V3Trace.origin_letters x origin hx 510 (by omega)).1.symm
  · rw [ce _ (ne512 511 (by omega)) (ne770 511 (by omega)), F0 511 (by omega) (by omega)]
    exact R511
  · intro id h1 h2
    have f511 : (pullState (OB5.sig 511) (run (Rolling1588.allEncode base true 102) [] R)).basis (base 511) = true :=
      (F0 511 (by omega) (by omega)).trans R511
    by_cases e1 : id = 512
    · subst e1
      have h := ca
      rw [F0 512 (by omega) (by omega), f511, za 512 (by omega) (by omega)] at h
      exact h.trans rfl
    · by_cases e2 : id = 770
      · subst e2
        have h := cb
        rw [F0 770 (by omega) (by omega), f511, b770] at h
        exact h.trans rfl
      · rw [ce _ (ne512 id e1) (ne770 id e2), F0 id (by omega) h2]
        by_cases h3 : id < 770
        · exact za id h1 h3
        · exact zb id (by omega) h2
  · have n1 : base 1543 ≠ base 512 := fun e => absurd (base_injective e) (by omega)
    have n2 : base 1543 ≠ base 770 := fun e => absurd (base_injective e) (by omega)
    rw [ce _ n1 n2]
    rw [StairExitLT24Term.pull_basis, sig_host, avoid 1538 (Or.inr (by omega))]
    exact ((rpast 510 (by omega)).2).trans
      (StairField2V3Trace.origin_letters x origin hx 510 (by omega)).2.symm

end ECDSAAdd.Entrant.StairField2V3LastRec

end
end Merge_StairField2V3LastRec_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitRec_at_BOptimizations` -/
section Merge_StairField2V3ExitRec_at_BOptimizations

/-!
# LT43d: record facts of the multiplication (exit) side of field 2

Mirror of LT42's `StairField2V3RecScratch` on the exit side.  After the reference
opening (`ExitMiddleX k x`), the head `headE` and the packet groups in the
multiplication direction down to a cut `c`, the field view of the actual state
agrees off `EP = E ∪ payload0` with a placed record state whose kernel view carries
the record `Rolling1588.CutFrame c origin X Y` (`InvE x c`).  The frame's `origin`
is the forced record preparation state of the input `x` (`TraceOK x origin`).

On a `CutFrame c` the packets `≥ c` are A-encoded, exactly as in
`recVal origin` (`frame_val`: `allEncodeCut c` and `allEncode true` agree off the
history ids of the packets `< c`; the raw state agrees with `origin` off the r/y
words), and the scratch is zero (`StairField2V3RecScratch.frame_zero`).

Sections "Exit helpers" are verbatim copies of LT32's helpers
(`StairLoanField7Values`, which is not in this tree).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3ExitRec

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR StairField2V3ExitStepsR
open StairField2V3RecScratch
open StairPhysicalLayout StairOuterPlacement

attribute [local irreducible] wires run

/-! ## Exit helpers (LT32) -/



/-! ## Pieces of the record head -/





/-! ## The exit invariant -/




/-- **The invariant at the head**: after `headE` the cut is 100; LT47: and the packet-0
controls hold the window image of the canonical frame (`WinT`). -/
theorem inv_head_w (k x : Nat) (t0 : State) (h0 : ExitMiddleX k x t0) (m : List Bool) :
    InvE x 100 (run headE m t0) ∧ StairField2V3Win.WinT x (run headE m t0) := by
  obtain ⟨s, f, rfl, records, rfl⟩ := h0
  have opening : run StairField2V3Replay.exitReferenceOpening records s =
      run (Rolling1588.firstPhase false) records s :=
    first_phase_hosted false f.sharedNodup f.historyAbove f.x f.Y.val f.x_pos f.x_lt s
      records f.input
  rw [opening]
  obtain ⟨origin, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
    f.sharedNodup f.historyAbove f.selectorsAway f.x f.Y f.x_pos f.x_lt s records f.input
  have ctx := Rolling1588Lifetime.prepared_context f.sharedNodup f.selectorsAway
    f.transcript f.x f.Y s origin facts legal f.selectorG_zero f.selectorS_zero
  have bits := Rolling1588Lifetime.first_clean false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  have work := Rolling1588Lifetime.first_work_zero false f.sharedNodup f.x f.Y.val s
    records f.input
  have parity := Rolling1588Lifetime.first_parity false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  have input := frames false
  rw [lf_eq] at input bits work parity
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) records s = v := ⟨_, rfl⟩
  rw [hv] at input bits work parity
  rw [hv]
  have code := Rolling1588Frame.canonical_special_at origin.basis f.Y 0 v 511 (by simp) input
  have fixed : OB5.sig 511 (base 511) = base 511 := by decide +kernel
  rw [fixed] at code
  have in511 : v.basis (base 511) = true :=
    code.trans (trace_last f.x f.x_pos f.x_lt origin.basis facts.trace)
  have in1542 : v.basis (base 1542) = false :=
    bits _ (by simp [FrontierEntry1591Native.workSites])
  have flags := canonical_flags origin.basis ctx f.Y 0 v input
  -- the forced record frame
  let origin' := writeBit origin.basis (base 2400) true
  have ctx' := FrontierEntry1591.context_control_set origin.basis ctx true
  have ha' := FrontierEntry1591.source_zero_control_set origin.basis true facts.sourceZero
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (f.x : Int) (p : Int)) := by
    rw [FrontierEntry1591.trace_control_set]
    exact facts.trace
  have input' := Rolling1588.canonical_control_set origin.basis f.Y 0 v true input
  have enabled' : origin' (base 2400) = true := by
    simp only [origin', writeBit, Function.update_self]
  have codes := Rolling1588.canonical_prefix_codes origin' ctx' f.Y 0 (force v) input'
    f.x f.x_pos f.x_lt trace'
  have clean := FourScratchWindow.canonical_clean origin' ctx' ha' f.Y (force v) input'
    codes.1 codes.2.1
  have z768 := Rolling1588.canonical_768_zero origin' ctx' f.Y 0 (force v) input'
  -- split the head
  have core : ∀ m1, InvE f.x 102 (run (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram ++ liftF headCore) m1 v) ∧
      StairField2V3Win.WinT f.x (run (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram ++ liftF headCore) m1 v) := by
    intro m1
    rw [run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram) (liftF headCore)]
    generalize m1.take (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram)) = mA
    generalize m1.drop (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
        StairSchedule.fieldRename FourScratchWindow.clearProgram)) = mB
    obtain ⟨X', Y', cut⟩ := headCore_frame origin' ctx' ha' enabled' f.Y (force v) input' mB
    refine ⟨⟨origin', X', Y', run headCore mB (force v), ctx', enabled',
      ⟨f.x_pos, f.x_lt, trace', ctx'.legal⟩, ha', cut, ?_⟩, ?_⟩
    · intro q hq
      rw [pullIn_liftF]
      refine run_agree_offP _ headCore_off _ _ mB ?_ q hq
      intro r hr
      rw [run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX), field_pullIn]
      exact window_agree _ (force v) _
        (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity _)
        clean codes.2.2 z768 r hr.1 hr.2
    · refine StairField2V3Win.winT_lift f.x headCore headCore_off mB _
        ⟨force v, 102, origin', X', Y', run headCore mB (force v), clean, codes.2.2, ctx',
          ⟨f.x_pos, f.x_lt, trace', ctx'.legal⟩, cut, ?_, ?_⟩
      · intro i
        exact run_preserves_outside _ _ _ _
          (fun hq => (headCore_off _ hq).2 i (StairField2V3Win.pctrl_payload0 i))
      · intro i hi
        rw [run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX), field_pullIn]
        exact StairField2V3Win.window_payload _ (force v) _
          (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity _) clean codes.2.2 i hi
  rw [headE_shape,
    run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram ++ liftF headCore) (grpF 100 2)]
  have c := core (m.take (measurementCount (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram ++ liftF headCore)))
  refine ⟨inv_stepE f.x 100 2 (by norm_num) (by norm_num) _ c.1 _, ?_⟩
  unfold grpF
  exact StairField2V3Win.winT_lift f.x _ (groupsF_off 100 2 (by norm_num) (by norm_num)) _ _ c.2

theorem inv_head (k x : Nat) (t0 : State) (h0 : ExitMiddleX k x t0) (m : List Bool) :
    InvE x 100 (run headE m t0) :=
  (inv_head_w k x t0 h0 m).1

/-! ## Reachability: the cut along the reference prefixes -/

theorem reach_head (k x : Nat) (t : State) (h : ReachE k x headE t) : InvE x 100 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  exact inv_head k x s0 hs0 m

theorem reach_YA (k x : Nat) (t : State) (h : ReachE k x YA t) : InvE x 98 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold YA
  rw [run_append headE (grpF 98 2)]
  exact inv_stepE x 98 2 (by norm_num) (by norm_num) _ (reach_head k x _ ⟨s0, _, hs0, rfl⟩) _

theorem reach_YB (k x : Nat) (t : State) (h : ReachE k x YB t) : InvE x 96 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold YB
  rw [run_append YA (grpF 96 2)]
  exact inv_stepE x 96 2 (by norm_num) (by norm_num) _ (reach_YA k x _ ⟨s0, _, hs0, rfl⟩) _

theorem reach_YC (k x : Nat) (t : State) (h : ReachE k x YC t) : InvE x 93 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold YC
  rw [run_append YB (grpF 93 3)]
  exact inv_stepE x 93 3 (by norm_num) (by norm_num) _ (reach_YB k x _ ⟨s0, _, hs0, rfl⟩) _

theorem reach_YD (k x : Nat) (t : State) (h : ReachE k x YD t) : InvE x 90 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold YD
  rw [run_append YC (grpF 90 3)]
  exact inv_stepE x 90 3 (by norm_num) (by norm_num) _ (reach_YC k x _ ⟨s0, _, hs0, rfl⟩) _

theorem reach_YE (k x : Nat) (t : State) (h : ReachE k x YE t) : InvE x 85 t := by
  obtain ⟨s0, m, hs0, rfl⟩ := h
  unfold YE
  rw [run_append YD (grpF 85 5)]
  exact inv_stepE x 85 5 (by norm_num) (by norm_num) _ (reach_YD k x _ ⟨s0, _, hs0, rfl⟩) _


/-! ## Values on a `CutFrame`: packets `≥ c` are A-encoded -/







/-! ## Site facts of the invariant (arbitrary sites) -/





/-! ## The record facts of the rows -/



theorem rowRec (k x B B' c : Nat) (Y : Program) (hc : c ≤ 102) (vf : ValFacts B c)
    (rf : RecFacts B B') (h : ∀ t, ReachE k x Y t → InvE x c t) : RowRecE k x B B' Y := by
  intro t ht
  obtain ⟨origin, tr, hv, hz⟩ := vals_of_inv x B c hc vf t (h t ht)
  exact ⟨origin, tr, hv, fun r hr => hz r (rf r hr).1 (rf r hr).2⟩


theorem rr4 : ∀ k x, RowRecE k x 22 12 YA := fun k x =>
  rowRec k x 22 12 98 YA (by norm_num) valFacts4 recFacts4 (reach_YA k x)

theorem rr3 : ∀ k x, RowRecE k x 32 22 YB := fun k x =>
  rowRec k x 32 22 96 YB (by norm_num) valFacts3 recFacts3 (reach_YB k x)

theorem rr2 : ∀ k x, RowRecE k x 47 32 YC := fun k x =>
  rowRec k x 47 32 93 YC (by norm_num) valFacts2 recFacts2 (reach_YC k x)

theorem rr1 : ∀ k x, RowRecE k x 62 47 YD := fun k x =>
  rowRec k x 62 47 90 YD (by norm_num) valFacts1 recFacts1 (reach_YD k x)

theorem rr0 : ∀ k x, RowRecE k x 87 62 YE := fun k x =>
  rowRec k x 87 62 85 YE (by norm_num) valFacts0 recFacts0 (reach_YE k x)



end ECDSAAdd.Entrant.StairField2V3ExitRec

end
end Merge_StairField2V3ExitRec_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3Final_at_BOptimizations` -/
section Merge_StairField2V3Final_at_BOptimizations

/-!
# LT43: field 2 from one explicit list of obligations

`Field2Obligations` lists every remaining statement of field 2 on CANON v3
(division: LT21's `EntryPlanV3d` with the row-425 junction in generic form;
multiplication: `ExitPlanR` through `exitPlanR_of`).  Everything else is proved:
the coupled chains, all group/first-packet/low-tail avoidance facts, LT24's record
round trip `close_record_trip` (row 425), the mirror `rspec_of_spec`, the
uniqueness of selected partners, and the exit junction from the division last step.

Obligations, by kind:
* pure staircase (tail coordinates, no record state): `spec0..4` (`SegSpecT`, LT42),
  `trip0..4` (`RowTripT`, e.g. LT24 `rowTripT_of`), `lastSpec`, `lastTrip`
  (e.g. `lastTrip_of` + LT24 `termTrip_final`), `firstTrip` (LT24 `firstTrip`);
* the generic row-425 junction `junc` (selected first pack vs record walk end on any
  admissible tick-424 state; split into a selected and a record half by
  `junctionG_of_split`);
* record facts (division): `rec0..4` (`RecordScratch`, LT42), `lastRec`, `adm`;
* record facts (multiplication): `juncRec`, `rr0..4`, `closeRec`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3Final

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR StairField2V3ExitStepsR
open StairPhysicalLayout StairOuterPlacement


/-- Admissible states at the row-425 junction for input `x`: the phase-hosted record
walk after ticks `1..424` from a stage-1 state of `x`, plus an extra predicate
`Extra x` chosen by the junction proof. -/
def Adm (Extra : Nat → State → Prop) (x : Nat) (t0 : State) : Prop :=
  0 < x ∧ x < ECDSAAdd.p ∧ Extra x t0 ∧ ∃ (s1 : State) (m : List Bool),
    W.CompactSkywalkStage base (SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)) 1
      s1.basis ∧
    pullState Rolling1588Lifetime.phaseHost t0 = run (Rolling1588TickGap.forward true 1 424) m s1







/- LT47: the unpinned exit junction was removed: on the defect-2-fixed program the
selected setup sits between two windows and is not an unconditional involution; the
pinned junction is `StairField2V3Field2R.junctionRX`. -/

end ECDSAAdd.Entrant.StairField2V3Final

end
end Merge_StairField2V3Final_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3ExitRecClose_at_BOptimizations` -/
section Merge_StairField2V3ExitRecClose_at_BOptimizations

/-!
# LT43d: the multiplication reference state at row 425 (`YF`) in closed form

The reference state `t` after `YF` (all multiplication groups and `lowTail`) is the
state inside the record's hosted exit field just before the closing `X`/parity
wrapper: `YF ++ XS = Rolling1588.exitFieldHosted` (`YF_XS`).  By the record's
`Rolling1588.exit_boundary`, the state after the whole hosted exit field is the
division first phase `run (firstPhase true) mp s` of the same caller state `s`
except on the numerator word (`wireBlock base 2056 256`), which holds
`centerWord (Y * x / 2)`.  The first phase does not touch the numerator, so that
state is the division first phase of the division input `s'` (= `s` with the new
numerator): an `EntryFrame` state with the same `x`.  Since
`prefixW ++ refJ0 = ph (TickGap.firstPhase true) ++ SX` and `SX` is an involution
equal to `XS`,

  `t = run refJ0 c1 (run prefixW c0 s')`   (`close_form`),

i.e. `t` is the `refJ0` image of a `Reach prefixW` state, which is admissible
(`closeRec_true`, for `Extra := fun _ _ => True`).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3ExitRecClose

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR StairField2V3ExitStepsR
open StairField2V3RecScratch StairField2V3Final
open StairPhysicalLayout StairOuterPlacement

attribute [local irreducible] wires run

/-! ## Shapes -/


theorem R0_eq : prefixW ++ refJ0 =
    ph (Rolling1588TickGap.firstPhase true) ++ StairExitLT24.SX := by
  simp only [prefixW, refJ0, ph, StairExitLT24.SX, Rolling1588TickGap.firstPhase,
    Rolling1588TickGap.tailPhase, Rolling1588TickGap.stackForward, Six505.stackForward6,
    forward_504, rename_append', List.append_assoc]

/-! ## A register can be given any value -/



/-! ## The closed form -/


/-! ## Admissibility -/

/-- The `prefixW` image of a division input is an admissible tick-424 state, for any
extra predicate that holds on such images. -/
theorem adm_frame (Extra : Nat → State → Prop)
    (hE : ∀ (s' : State) (f' : StairConcreteAssembly.EntryFrame s') (c0 : List Bool),
      Extra f'.x (run prefixW c0 s'))
    (s' : State) (f' : StairConcreteAssembly.EntryFrame s') (c0 : List Bool) :
    Adm Extra f'.x (run prefixW c0 s') := by
  have input := FrontierEntry1591Kernel.paired_input f'.x f'.Y.val f'.source s' f'.input
    f'.outsideNumerator
  refine ⟨f'.x_pos, f'.x_lt, hE s' f' c0,
    run (FrontierEntry1591Native.forward base)
      (c0.take (measurementCount (FrontierEntry1591Native.forward base))) s',
    c0.drop (measurementCount (FrontierEntry1591Native.forward base)), ?_, ?_⟩
  · exact FrontierEntry1591Native.caller_first_stageW base f'.sharedNodup f'.x _ f'.x_pos
      f'.x_lt s' _ input
  · unfold prefixW ph
    rw [ECDSAAdd.run_rename _ Rolling1588Lifetime.phaseHost.injective,
      Rolling1588Lifetime.pull_phase_clean s'
        (Rolling1588Lifetime.caller_phase_clean f'.x _ s' input),
      run_append (FrontierEntry1591Native.forward base)]






end ECDSAAdd.Entrant.StairField2V3ExitRecClose

end
end Merge_StairField2V3ExitRecClose_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3JuncRecord_at_BOptimizations` -/
section Merge_StairField2V3JuncRecord_at_BOptimizations

/-!
# LT43: record half of the row-425 junction — first reductions

* `refJ0_split`: `refJ0` = the phase-hosted record walk end `RW` (`ticks 425..504` +
  record terminal + clear) followed by the setup/X pair `SX` (measurement free).
* `refJ0_record`: on an admissible state the phase-hosted part is the clear applied
  to the complete record forward walk `Rolling1588.stackForward true` of the stage-1
  state (whose closed form is `Rolling1588.stackForward_boundary`).
* `host_off`, `x511_off`, `sel_off`: the parity host `base 1543`, `base 511` and the
  selector `base 2409` are outside `Δv 87`, so the record half of the junction must
  return them to their tick-424 values.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3JuncRecord

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR StairField2V3Final
open StairPhysicalLayout StairOuterPlacement

/-- The phase-hosted part of `refJ0`: record ticks `425..504`, record terminal blocks, clear. -/
def RW : Program :=
  Rolling1588TickGap.forward true 425 80 ++
    (Six505.merged6 ++ (Six505.packP true ++ ForwardSixPlacement.after true)) ++
    skywalkArithmeticClear base

theorem refJ0_eq' : refJ0 = ph RW ++ StairExitLT24.SX := by
  simp only [refJ0, RW, StairExitLT24.SX, List.append_assoc]

theorem refJ0_split (c : List Bool) (t0 : State) :
    ∃ c1, run refJ0 c t0 = run StairExitLT24.SX [] (run (ph RW) c1 t0) := by
  rw [refJ0_eq', run_append,
    StairField2V3ExitRowTrips.run_noMeas_any _ StairExitLT24.SX_measurements]
  exact ⟨_, rfl⟩

theorem walkEnd_eq :
    Rolling1588TickGap.forward true 1 424 ++ RW =
      Six505.stackForward6 true ++ skywalkArithmeticClear base := by
  rw [Six505.stackForward6, forward_504]
  simp only [RW, List.append_assoc]

theorem refJ0_record (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base
      (SkywalkRails.encode false false (x : Int) (ECDSAAdd.p : Int)) 1 s1.basis)
    (m : List Bool) (t0 : State)
    (ht : pullState Rolling1588Lifetime.phaseHost t0 = run (Rolling1588TickGap.forward true 1 424) m s1)
    (c : List Bool) :
    ∃ c1 c2, pullState Rolling1588Lifetime.phaseHost (run (ph RW) c t0) =
      run (skywalkArithmeticClear base) c2 (run (Rolling1588.stackForward true) c1 s1) := by
  have e := ECDSAAdd.run_rename Rolling1588Lifetime.phaseHost
    Rolling1588Lifetime.phaseHost.injective RW c t0
  rw [ht, nested_run_eq_append, walkEnd_eq, run_append,
    Six505.stackForward6_run_eq true x hx0 hx s1 _ first,
    Rolling1588TickGap.stackForward0_run_eq true x hx0 hx s1 _ first] at e
  exact ⟨_, _, e⟩




end ECDSAAdd.Entrant.StairField2V3JuncRecord

end
end Merge_StairField2V3JuncRecord_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3JuncRefWalk_at_BOptimizations` -/
section Merge_StairField2V3JuncRefWalk_at_BOptimizations

/-!
# LT43b: the record walk in closed form at tick 424 and at its end

For a stage-1 state `s1` of the input `x` (no other assumption on `s1`):

* `walk424`: the record ticks `1..424` give
  `pullState (sig 424) (allEncode 84 (raw425 s1))`, `raw425 s1` = the raw compact walk
  after 424 ticks (a `CompactSkywalkStage 425`);
* the complete record walk gives `pullState (sig 511) (allEncode 102 (raw512 s1))`
  (record `stackForward_boundary`), `raw512 s1 = ` 87 more raw ticks;
* per-id values of `raw425`, `raw512` and of the cleared raw end `rawEnd s1`
  (`origin` of the junction) on the 1798 pool ids, and the frame off the pool;
* the encoders: `allEncode 102` versus `allEncode 84` off the packets `84..101`,
  holes, and the link to `recVal`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3JuncRefWalk

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1
open StairField2V3Seg StairField2V3SegSpec



/-! The five states are *notations* (explicit `run` terms), not definitions: a
definition would have to be unfolded under `State.basis _ q`, and such a
conversion makes Lean evaluate the concrete walk (70 GB). -/

/- The raw compact walk after ticks `1..424`. -/
/- The raw compact walk after ticks `1..511`. -/
/- The cleared raw walk end: its basis is the `origin` of the junction. -/
/- The encoded walk state at tick 424 (before the `sig 424` placement). -/
/- The encoded walk end (before the `sig 511` placement). -/




/-! ## Small tools -/








/-! ## Generic program shapes (before the concrete programs are sealed) -/



theorem clear_spec (s : State) (m : List Bool) :
    (run (skywalkArithmeticClear base) m s).phase = s.phase ∧
    (∀ q, q ≠ base 512 → q ≠ base 770 →
      (run (skywalkArithmeticClear base) m s).basis q = s.basis q) ∧
    (run (skywalkArithmeticClear base) m s).basis (base 512) =
      (!(s.basis (base 512) ^^ s.basis (base 511))) ∧
    (run (skywalkArithmeticClear base) m s).basis (base 770) =
      (s.basis (base 770) ^^ s.basis (base 511)) :=
  skywalkTerminalClear_correct _ _ _ (DirectSkywalk.arith_clear_gates base Six505.shared_nodup) s m

attribute [local irreducible] run wires W.compactSkywalkForward Rolling1588TickGap.forward Rolling1588.stackForward Rolling1588.allEncode Rolling1588.encodeGroup Rolling1588.Integer.regularForward Rolling1588.Integer.compactForward Rolling1588.Integer.encodePrefix skywalkArithmeticClear


/-! ## Closed forms -/



/-- Record ticks `1..424` in closed form. -/
theorem walk424 (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base (rails x) 1 s1.basis) (m : List Bool) :
    run (Rolling1588TickGap.forward true 1 424) m s1 = pullState (OB5.sig 424) ((run (Rolling1588.allEncode base true 84) [] (run (W.compactSkywalkForward base 1 424) [] s1))) := by
  obtain ⟨hp0, hpo, hp, cop⟩ := StackOB5.prime_facts x hx0 hx
  have st1 := Rolling1588.Integer.stage_one base true x ECDSAAdd.p s1 first
  have start : pullState (OB5.sig (1 - 1)) s1 = s1 := by
    apply State.extensionality
    · rfl
    · funext q
      change s1.basis (OB5.sig 0 q) = s1.basis q
      rw [OB5.sig_zero]
  have h := Rolling1588TickGap.forward_gen true x hx0 hx 424 1 le_rfl (by norm_num) s1 m st1
  have g : run (Rolling1588TickGap.forward true 1 424) m s1 =
      pullState (OB5.sig 424) (run (Rolling1588.Integer.regularForward base true 1 424) m s1) :=
    (congrArg (fun t => run (Rolling1588TickGap.forward true 1 424) m t) start.symm).trans h
  have e1 := Rolling1588.Integer.regularForward_eq base true base_pool_nodup StackOB5.historyAbove
    x ECDSAAdd.p hp0 hx0 hpo hp gap hx cop 424 1 (by norm_num) s1 m [] st1
  have nrm := norm_gen base base_pool_nodup 424 (by norm_num) s1
  have pre : Rolling1588.Integer.encodePrefix base true (1 + 424) =
      Rolling1588.allEncode base true 84 :=
    StairField2V3Trace.encodePrefix_boundary base 84
  exact g.trans (congrArg (pullState (OB5.sig 424))
    (e1.trans (nrm.trans (congrArg (fun P => run P [] ((run (W.compactSkywalkForward base 1 424) [] s1))) pre))))

/-- The complete record walk in closed form. -/
theorem walk511 (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base (rails x) 1 s1.basis) (m : List Bool) :
    run (Rolling1588.stackForward true) m s1 = pullState (OB5.sig 511) ((run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1))) :=
  Rolling1588.stackForward_boundary true Six505.shared_nodup StackOB5.historyAbove x hx0 hx s1 m
    first

/-! ## Frames off the pool -/



/-! ## Encoder supports -/








/-! ## Values of the raw walk states on the pool -/








/-! ## The cleared raw end -/


/-- After the clear both rails are zero (ids `512..1027`). -/
theorem rawEnd_zero (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base (rails x) 1 s1.basis) (j : Nat)
    (h : 512 ≤ j ∧ j < 1028) : ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis (base j) = false := by
  have words := DirectSkywalk.arith_clear_words base Six505.shared_nodup x hx0 hx ((run (W.compactSkywalkForward base 1 511) [] s1)) []
    (integer512 x hx0 hx s1 first)
  by_cases h2 : j < 770
  · exact (regValue_zero _ _).mp words.1 _ (block_mem 512 258 j h.1 (by omega))
  · exact (regValue_zero _ _).mp words.2 _ (block_mem 770 258 j (by omega) (by omega))

theorem rawEnd_keep (s1 : State) (j : Nat) (h1 : j ≠ 512) (h2 : j ≠ 770) :
    ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis (base j) = ((run (W.compactSkywalkForward base 1 511) [] s1)).basis (base j) :=
  (clear_spec ((run (W.compactSkywalkForward base 1 511) [] s1)) []).2.1 _ (fun e => h1 (base_injective e)) (fun e => h2 (base_injective e))


/-- The cleared raw end carries the transcript of `x`. -/
theorem traceOK (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base (rails x) 1 s1.basis) :
    TraceOK x ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis := by
  obtain ⟨hp0, hpo, -, -⟩ := StackOB5.prime_facts x hx0 hx
  refine ⟨hx0, hx, ?_, ?_⟩
  · exact (DirectSkywalk.arith_tape_clear base Six505.shared_nodup ((run (W.compactSkywalkForward base 1 511) [] s1)) []).trans
      (DirectSkywalk.arith_tape base x _ (integer512 x hx0 hx s1 first))
  · have legal : NewHistory5.RawLegal base 102 ((run (W.compactSkywalkForward base 1 511) [] s1)).basis := by
      intro j hj
      exact W.stage_group_legal base base_pool_nodup x ECDSAAdd.p 512 (5 * j) hp0 hpo (by omega)
        (by decide) _ (stage512 x hx0 hx s1 first).2
    have keep (j : Nat) (hj : j < 102) (u : Fin 10) :
        ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis (History5.historyMap base (5 * j) u) =
          ((run (W.compactSkywalkForward base 1 511) [] s1)).basis (History5.historyMap base (5 * j) u) := by
      have r := hist_range j u
      exact rawEnd_keep s1 _ (by omega) (by omega)
    intro j hj
    apply (MeasuredCodec5.legalAt_iff _ _).mpr
    intro u
    rw [keep j hj ⟨2 * u.val, by omega⟩, keep j hj ⟨2 * u.val + 1, by omega⟩]
    exact (MeasuredCodec5.legalAt_iff _ _).mp (legal j hj) u

/-! ## The encoded states -/

/-- `allEncode 102` of the raw end and of the cleared raw end agree off `512`, `770`. -/
theorem encEnd (s1 : State) (r : Wire) (h1 : r ≠ base 512) (h2 : r ≠ base 770) :
    (run (Rolling1588.allEncode base true 102) [] ⟨false, ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis⟩).basis r =
      ((run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis r := by
  have agree : ∀ q ∈ wires (Rolling1588.allEncode base true 102),
      (⟨false, ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis⟩ : State).basis q = ((run (W.compactSkywalkForward base 1 511) [] s1)).basis q := by
    intro q hq
    obtain ⟨j, hj, i, rfl⟩ := enc_mem 102 q hq
    have r := hist_range j i
    exact (mk_basis _ _ _).trans (rawEnd_keep s1 _ (by omega) (by omega))
  by_cases hw : r ∈ wires (Rolling1588.allEncode base true 102)
  · exact (ECDSAAdd.Arithmetic.run_local_increment _ _ _ [] agree).2 r hw
  · exact (run_preserves_outside _ _ _ r hw).trans ((mk_basis _ _ _).trans
      (((clear_spec ((run (W.compactSkywalkForward base 1 511) [] s1)) []).2.1 r h1 h2).trans (run_preserves_outside _ _ _ r hw).symm))



/-- The final encoded state is the record value `recVal` of the cleared raw end. -/
theorem enc102_recVal (s1 : State) (q : Wire) (h1 : q ≠ base 512) (h2 : q ≠ base 770) :
    ((run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis (OB5.sig 511 q) = recVal ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis q := by
  rw [recVal_defJW]
  have f1 : OB5.sig 511 (base 512) = base 512 := sig_fix 511 le_rfl 512 (by omega)
  have f2 : OB5.sig 511 (base 770) = base 770 := sig_fix 511 le_rfl 770 (by omega)
  exact (encEnd s1 _ (fun e => h1 (OB5.sig_injective 511 (by norm_num) (e.trans f1.symm)))
    (fun e => h2 (OB5.sig_injective 511 (by norm_num) (e.trans f2.symm)))).symm



/-! ## Zero classes of the encoded states -/



/-- Sites that are zero in the final encoded state: both rails except their two
low bits handled by the clear, and the carry. -/
theorem enc102_zero (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base (rails x) 1 s1.basis) (j : Nat)
    (h : (513 ≤ j ∧ j < 770) ∨ (771 ≤ j ∧ j < 1028) ∨ (1540 ≤ j ∧ j < 1798)) :
    ((run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis (base j) = false := by
  rw [enc102_non _ j (by omega)]
  rcases h with h | h | h
  · rw [← rawEnd_keep s1 j (by omega) (by omega)]
    exact rawEnd_zero x hx0 hx s1 first j (by omega)
  · rw [← rawEnd_keep s1 j (by omega) (by omega)]
    exact rawEnd_zero x hx0 hx s1 first j (by omega)
  · exact raw512_carry x hx0 hx s1 first j h


end ECDSAAdd.Entrant.StairField2V3JuncRefWalk

end
end Merge_StairField2V3JuncRefWalk_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3JuncRef_at_BOptimizations` -/
section Merge_StairField2V3JuncRef_at_BOptimizations

/-!
# LT43b: the record half of the row-425 junction, and division admissibility

`junc_ref`: on every admissible tick-424 state `t0` (no extra assumption,
`ExtraRef := True`) the record junction `refJ0` (ticks `425..504`, record terminal,
clear, parity setup, X)

* keeps the phase, for every tape;
* off `Δv 87` and off the ten sites `pk84` of packet 84 it only clears `Zref`
  (`base 511`, `base 512` = top bits of the a rail, `base 770..857` = the b rail);
* writes the record transcript `recVal origin` on `futurePayload 87` and on `pk84`
  (packet 84 is raw at tick 424 and encoded afterwards: these ten sites are off
  `Δv 87`, change, and are not cleared).

`adm_div` / `adm_div_frame`: a state reached by the division prefix is admissible.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3JuncRef

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR StairField2V3ExitStepsR
open StairField2V3Final StairField2V3JuncRecord StairField2V3JuncRefWalk
open StairPhysicalLayout StairOuterPlacement

attribute [local irreducible] run wires W.compactSkywalkForward Rolling1588TickGap.forward Rolling1588.stackForward Rolling1588.allEncode Rolling1588.encodeGroup Rolling1588.Integer.regularForward Rolling1588.Integer.compactForward Rolling1588.Integer.encodePrefix skywalkArithmeticClear FrontierEntry1591Native.forward RW refJ0






/-! ## Site facts (finite checks) -/








/-! ## Kernel comparison of the two encoded states -/

theorem kernel_unch (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base (rails x) 1 s1.basis) (j : Nat) (hj : Unch j) :
    ((run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis (OB5.sig 511 (base j)) = ((run (Rolling1588.allEncode base true 84) [] (run (W.compactSkywalkForward base 1 424) [] s1))).basis (OB5.sig 424 (base j)) := by
  have z84 := enc84_zero x hx0 hx s1 first
  have z102 := enc102_zero x hx0 hx s1 first
  have p512 := raw512_past x hx0 hx s1 first
  have p425 := raw425_past x hx0 hx s1 first
  rcases hj with h | h | h | h | h
  · rw [sig_fix 511 le_rfl j (by omega), sig_fix 424 (by norm_num) j (by omega)]
    exact enc_agree x hx0 hx s1 first j (Or.inl h)
      (by rw [(p512 j (by omega)).1, (p425 j (by omega)).1])
  · rw [sig_fix 511 le_rfl j (by omega), sig_fix 424 (by norm_num) j (by omega), z102 j (by omega), z84 j (by omega)]
  · by_cases a1 : j < 1028
    · rw [sig_fix 511 le_rfl j (by omega), sig_fix 424 (by norm_num) j (by omega), z102 j (by omega),
        z84 j (by omega)]
    by_cases a2 : j < 1285
    · obtain ⟨t, rfl⟩ : ∃ t, j = 1028 + t := ⟨j - 1028, by omega⟩
      rw [sig_fix 511 le_rfl (1028 + t) (by omega), sig_fix 424 (by norm_num) (1028 + t) (by omega)]
      exact enc_agree x hx0 hx s1 first (1028 + t) (Or.inr (Or.inl ⟨by omega, by omega⟩))
        (by rw [(p512 t (by omega)).2, (p425 t (by omega)).2])
    by_cases a3 : j ≤ 1452
    · rw [sig_move 511 le_rfl j (by omega), sig_move 424 (by norm_num) j (by omega), z102 (3081 - j) (by omega),
        z84 (3081 - j) (by omega)]
    by_cases a4 : j ≤ 1539
    · rw [sig_move 511 le_rfl j (by omega), sig_fix 424 (by norm_num) j (by omega), z102 (3081 - j) (by omega),
        z84 j (by omega)]
    by_cases a5 : j ≤ 1541
    · rw [sig_fix 511 le_rfl j (by omega), sig_fix 424 (by norm_num) j (by omega), z102 j (by omega),
        z84 j (by omega)]
    · have e : j = 1542 := by omega
      subst e
      rw [sig_move 511 le_rfl 1542 (by omega), sig_fix 424 (by norm_num) 1542 (by omega),
        z84 1542 (by omega), show (3081 : Nat) - 1542 = 1028 + 511 from rfl]
      exact (enc102_non ((run (W.compactSkywalkForward base 1 511) [] s1)) (1028 + 511) (by omega)).trans
        ((p512 511 (by norm_num)).2.trans (congrArg Prod.snd (cw511 x hx0 hx)))
  · rw [sig_move 511 le_rfl j (by omega), sig_fix 424 (by norm_num) j (by omega), z84 j (by omega),
      show 3081 - j = 1028 + (2053 - j) by omega]
    exact enc102_hole x hx0 hx s1 first (2053 - j) (by omega) h.2.2
  · by_cases a1 : j = 1797
    · subst a1
      rw [sig_fix 511 le_rfl 1797 (by omega), sig_fix 424 (by norm_num) 1797 (by omega), z102 1797 (by omega),
        z84 1797 (by omega)]
    · rw [sig_move 511 le_rfl j (by omega), sig_move 424 (by norm_num) j (by omega)]
      obtain ⟨t, ht⟩ : ∃ t, 3081 - j = 1028 + t := ⟨2053 - j, by omega⟩
      rw [ht]
      exact enc_agree x hx0 hx s1 first (1028 + t) (Or.inr (Or.inl ⟨by omega, by omega⟩))
        (by rw [(p512 t (by omega)).2, (p425 t (by omega)).2])


/-! ## The state after the phase-hosted record walk end -/


theorem ref_state (x : Nat) (hx0 : 0 < x) (hx : x < ECDSAAdd.p) (s1 : State)
    (first : W.CompactSkywalkStage base (rails x) 1 s1.basis) (m : List Bool) (t0 : State)
    (ht : pullState Rolling1588Lifetime.phaseHost t0 =
      run (Rolling1588TickGap.forward true 1 424) m s1) (c : List Bool) :
    ∃ G : State, run refJ0 c t0 = run StairExitLT24.SX [] G ∧ G.phase = t0.phase ∧
      (∀ q, t0.basis (Rolling1588Lifetime.phaseHost q) = ((run (Rolling1588.allEncode base true 84) [] (run (W.compactSkywalkForward base 1 424) [] s1))).basis (OB5.sig 424 q)) ∧
      (∀ q, q ≠ base 512 → q ≠ base 770 →
        G.basis (Rolling1588Lifetime.phaseHost q) = ((run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis (OB5.sig 511 q)) ∧
      G.basis (Rolling1588Lifetime.phaseHost (base 512)) = false ∧
      G.basis (Rolling1588Lifetime.phaseHost (base 770)) = false ∧
      G.basis FrontierEntry1591Field.host =
        TraceParity5.parity (FrontierEntry1591Field.controls.map G.basis) := by
  obtain ⟨c1, h1⟩ := refJ0_split c t0
  obtain ⟨c1', c2, h2r⟩ := refJ0_record x hx0 hx s1 first m t0 ht c1
  obtain ⟨G, hG⟩ : ∃ G : State, run (ph RW) c1 t0 = G := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : State, (run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1)) = E := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : State,
      run (skywalkArithmeticClear base) c2 (pullState (OB5.sig 511) E) = K := ⟨_, rfl⟩
  have h1' : run refJ0 c t0 = run StairExitLT24.SX [] G :=
    h1.trans (congrArg (fun t => run StairExitLT24.SX [] t) hG)
  have h2 : pullState Rolling1588Lifetime.phaseHost G = K :=
    (congrArg (pullState Rolling1588Lifetime.phaseHost) hG).symm.trans (h2r.trans
      ((congrArg (fun t => run (skywalkArithmeticClear base) c2 t)
        ((walk511 x hx0 hx s1 first c1').trans (congrArg (pullState (OB5.sig 511)) hE))).trans hK))
  have ht' : pullState Rolling1588Lifetime.phaseHost t0 = pullState (OB5.sig 424) ((run (Rolling1588.allEncode base true 84) [] (run (W.compactSkywalkForward base 1 424) [] s1))) :=
    ht.trans (walk424 x hx0 hx s1 first m)
  have cs := clear_spec (pullState (OB5.sig 511) E) c2
  rw [hK] at cs
  have hb : ∀ q, G.basis (Rolling1588Lifetime.phaseHost q) = K.basis q := fun q =>
    (pull_basis Rolling1588Lifetime.phaseHost G q).symm.trans
      (congrFun (congrArg State.basis h2) q)
  have eE : ∀ r, E.basis r = ((run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis r :=
    fun r => congrFun (congrArg State.basis hE.symm) r
  have rc := clear_spec ((run (W.compactSkywalkForward base 1 511) [] s1)) []
  have v512 : E.basis (OB5.sig 511 (base 512)) = ((run (W.compactSkywalkForward base 1 511) [] s1)).basis (base 512) := by
    rw [sig_fix 511 le_rfl 512 (by omega)]
    exact (eE _).trans (enc102_non _ 512 (by omega))
  have v511 : E.basis (OB5.sig 511 (base 511)) = ((run (W.compactSkywalkForward base 1 511) [] s1)).basis (base 511) := by
    rw [sig_fix 511 le_rfl 511 (by omega)]
    exact (eE _).trans (enc102_non _ 511 (by omega))
  have v770 : E.basis (OB5.sig 511 (base 770)) = ((run (W.compactSkywalkForward base 1 511) [] s1)).basis (base 770) := by
    rw [sig_fix 511 le_rfl 770 (by omega)]
    exact (eE _).trans (enc102_non _ 770 (by omega))
  refine ⟨G, h1', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have p1 : G.phase = K.phase :=
      (pull_phase Rolling1588Lifetime.phaseHost G).symm.trans (congrArg State.phase h2)
    have p3 : K.phase = E.phase := cs.1.trans (pull_phase _ E)
    have p4 : E.phase = s1.phase := (congrArg State.phase hE.symm).trans
      ((enc_phase s1).2.trans (stage512 x hx0 hx s1 first).1)
    have p2 : t0.phase = s1.phase :=
      (pull_phase Rolling1588Lifetime.phaseHost t0).symm.trans ((congrArg State.phase ht').trans
        ((pull_phase _ _).trans ((enc_phase s1).1.trans (stage425 x hx0 hx s1 first).1)))
    exact p1.trans (p3.trans (p4.trans p2.symm))
  · exact fun q => (pull_basis Rolling1588Lifetime.phaseHost t0 q).symm.trans
      ((congrFun (congrArg State.basis ht') q).trans (pull_basis (OB5.sig 424) _ q))
  · intro q n1 n2
    exact (hb q).trans ((cs.2.1 q n1 n2).trans ((pull_basis (OB5.sig 511) E q).trans (eE _)))
  · refine (hb _).trans (cs.2.2.1.trans ?_)
    rw [pull_basis, pull_basis, v512, v511, ← rc.2.2.1]
    exact rawEnd_zero x hx0 hx s1 first 512 (by omega)
  · refine (hb _).trans (cs.2.2.2.trans ?_)
    rw [pull_basis, pull_basis, v770, v511, ← rc.2.2.2]
    exact rawEnd_zero x hx0 hx s1 first 770 (by omega)
  · have par := Rolling1588.encoded_host_relation base true base_pool_nodup x hx0 hx ((run (W.compactSkywalkForward base 1 511) [] s1))
      ((run (Rolling1588.allEncode base true 102) [] (run (W.compactSkywalkForward base 1 511) [] s1))) (stage512 x hx0 hx s1 first).2 rfl
    have parE : E.basis (base 1538) = TraceParity5.xorRange 816
        (fun i => E.basis (NewHistory5.payloadWire base i)) := by
      rw [← hE]
      exact par
    have placed := FrontierEntry1591Kernel.placed_host_parity E parE
    have kpar := FrontierEntry1591Kernel.clear_host_parity _ c2 placed
    rw [hK] at kpar
    have hh : G.basis FrontierEntry1591Field.host = K.basis (base 1543) :=
      (congrArg G.basis ph_fix.2.2.2.1.symm).trans (hb (base 1543))
    have hc : FrontierEntry1591Field.controls.map G.basis =
        FrontierEntry1591Kernel.payloadControls.map K.basis :=
      List.map_congr_left (fun q hq => (congrArg G.basis (ph_controls q hq).symm).trans (hb q))
    exact hh.trans (kpar.trans (congrArg TraceParity5.parity hc.symm))

/-! ## The record half of the junction -/

theorem junc_ref (x : Nat) : ∀ t0, Adm ExtraRef x t0 → ∀ c,
    (run refJ0 c t0).phase = t0.phase ∧
    (∀ q, q ∉ Δv 87 → q ∉ pk84 →
      (run refJ0 c t0).basis q = if q ∈ Zref then false else t0.basis q) ∧
    ∃ origin, TraceOK x origin ∧
      (∀ r ∈ futurePayload 87, (run refJ0 c t0).basis (fieldPlace r) = recVal origin r) ∧
      (∀ r ∈ pk84, (run refJ0 c t0).basis r = recVal origin r) := by
  rintro t0 ⟨hx0, hx, -, s1, m, first, ht⟩ c
  obtain ⟨G, hG, gph, hk0, hkf, g512, g770, gpar⟩ := ref_state x hx0 hx s1 first m t0 ht c
  have hrun : run refJ0 c t0 = ⟨G.phase, Function.update (Function.update G.basis (base 1543) false)
      (base 511) (!(Function.update G.basis (base 1543) false (base 511)))⟩ :=
    hG.trans (sx_run G gpar [])
  rw [hrun]
  have nh : (base 511 : Wire) ≠ base 1543 := fun e => absurd (base_injective e) (by norm_num)
  have f_other : ∀ a, a ≠ base 511 → a ≠ base 1543 →
      Function.update (Function.update G.basis (base 1543) false) (base 511)
        (!(Function.update G.basis (base 1543) false (base 511))) a = G.basis a := by
    intro a n1 n2
    rw [Function.update_of_ne n1, Function.update_of_ne n2]
  have g511 : G.basis (base 511) = true := by
    have t := hkf (base 511) (fun e => absurd (base_injective e) (by norm_num))
      (fun e => absurd (base_injective e) (by norm_num))
    rw [ph_fix.1, sig_fix 511 le_rfl 511 (by omega)] at t
    rw [t]
    exact (enc102_non ((run (W.compactSkywalkForward base 1 511) [] s1)) 511 (by omega)).trans
      ((raw512_past x hx0 hx s1 first 511 (by norm_num)).1.trans
        (congrArg Prod.fst (cw511 x hx0 hx)))
  have pay : ∀ r ∈ futurePayload 87 ++ pk84,
      Function.update (Function.update G.basis (base 1543) false) (base 511)
        (!(Function.update G.basis (base 1543) false (base 511))) r =
        recVal ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis r := by
    intro r hr
    obtain ⟨-, n511, nhost, n512, n770, fixr⟩ := pfacts r hr
    rw [f_other r n511 nhost]
    have t := hkf r n512 n770
    rw [fixr] at t
    rw [t]
    exact enc102_recVal s1 r n512 n770
  refine ⟨gph, ?_, ((run (skywalkArithmeticClear base) [] (run (W.compactSkywalkForward base 1 511) [] s1))).basis, traceOK x hx0 hx s1 first, ?_, ?_⟩
  · intro a hΔ hpk
    show Function.update (Function.update G.basis (base 1543) false) (base 511)
        (!(Function.update G.basis (base 1543) false (base 511))) a = _
    by_cases h511 : a = base 511
    · subst h511
      rw [if_pos (by simp [Zref]), Function.update_self, Function.update_of_ne nh, g511]
      rfl
    by_cases hh : a = base 1543
    · subst hh
      rw [if_neg ph_fix.2.2.2.2]
      have t := hk0 (base 1543)
      rw [ph_fix.2.2.2.1, sig_fix 424 (by norm_num) 1543 (by omega),
        enc84_zero x hx0 hx s1 first 1543 (by omega)] at t
      rw [t, Function.update_of_ne (Ne.symm nh), Function.update_self]
    rw [f_other a h511 hh]
    have ea : Rolling1588Lifetime.phaseHost (Rolling1588Lifetime.phaseHost.symm a) = a :=
      Equiv.apply_symm_apply _ _
    rcases symm_cases a with e | ⟨a6, q6⟩
    · rw [e] at ea
      by_cases hz : a ∈ Zref
      · rw [if_pos hz]
        simp only [Zref, List.mem_cons, List.mem_map, List.mem_range] at hz
        rcases hz with e1 | e1 | ⟨k, hk, rfl⟩
        · exact absurd e1 h511
        · subst e1
          rw [← ea]
          exact g512
        · by_cases k0 : k = 0
          · subst k0
            rw [← ea]
            exact g770
          · have t := hkf (base (770 + k)) (fun e => absurd (base_injective e) (by omega))
              (fun e => absurd (base_injective e) (by omega))
            rw [ea, sig_fix 511 le_rfl (770 + k) (by omega)] at t
            rw [t]
            exact enc102_zero x hx0 hx s1 first (770 + k) (by omega)
      · rw [if_neg hz]
        have n512 : a ≠ base 512 := fun e => hz (by rw [e]; simp [Zref])
        have n770 : a ≠ base 770 := fun e => hz (by
          rw [e]
          simp only [Zref, List.mem_cons, List.mem_map, List.mem_range]
          exact Or.inr (Or.inr ⟨0, by norm_num, rfl⟩))
        have tf := hkf a n512 n770
        have t0' := hk0 a
        rw [ea] at tf t0'
        rw [tf, t0']
        by_cases hp : a ∈ skywalkPoolWires base
        · obtain ⟨j, hj, rfl⟩ := pool_id a hp
          have cls : Unch j ∨ (420 ≤ j ∧ j ≤ 424) ∨ (425 ≤ j ∧ j ≤ 510) ∨ j = 511 ∨ j = 512 ∨
              (770 ≤ j ∧ j ≤ 857) ∨ j = 1543 ∨
              (1544 ≤ j ∧ j ≤ 1628 ∧
                ((2053 - j) % 5 = 0 ∨ (2053 - j) % 5 = 1 ∨ (2053 - j) % 5 = 3)) ∨
              (1629 ≤ j ∧ j ≤ 1633) := by
            unfold Unch
            omega
          rcases cls with u | u | u | u | u | u | u | u | u
          · exact kernel_unch x hx0 hx s1 first j u
          · exact (hpk (by
              unfold pk84
              exact List.mem_append_left _ (List.mem_map.mpr
                ⟨j - 420, List.mem_range.mpr (by omega), congrArg base (by omega)⟩))).elim
          · exact (hΔ (List.mem_toFinset.mpr
              (dv_g j (List.mem_range'_1.mpr ⟨u.1, by omega⟩)))).elim
          · exact absurd (congrArg base u) h511
          · exact absurd (congrArg base u) n512
          · exfalso
            apply hz
            simp only [Zref, List.mem_cons, List.mem_map, List.mem_range]
            exact Or.inr (Or.inr ⟨j - 770, by omega, congrArg base (by omega)⟩)
          · exact absurd (congrArg base u) hh
          · exfalso
            apply hΔ
            have d := dv_s (2053 - j) (List.mem_filter.mpr
              ⟨List.mem_range'_1.mpr ⟨by omega, by omega⟩, decide_eq_true u.2.2⟩)
            rw [show 2053 - (2053 - j) = j by omega] at d
            exact List.mem_toFinset.mpr d
          · exact (hpk (by
              unfold pk84
              exact List.mem_append_right _ (List.mem_map.mpr
                ⟨j - 1629, List.mem_range.mpr (by omega), congrArg base (by omega)⟩))).elim
        · exact kernel_off s1 a hp
    · rw [if_neg (six_facts a a6).1]
      have qf := six_facts _ q6
      have tf := hkf _ qf.2.1 qf.2.2.1
      have t0' := hk0 (Rolling1588Lifetime.phaseHost.symm a)
      rw [ea] at tf t0'
      rw [tf, t0']
      simp only [six, List.mem_cons, List.not_mem_nil, or_false] at q6
      rcases q6 with e | e | e | e | e | e
      all_goals
        rw [e]
        exact kernel_unch x hx0 hx s1 first _ (by unfold Unch; omega)
  · intro r hr
    rw [(pfacts r (List.mem_append_left _ hr)).1]
    exact pay r (List.mem_append_left _ hr)
  · intro r hr
    exact pay r (List.mem_append_right _ hr)


/-! ## Values of an admissible tick-424 state -/

/-- Closed form of an admissible state, for the selected half. -/
theorem adm_closed (Extra : Nat → State → Prop) (x : Nat) (t0 : State) (h : Adm Extra x t0) :
    ∃ s1 : State, W.CompactSkywalkStage base (rails x) 1 s1.basis ∧ t0.phase = s1.phase ∧
      (∀ q, t0.basis (Rolling1588Lifetime.phaseHost q) = ((run (Rolling1588.allEncode base true 84) [] (run (W.compactSkywalkForward base 1 424) [] s1))).basis (OB5.sig 424 q)) ∧
      (∀ q, q ∉ skywalkPoolWires base →
        t0.basis (Rolling1588Lifetime.phaseHost q) = s1.basis q) := by
  obtain ⟨hx0, hx, -, s1, m, first, ht0⟩ := h
  have ht := ht0.trans (walk424 x hx0 hx s1 first m)
  have hv : ∀ q, t0.basis (Rolling1588Lifetime.phaseHost q) = ((run (Rolling1588.allEncode base true 84) [] (run (W.compactSkywalkForward base 1 424) [] s1))).basis (OB5.sig 424 q) :=
    fun q => (pull_basis Rolling1588Lifetime.phaseHost t0 q).symm.trans
      ((congrFun (congrArg State.basis ht) q).trans (pull_basis (OB5.sig 424) _ q))
  refine ⟨s1, first, ?_, hv, ?_⟩
  · exact (pull_phase Rolling1588Lifetime.phaseHost t0).symm.trans ((congrArg State.phase ht).trans
      ((pull_phase _ _).trans ((enc_phase s1).1.trans (stage425 x hx0 hx s1 first).1)))
  · intro q hq
    rw [hv q, sig_off_pool 424 (by norm_num) q hq, enc_off 84 (by norm_num) _ q hq,
      raw425_off s1 q hq]


/-! ## Division admissibility -/



end ECDSAAdd.Entrant.StairField2V3JuncRef

end
end Merge_StairField2V3JuncRef_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3JuncSel2Final_at_BOptimizations` -/
section Merge_StairField2V3JuncSel2Final_at_BOptimizations

/-!
# LT43f: the row-425 junction on the repaired first pack

* `extraSel_genuine`: the extra admissibility fact `ExtraSel` (clean sites of the
  tick-424 record state) holds on every `prefixW` image of a division input;
* `junc_sel_ref`: the selected half in the shape of LT43b's combinator
  `StairField2V3JuncRef.junctionG_of_halves`;
* `junc`: the junction `JunctionG P x (Adm ExtraSel x)`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3JuncSel2

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairPhysicalLayout StairOuterPlacement StairField2V3Seg
open StairField2V3SegFacts StairField2V3Entry StairField2V3Delta
open StairField2V3ExitStepsR StairField2V3Final
open StairField2V3JuncSel StairField2V3JuncRefWalk






attribute [local irreducible] run wires W.compactSkywalkForward Rolling1588TickGap.forward Rolling1588.stackForward Rolling1588.allEncode Rolling1588.encodeGroup Rolling1588.Integer.regularForward Rolling1588.Integer.compactForward Rolling1588.Integer.encodePrefix skywalkArithmeticClear FrontierEntry1591Native.forward


/-- **`ExtraSel` is true on genuine states**: every `prefixW` image of a division
input is clean on `cleanRec2`. -/
theorem extraSel_genuine : ∀ (s' : State) (f' : StairConcreteAssembly.EntryFrame s')
    (c0 : List Bool), ExtraSel f'.x (run prefixW c0 s') := by
  intro s' f' c0 q hq
  have hadm := StairField2V3ExitRecClose.adm_frame (fun _ _ => True) (fun _ _ _ => trivial)
    s' f' c0
  obtain ⟨s1, first, -, hv, -⟩ := StairField2V3JuncRef.adm_closed _ _ _ hadm
  rw [hv q]
  exact clean_enc f'.x hadm.1 hadm.2.1 s1 first q hq



end ECDSAAdd.Entrant.StairField2V3JuncSel2

end
end Merge_StairField2V3JuncSel2Final_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3LastTraj_at_BOptimizations` -/
section Merge_StairField2V3LastTraj_at_BOptimizations

/-!
# LT43c: the last step of field 2 — forward trajectory to tick 504 and the terminal round trip

Tail coordinates, terminal row (budget 12, ticks 500 .. 504).

* `traj504`: on a shadow-clean state holding the compact checkpoint of row 500 and
  clean on `CT`, after `unpack 12 · tick 500 · middle 501..504` the state agrees
  (off the virtual sites) with a moved record stage at tick 505;
* `termVirtual`: LT24's `TermVirtual` at that state (record state at tick 505 of a
  stage-1 trajectory, through `terminalPerm`);
* `trip_clean` / `trip_tail`: `reverseLast ∘ forwardLast = id` (shadow-clean, then
  arbitrary shadow labels);
* `lastTrip_of_clean`: `LastTrip Φ` for every `Φ` that implies `CleanT`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3LastTraj

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairPhysicalLayout StairField2V3Seg StairField2V3Codec StairField2V3Unpack StairField2V3Pack
open StairField2V3End StairField2V3Decode StairField2V3Walk StairField2V3SegFacts StairField2V3SegFacts2
open StairField2V3SegSpec StairField2V3LastStage



/-- The state at the terminal link. -/
abbrev u3 (m1 m2 m3 : List Bool) (u : State) : State :=
  run (StairPhysicalPrimitives.middleForward 501 4) m3
    (run (StairPhysicalPrimitives.tickForward 500) m2
      (run (StairPhysicalPrimitives.unpack 12) m1 u))





/-! ## The virtual record state at the terminal link -/





/-! ## K4C (replay budget): `Chk` on literal bit masks, one pass per program

`Chk` tested membership in `ZList 12`, `walkSites 12`, `CT`, `futurePayload 12`,
`unpackSites 12` and the sign pools by list scans, re-evaluated per wire, and the support of
each block was a `Finset` union.  Every list is now a literal mask (checked once below), and
each block is checked by one linear pass over its instructions (`k4cAll`). -/
























theorem chk_forward : ∀ q ∈ wires StairTerminalV3.forwardRecord, Chk q := by
  have m6 : ∀ y ∈ StairTerminalV3.cand6Sites, Chk (OB5.sig 510 y) :=
    k4c_chk_list (by decide +kernel)
  have pp : ∀ q ∈ wires (Six505.packP true), Chk q := k4c_chk_all (by decide +kernel)
  have af : ∀ q ∈ wires (ForwardSixPlacement.after true), Chk q := k4c_chk_all (by decide +kernel)
  have cl : ∀ q ∈ wires (skywalkArithmeticClear base), Chk q := k4c_chk_all (by decide +kernel)
  intro q hq
  simp only [StairTerminalV3.forwardRecord, wires_append, Finset.mem_union] at hq
  rcases hq with ((hm | hp) | ha) | hc
  · rw [Six505.merged6, renameProgram_support, Finset.mem_image] at hm
    obtain ⟨y, hy, rfl⟩ := hm
    exact m6 y (List.mem_toFinset.mp (StairTerminalV3.cand6_support hy))
  · exact pp q hp
  · exact af q ha
  · exact cl q hc






/-! ## The terminal round trip in tail coordinates -/




section
/- K4C (elaboration): without this the elaborator unfolds `StairPhysicalPrimitives.pack 12`
while matching `pack_rows` against `StairExitLT24.P.pack 12` (≈ 145 s); the kernel is unaffected. -/
attribute [local irreducible] StairPhysicalPrimitives.pack


end


/-! ## `LastTrip` -/




end ECDSAAdd.Entrant.StairField2V3LastTraj

end
end Merge_StairField2V3LastTraj_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3Field2R_at_BOptimizations` -/
section Merge_StairField2V3Field2R_at_BOptimizations

/-!
# LT43g: field 2 from the two pinned plans

* `entryPlanR lastRecX : ∀ x, EntryPlanR P x` — the division plan with the input
  pinned: junction from LT43f's `junc`, segments from LT42's `spec`/`rec`, last step
  from LT43c's `lastSpec_pinned` and the record fact `lastRecX`;
* `exitPlanR juncRecX : ∀ k x, ExitPlanR P k x` — the multiplication plan: junction
  from `lastSpec_pinned` / `lastTrip_pinned` and the record fact `juncRecX`, reverse
  segments from LT42 + LT43d's `rr0..rr4`, close from LT43f/LT43b/LT43d;
* `field2_R` — field 2 (exact certificate field type) from the two record facts.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField2V3Field2R

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR StairField2V3ExitStepsR
open StairField2V3EntryPlanR StairField2V3Final
open StairPhysicalLayout StairOuterPlacement
open StairField2V3LastSpec (lastΦx)
open StairField2V3JuncSel2 (ExtraSel)

/-- The division record fact of the last step (proved by LT43h): after the record
prefix `R6` from a division input of input `x`, the record state satisfies `lastΦx x`. -/
def LastRecX : Prop :=
  ∀ (x : Nat) (s0 : State) (f : StairConcreteAssembly.EntryFrame s0), f.x = x →
    ∀ m, lastΦx x (run R6 m s0).basis

/-- The multiplication record fact of the exit junction (proved by LT43h). -/
def JuncRecX : Prop :=
  ∀ k x, JuncRecE k x (lastΦx x)

/-! ## Division -/




/-! ## Multiplication -/



/-! ## Field 2 -/



end ECDSAAdd.Entrant.StairField2V3Field2R

end
end Merge_StairField2V3Field2R_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField2V3LastRecX_at_BOptimizations` -/
section Merge_StairField2V3LastRecX_at_BOptimizations

/-!
# LT43h: record facts of the last step for a pinned input (both sides)

On the genuine record state `b` after `R6` (division) and after `headE`
(multiplication), for the input `x`:

* `CleanT b` holds (the scratch of the last step is clean);
* the control `base 0` is zero;
* the XOR of the 816 payload controls obeys the law (`lastΨx`)

  `parity (controls.map b) = s510 x ^^ (XOR of the first five raw sign letters of x
      ^^ XOR of the eight packet-0 controls of b)`.

The packets `1 … 101` agree with the record cut frame, whose packets keep the XOR of
their raw sign letters.  Packet 0 holds the scratch-window image of the encoded packet
(`WinT`, carried along the invariant `G` and by `inv_head_w`).

LT47 (fixed program, defect 2): the selected setup now runs between `unprefix` and
`clearProgram`, so it reads the encoded packet 0.  `lastRecX` / `juncRecX`: the record
states satisfy LT47's `lastΦx` (window image of a clean canonical state whose packet-0
payload XOR is that of the first five raw sign letters).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairField2V3LastRecX

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3Delta StairField2V3Seg StairField2V3ExitPlanR StairField2V3ExitStepsR
open StairField2V3RecScratch StairField2V3ExitRec
open StairField2V3LastTraj StairField2V3LastSpec StairField2V3LastRecXPar
open StairPhysicalLayout StairOuterPlacement

attribute [local irreducible] wires run

/-! ## The frame invariant with a pinned input, and the exceptional sites -/











/-! ## Division: the invariant along `R0 … R6` -/





theorem g_first (s0 : State) (f : StairConcreteAssembly.EntryFrame s0) (m : List Bool) :
    G f.x 1 (run (R0 ++ firstPkt) m s0) := by
  have actual := FrontierEntry1591Kernel.paired_input f.x f.Y.val f.source s0 f.input
    f.outsideNumerator
  rw [R0_shape,
    run_append (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
      (StairSchedule.paritySetup ++ StairSchedule.hostedX)),
    run_append (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true)),
    first_phase_hosted true f.sharedNodup f.historyAbove f.x _ f.x_pos f.x_lt s0 _ actual]
  exact g_inner s0 f _ _ _

theorem g_R1 (s0 : State) (f : StairConcreteAssembly.EntryFrame s0) (m : List Bool) :
    G f.x 85 (run R1 m s0) := by
  unfold R1
  rw [run_append (R0 ++ firstPkt) (grp 1 84)]
  exact g_step f.x 1 84 le_rfl (by norm_num) _ (g_first s0 f _) _

theorem g_R2 (s0 : State) (f : StairConcreteAssembly.EntryFrame s0) (m : List Bool) :
    G f.x 90 (run R2 m s0) := by
  unfold R2
  rw [run_append R1 (grp 85 5)]
  exact g_step f.x 85 5 (by norm_num) (by norm_num) _ (g_R1 s0 f _) _

theorem g_R3 (s0 : State) (f : StairConcreteAssembly.EntryFrame s0) (m : List Bool) :
    G f.x 93 (run R3 m s0) := by
  unfold R3
  rw [run_append R2 (grp 90 3)]
  exact g_step f.x 90 3 (by norm_num) (by norm_num) _ (g_R2 s0 f _) _

theorem g_R4 (s0 : State) (f : StairConcreteAssembly.EntryFrame s0) (m : List Bool) :
    G f.x 96 (run R4 m s0) := by
  unfold R4
  rw [run_append R3 (grp 93 3)]
  exact g_step f.x 93 3 (by norm_num) (by norm_num) _ (g_R3 s0 f _) _

theorem g_R5 (s0 : State) (f : StairConcreteAssembly.EntryFrame s0) (m : List Bool) :
    G f.x 98 (run R5 m s0) := by
  unfold R5
  rw [run_append R4 (grp 96 2)]
  exact g_step f.x 96 2 (by norm_num) (by norm_num) _ (g_R4 s0 f _) _

theorem g_R6 (s0 : State) (f : StairConcreteAssembly.EntryFrame s0) (m : List Bool) :
    G f.x 100 (run R6 m s0) := by
  unfold R6
  rw [run_append R5 (grp 98 2)]
  exact g_step f.x 98 2 (by norm_num) (by norm_num) _ (g_R5 s0 f _) _

/-! ## Multiplication: the exceptional sites after `headE` -/

theorem ez_head (k x : Nat) (t0 : State) (h0 : ExitMiddleX k x t0) (m : List Bool) :
    EZ (run headE m t0) := by
  obtain ⟨s, f, -, records, rfl⟩ := h0
  have opening : run StairField2V3Replay.exitReferenceOpening records s =
      run (Rolling1588.firstPhase false) records s :=
    first_phase_hosted false f.sharedNodup f.historyAbove f.x f.Y.val f.x_pos f.x_lt s
      records f.input
  rw [opening]
  obtain ⟨origin, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
    f.sharedNodup f.historyAbove f.selectorsAway f.x f.Y f.x_pos f.x_lt s records f.input
  have ctx := Rolling1588Lifetime.prepared_context f.sharedNodup f.selectorsAway
    f.transcript f.x f.Y s origin facts legal f.selectorG_zero f.selectorS_zero
  have work := Rolling1588Lifetime.first_work_zero false f.sharedNodup f.x f.Y.val s
    records f.input
  have parity := Rolling1588Lifetime.first_parity false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  have input := frames false
  rw [lf_eq] at input work parity
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) records s = v := ⟨_, rfl⟩
  rw [hv] at input work parity
  rw [hv]
  have flags := canonical_flags origin.basis ctx f.Y 0 v input
  rw [headE_shape,
    run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram ++ liftF headCore) (grpF 100 2),
    run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram) (liftF headCore),
    run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX)
      (StairSchedule.fieldRename FourScratchWindow.clearProgram)]
  unfold grpF
  exact ez_lift _ (groupsF_off 100 2 (by norm_num) (by norm_num)) _ _
    (ez_lift headCore headCore_off _ _ (ez_start v flags.1 work parity _ clear_avoidE _ _))

/-! ## Site facts -/

/-! K4C (replay budget): the site checks below scanned `futurePayload 12`, `EP`, `ryL` (512
labels), `histL` (1024 labels), `cleanL` and the twelve window labels once per site.  Each list
is now a literal bit mask (checked once, `k4rM*_eq`), the clean-site check is one `List.all`
pass, and the two payload-control facts share one pass (`k4r_pay_all`). -/















/-! ## Consequences of the invariant -/







/-! ## The record facts in the form that is TRUE on genuine states -/



/-! ## LT47: the record facts for the fixed program (window read between the windows) -/

open StairField2V3Win (mem_L mix pctrl Canon WinT)













/-- **LastRecX (division record fact), fixed program.** -/
theorem lastRecX : ∀ (x : Nat) (s0 : State) (f : StairConcreteAssembly.EntryFrame s0),
    f.x = x → ∀ m, lastΦx x (run R6 m s0).basis := by
  intro x s0 f hx m
  subst hx
  obtain ⟨fr, ez, w⟩ := g_R6 s0 f m
  exact phi_of_win f.x _ (psi_of f.x 100 _ fr ez) (holes_of f.x 100 _ fr) w

/-- **JuncRecX (multiplication record fact), fixed program.** -/
theorem juncRecX : ∀ k x, JuncRecE k x (lastΦx x) := by
  intro k x t ht
  obtain ⟨s0, m, hs0, rfl⟩ := ht
  have hw := inv_head_w k x s0 hs0 m
  have fr := frameAt_of_invE x 100 _ hw.1
  refine ⟨phi_of_win x _ (psi_of x 100 _ fr (ez_head k x s0 hs0 m)) (holes_of x 100 _ fr) hw.2, ?_⟩
  obtain ⟨origin, tr, hv, -⟩ := vals_of_inv x 12 100 (by norm_num) valFacts5 _ hw.1
  exact ⟨origin, tr, hv⟩

end ECDSAAdd.Entrant.StairField2V3LastRecX

end
end Merge_StairField2V3LastRecX_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairLoanField7Cores_at_BOptimizations` -/
section Merge_StairLoanField7Cores_at_BOptimizations

/-!
# Field 7 in the core shape of field 2 (one proof for both)

LT21's field 2 (`StairField2V3Core.field2_of_cores`) consumes two cores on the
four named kernel boundaries: the division arithmetic on `EntryPre` and the
multiplication remainder on `ExitMiddle k`.  This module states the same two
cores for an arbitrary loan provider (`CoresFor loans`; bodies of the four
programs are LT21's with `recordLoans` replaced by `loans` on the staircase
side and by the record-shaped loaned field on the reference side) and proves

* `commutationFor_of_cores : CoresFor loans → … → StairLoanField7.CommutationFor loans`
  (the unchanged entry closing / exit opening are tape-free on the reached
  states; both facts are proved here for `bestLoans` and `recordLoans`);
* `loan_composition_of_cores (best : CoresFor bestLoans) (record : CoresFor recordLoans)`
  = the exact `StairOpen.loan_composition` type.

The record instance of `CoresFor` is literally LT21's pair of cores
(`entryReferenceArithmeticFor_record`, `exitReferenceRemainderFor_record`).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairLoanField7Cores

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField

/-! ## Tape algebra (generic) -/








/-! ## The four kernel boundaries, for any loan provider -/


/-- LT21's `entryReferenceArithmetic` with the record-shaped loaned field. -/
def entryReferenceArithmeticFor (loans : StairSchedule.StairLoans) : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
    StairLoanRecordSupport.entryFieldHostedShape loans


/-- The unchanged multiplication opening (LT21's `exitReferenceOpening`). -/
def exitOpening : Program :=
  renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase false)



/-- LT21's `StairField2V3Core.ExitMiddle` (loan independent). -/
def ExitMiddle (k : Nat) (t : State) : Prop :=
  ∃ s, StairConcreteAssembly.ExitPre k s ∧ ∃ records, t = run exitOpening records s


/-! ## Record instances are LT21's programs -/

theorem entryReferenceArithmeticFor_record :
    entryReferenceArithmeticFor StairSchedule.recordLoans =
      renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
        Rolling1588.entryFieldHosted := by
  unfold entryReferenceArithmeticFor
  rw [StairLoanRecordSupport.entryFieldHostedShape_record]


/-! ## Kernel splits -/





/-! ## Cores give the commutation -/


/-! ## The two side conditions, proved -/

/-- The unchanged opening is tape-free on `ExitPre` (record facts only). -/
theorem exitOpening_tapeFree (k : Nat) (s : State)
    (hs : StairConcreteAssembly.ExitPre k s) : TapeFree exitOpening s := by
  intro fresh old
  rcases hs with ⟨frame⟩
  have clean := Rolling1588Lifetime.caller_phase_clean frame.x frame.Y.val s
    frame.input
  have hosted (m : List Bool) :=
    Rolling1588TickGap.first_hosted_run_eq false frame.sharedNodup frame.x
      frame.Y.val frame.x_pos frame.x_lt s m frame.input
  rw [exitOpening, hosted fresh, hosted old]
  apply ECDSAAdd.Arithmetic.MappedCompressed.pullState_perm_injective
    Rolling1588Lifetime.phaseHost
  rw [ECDSAAdd.run_rename _ Rolling1588Lifetime.phaseHost.injective,
    ECDSAAdd.run_rename _ Rolling1588Lifetime.phaseHost.injective,
    Rolling1588Lifetime.pull_phase_clean s clean]
  apply State.extensionality
  · exact (Rolling1588Lifetime.first_phase false frame.sharedNodup
      frame.historyAbove frame.x frame.Y.val frame.x_pos frame.x_lt
      s fresh frame.input).trans
      (Rolling1588Lifetime.first_phase false frame.sharedNodup
        frame.historyAbove frame.x frame.Y.val frame.x_pos frame.x_lt
        s old frame.input).symm
  · exact run_basis_records _ s s fresh old rfl





/-! ## Field 7 from the two instances of the cores -/




end ECDSAAdd.Entrant.StairLoanField7Cores

end
end Merge_StairLoanField7Cores_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairLoanField7Transport_at_BOptimizations` -/
section Merge_StairLoanField7Transport_at_BOptimizations

/-!
# Field 7 from LT21's field-2 plans (transport along the loans)

LT21's coupled chains (`StairField2V3Entry.EntryPlan`, `StairField2V3ExitPlan.ExitPlan`;
copied unchanged from `../LT21/Entrant`) cut both kernels of field 2 into the same pieces.
The loan provider enters only through the packet groups, the division tail
(group 100+2, `divEndpoint`, `copyN`, `canon`) and the multiplication head (`center`,
`copyN`, 68 endpoint, group 100+2).  Here every such piece is a function of a variable
`loans` (`grpL`, `tailPL`, `grpFL`, `headEL`); both cores for `loans` have the same
piece decomposition (`selArithL_shape`, `refArithL_shape`, `selRemL_shape`,
`refRemL_shape`), and the record instances are LT21's pieces (`grpL_record`, …, `rfl`).

Transport of the record plans to `bestLoans`:

* group avoidance (`g*_away`): by inclusion (`StairLoanGroupSupport.liftedGroups_sub`) —
  wires only;
* junction, first packet, segments, last step, low tail, close: no loan piece — copied;
* **value-dependent** (exactly two families, both about the RECORD trajectory only):
  - `EntryReachTransport bestLoans`: every reference state reached through the loaned
    group prefix `RᵢL` is reached through LT21's record prefix `Rᵢ` (i = 1..6), i.e. the
    loaned groups replay the record groups on the record trajectory — used because LT21's
    `seg*`/`lastStep` read `Reach Rᵢ t` as an abstract record fact;
  - `ExitHeadTransport bestLoans k`: the loaned multiplication head `headEL bestLoans`
    reaches only states the record head `headE` reaches from `ExitMiddle k` — used because
    LT21's exit `junction` reads `JE k` (the head's output values);
* reference tape-freeness for `bestLoans`: proved here from LT10's
  `shapeEntryKernel_run_eq` / `shapeExitKernel_run_eq` (fields 3–6).

`site_local_reach` is the value-free alternative: if a plan obligation only reads the
reference state on sites `S` avoided by the record pieces, the loaned prefix reaches a
state agreeing with a record-reachable one on `S`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairLoanField7Transport

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan

/-! ## Generic tape and locality facts (variable programs) -/







/-! ## Division pieces with loans -/






theorem refArithL_shape (loans : StairSchedule.StairLoans) :
    StairLoanField7Cores.entryReferenceArithmeticFor loans =
      prefixW ++ (refJ0 ++ (firstPkt ++ (grpL loans 0 1 84 ++ (grpL loans 13 85 5 ++ (grpL loans 22 90 3 ++ (grpL loans 30 93 3 ++ (grpL loans 36 96 2 ++ (grpL loans 41 98 2 ++ tailPL loans)))))))) := by
  simp only [StairLoanField7Cores.entryReferenceArithmeticFor,
    Rolling1588TickGap.firstPhase, Rolling1588TickGap.tailPhase,
    Rolling1588TickGap.stackForward, Six505.stackForward6, forward_504,
    StairLoanRecordSupport.entryFieldHostedShape, ParityField1591.program,
    ParityHostTransport5.program, FrontierEntry1591Field.hosted,
    StairLoanRecordShape.entryFieldShape, StairLoanRecordShape.entryTailShape,
    StairLoanRecordShape.slices, StairLoanRecordShape.entrySliceList,
    StairSchedule.paritySetup, StairSchedule.hostedX, StairSchedule.entryTailSuffix,
    StairSchedule.placedGroups, StairSchedule.fieldRename, StairSchedule.parityRename,
    prefixW, refJ0, firstPkt, grpL, tailPL, liftF, ph, rename_append', parity_X,
    rename_nil, List.append_assoc, List.append_nil]

/-! ## Division transport -/

def R1L (loans : StairSchedule.StairLoans) : Program := (R0 ++ firstPkt) ++ grpL loans 0 1 84
def R2L (loans : StairSchedule.StairLoans) : Program := R1L loans ++ grpL loans 13 85 5
def R3L (loans : StairSchedule.StairLoans) : Program := R2L loans ++ grpL loans 22 90 3
def R4L (loans : StairSchedule.StairLoans) : Program := R3L loans ++ grpL loans 30 93 3
def R5L (loans : StairSchedule.StairLoans) : Program := R4L loans ++ grpL loans 36 96 2
def R6L (loans : StairSchedule.StairLoans) : Program := R5L loans ++ grpL loans 41 98 2






/-! ### Wire-only route: site-local record facts through the loaned prefixes -/








/-! ## Multiplication pieces with loans -/







/-! ## Multiplication transport -/









/-! ## Assembly: field 7 from LT21's plans -/





end ECDSAAdd.Entrant.StairLoanField7Transport

end
end Merge_StairLoanField7Transport_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairLoanField7Values_at_BOptimizations` -/
section Merge_StairLoanField7Values_at_BOptimizations

/-!
# LT32: the value-level inputs of field 7

* `exitHeadTransport_best half endpoint k : ExitHeadTransport bestLoans k`
* `entryReachTransport_best half : EntryReachTransport bestLoans`

Both are record-trajectory facts: on a record-reachable state the loaned field blocks
replay the record ones.  The replay itself is LT10's record-level loan replay
(`headPrefix_run_eq`, `forward_slices_run_eq`) on the record's own frame; it is moved to
the actual (hosted, windowed, kernel-coordinate) state by `replay_transfer`, using that
the actual field-coordinate state agrees with the record frame state outside

* the three wrapper sites `E = {base 511, host, base 2400}` (hosted X, parity host,
  forced control bit), and
* the eight scratch-window payload sites `Prefix1590.payload0 i`,

and that the record pieces avoid all of these sites.  Variable programs only.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairLoanField7Values

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan

attribute [local irreducible] wires run

/-! ## Exceptional sites -/







/-! ## The scratch window -/









/-! ## The host/parity wrapper -/





/-! ## Record facts (copies of LT10's private helpers) -/





theorem first_phase_hosted (isA : Bool) (hn : (skywalkSharedWires base).Nodup)
    (hlo : History5.HistoryAbove base) (x y : Nat) (hx0 : 0 < x) (hx : x < p)
    (s : State) (m : List Bool) (input : SkywalkArithmeticInput base x y s.basis) :
    run (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase isA)) m s =
      run (Rolling1588.firstPhase isA) m s := by
  refine (Rolling1588TickGap.first_hosted_run_eq isA hn x y hx0 hx s m input).trans ?_
  have before := Rolling1588Lifetime.caller_phase_clean x y s input
  apply Rolling1588Lifetime.phase_run_eq _ s m before
  intro q hq
  have work := Rolling1588Lifetime.first_clean isA hn hlo x y hx0 hx s m input
  rw [lf_eq] at work
  have hostsFree : ∀ r ∈ Rolling1588Lifetime.phaseHosts,
      r ∉ wires (Rolling1588.firstPhase isA) := by
    intro r hr
    have h := Rolling1588Lifetime.first_hosts_free isA r hr
    rw [lf_eq] at h
    exact h
  rw [phase_sites_split] at hq
  rcases Finset.mem_union.mp hq with w | h
  · exact work q w
  · exact (run_preserves_outside _ _ _ _ (hostsFree q h)).trans
      (before q (by rw [phase_sites_split]; exact Finset.mem_union_right _ h))

/-! ## Membership walks (variable programs) -/







/-! ## Exit: avoidance of the record head -/






/-! ## Exit: the endpoint replay as an explicit input (LT19 swap, step 3) -/






/-! ## Exit: the loaned head on `ExitMiddle` states -/

theorem exitHead_run (half : StairLoanRecordShape.HalfReplayHypothesis)
    (hEnd : EndpointReplay StairConcrete.bestLoans) (k : Nat) (t : State)
    (ht : StairField2V3Core.ExitMiddle k t) (m : List Bool) :
    run (StairLoanField7Transport.headEL StairConcrete.bestLoans) m t =
      run (StairLoanField7Transport.headEL StairSchedule.recordLoans) m t := by
  obtain ⟨s, ⟨f⟩, records, rfl⟩ := ht
  have opening : run StairField2V3Replay.exitReferenceOpening records s =
      run (Rolling1588.firstPhase false) records s :=
    first_phase_hosted false f.sharedNodup f.historyAbove f.x f.Y.val f.x_pos f.x_lt s
      records f.input
  rw [opening]
  obtain ⟨origin, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
    f.sharedNodup f.historyAbove f.selectorsAway f.x f.Y f.x_pos f.x_lt s records f.input
  have ctx := Rolling1588Lifetime.prepared_context f.sharedNodup f.selectorsAway
    f.transcript f.x f.Y s origin facts legal f.selectorG_zero f.selectorS_zero
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) records s = v := ⟨_, rfl⟩
  have input := frames false
  rw [lf_eq, hv] at input
  rw [hv]
  have bits := Rolling1588Lifetime.first_clean false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  have work := Rolling1588Lifetime.first_work_zero false f.sharedNodup f.x f.Y.val s
    records f.input
  have parity := Rolling1588Lifetime.first_parity false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  rw [lf_eq] at bits work parity
  rw [hv] at bits work parity
  have code := Rolling1588Frame.canonical_special_at origin.basis f.Y 0 v 511 (by simp) input
  have fixed : OB5.sig 511 (base 511) = base 511 := by decide +kernel
  rw [fixed] at code
  have in511 : v.basis (base 511) = true :=
    code.trans (trace_last f.x f.x_pos f.x_lt origin.basis facts.trace)
  have in1542 : v.basis (base 1542) = false :=
    bits _ (by simp [FrontierEntry1591Native.workSites])
  have flags := canonical_flags origin.basis ctx f.Y 0 v input
  -- the forced record frame
  let origin' := writeBit origin.basis (base 2400) true
  have ctx' := FrontierEntry1591.context_control_set origin.basis ctx true
  have ha' := FrontierEntry1591.source_zero_control_set origin.basis true facts.sourceZero
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (f.x : Int) (p : Int)) := by
    rw [FrontierEntry1591.trace_control_set]
    exact facts.trace
  have input' := Rolling1588.canonical_control_set origin.basis f.Y 0 v true input
  have enabled' : origin' (base 2400) = true := by
    simp only [origin', writeBit, Function.update_self]
  have codes := Rolling1588.canonical_prefix_codes origin' ctx' f.Y 0 (force v) input'
    f.x f.x_pos f.x_lt trace'
  have clean := FourScratchWindow.canonical_clean origin' ctx' ha' f.Y (force v) input'
    codes.1 codes.2.1
  have z768 := Rolling1588.canonical_768_zero origin' ctx' f.Y 0 (force v) input'
  -- split the head
  rw [headEL_shape, headEL_shape,
    run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram)
      (liftF (StairLoanExitHeadReplay.headPrefixShape StairConcrete.bestLoans)),
    run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram)
      (liftF (StairLoanExitHeadReplay.headPrefixShape StairSchedule.recordLoans)),
    StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run]
  apply congrArg StairField2V3Seg.pullOut
  apply StairLoanField7Transport.replay_transfer _ _ _ (force v) _ _ headPrefix_sub
  · intro q hq
    obtain ⟨hE, hP⟩ := exitHead_avoid q (headPrefix_record_sub hq)
    rw [run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX), field_pullIn]
    exact window_agree _ (force v) _
      (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity _)
      clean codes.2.2 z768 q hE hP
  · exact headPrefix_run_eq_of half hEnd origin' ctx' ha' enabled'
      f.Y (force v) input' _ _




/-! ## Entry: avoidance -/









/-! ## Entry: the loaned groups on the record trajectory -/

theorem R0_shape :
    R0 ++ firstPkt =
      renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
        (StairSchedule.paritySetup ++ StairSchedule.hostedX) ++
        StairSchedule.fieldRename (Rolling1588.placedFirstPacket true ++
          FourScratchWindow.clearProgram) := by
  simp only [R0, prefixW, refJ0, firstPkt, ph, Rolling1588TickGap.firstPhase,
    Rolling1588TickGap.tailPhase, Rolling1588TickGap.stackForward, Six505.stackForward6,
    forward_504, rename_append', List.append_assoc]


theorem entryGroups_run (half : StairLoanRecordShape.HalfReplayHypothesis) (t0 : State)
    (ht0 : StairConcreteAssembly.EntryPre t0) (m0 a b : List Bool)
    (L : List (Nat × Nat × Nat)) (hL : StairLoanRecordShape.ForwardChain 1 L)
    (hn : StairLoanRecordShape.sliceCount L ≤ 101) :
    run (liftF (renameProgram (OB5.sig 511)
        (StairLoanRecordShape.slices StairConcrete.bestLoans true L))) a
          (run (R0 ++ firstPkt) m0 t0) =
      run (liftF (renameProgram (OB5.sig 511)
        (StairLoanRecordShape.slices StairSchedule.recordLoans true L))) b
          (run (R0 ++ firstPkt) m0 t0) := by
  rcases ht0 with ⟨f⟩
  have actual := FrontierEntry1591Kernel.paired_input f.x f.Y.val f.source t0 f.input
    f.outsideNumerator
  rw [R0_shape,
    run_append (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true) ++
      (StairSchedule.paritySetup ++ StairSchedule.hostedX)),
    run_append (renameProgram Rolling1588Lifetime.phaseHost (Rolling1588TickGap.firstPhase true)),
    first_phase_hosted true f.sharedNodup f.historyAbove f.x _ f.x_pos f.x_lt t0 _ actual]
  exact entryGroups_inner half t0 f _ _ _ a b L hL hn


theorem RL_shape1 (loans : StairSchedule.StairLoans) :
    StairLoanField7Transport.R1L loans = (R0 ++ firstPkt) ++ liftF (renameProgram (OB5.sig 511)
      (StairLoanRecordShape.slices loans true [(0, 1, 84)])) := by
  simp only [StairLoanField7Transport.R1L, StairLoanField7Transport.grpL,
    StairSchedule.placedGroups, StairLoanRecordShape.slices, liftF, StairSchedule.fieldRename,
    StairSchedule.parityRename, rename_append', StairLoanField7Transport.rename_nil,
    List.append_nil, List.append_assoc]

theorem RL_shape2 (loans : StairSchedule.StairLoans) :
    StairLoanField7Transport.R2L loans = (R0 ++ firstPkt) ++ liftF (renameProgram (OB5.sig 511)
      (StairLoanRecordShape.slices loans true [(0, 1, 84), (13, 85, 5)])) := by
  simp only [StairLoanField7Transport.R2L, StairLoanField7Transport.R1L,
    StairLoanField7Transport.grpL,
    StairSchedule.placedGroups, StairLoanRecordShape.slices, liftF, StairSchedule.fieldRename,
    StairSchedule.parityRename, rename_append', StairLoanField7Transport.rename_nil,
    List.append_nil, List.append_assoc]

theorem RL_shape3 (loans : StairSchedule.StairLoans) :
    StairLoanField7Transport.R3L loans = (R0 ++ firstPkt) ++ liftF (renameProgram (OB5.sig 511)
      (StairLoanRecordShape.slices loans true [(0, 1, 84), (13, 85, 5), (22, 90, 3)])) := by
  simp only [StairLoanField7Transport.R3L, StairLoanField7Transport.R2L,
    StairLoanField7Transport.R1L, StairLoanField7Transport.grpL,
    StairSchedule.placedGroups, StairLoanRecordShape.slices, liftF, StairSchedule.fieldRename,
    StairSchedule.parityRename, rename_append', StairLoanField7Transport.rename_nil,
    List.append_nil, List.append_assoc]

theorem RL_shape4 (loans : StairSchedule.StairLoans) :
    StairLoanField7Transport.R4L loans = (R0 ++ firstPkt) ++ liftF (renameProgram (OB5.sig 511)
      (StairLoanRecordShape.slices loans true
        [(0, 1, 84), (13, 85, 5), (22, 90, 3), (30, 93, 3)])) := by
  simp only [StairLoanField7Transport.R4L, StairLoanField7Transport.R3L,
    StairLoanField7Transport.R2L, StairLoanField7Transport.R1L, StairLoanField7Transport.grpL,
    StairSchedule.placedGroups, StairLoanRecordShape.slices, liftF, StairSchedule.fieldRename,
    StairSchedule.parityRename, rename_append', StairLoanField7Transport.rename_nil,
    List.append_nil, List.append_assoc]

theorem RL_shape5 (loans : StairSchedule.StairLoans) :
    StairLoanField7Transport.R5L loans = (R0 ++ firstPkt) ++ liftF (renameProgram (OB5.sig 511)
      (StairLoanRecordShape.slices loans true
        [(0, 1, 84), (13, 85, 5), (22, 90, 3), (30, 93, 3), (36, 96, 2)])) := by
  simp only [StairLoanField7Transport.R5L, StairLoanField7Transport.R4L,
    StairLoanField7Transport.R3L,
    StairLoanField7Transport.R2L, StairLoanField7Transport.R1L, StairLoanField7Transport.grpL,
    StairSchedule.placedGroups, StairLoanRecordShape.slices, liftF, StairSchedule.fieldRename,
    StairSchedule.parityRename, rename_append', StairLoanField7Transport.rename_nil,
    List.append_nil, List.append_assoc]

theorem RL_shape6 (loans : StairSchedule.StairLoans) :
    StairLoanField7Transport.R6L loans = (R0 ++ firstPkt) ++ liftF (renameProgram (OB5.sig 511)
      (StairLoanRecordShape.slices loans true
        [(0, 1, 84), (13, 85, 5), (22, 90, 3), (30, 93, 3), (36, 96, 2), (41, 98, 2)])) := by
  simp only [StairLoanField7Transport.R6L, StairLoanField7Transport.R5L,
    StairLoanField7Transport.R4L, StairLoanField7Transport.R3L,
    StairLoanField7Transport.R2L, StairLoanField7Transport.R1L, StairLoanField7Transport.grpL,
    StairSchedule.placedGroups, StairLoanRecordShape.slices, liftF, StairSchedule.fieldRename,
    StairSchedule.parityRename, rename_append', StairLoanField7Transport.rename_nil,
    List.append_nil, List.append_assoc]

theorem R1_eq : StairLoanField7Transport.R1L StairSchedule.recordLoans = R1 := by
  simp only [StairLoanField7Transport.R1L, R1, StairLoanField7Transport.grpL_record]

theorem R2_eq : StairLoanField7Transport.R2L StairSchedule.recordLoans = R2 := by
  simp only [StairLoanField7Transport.R2L, R2, R1_eq, StairLoanField7Transport.grpL_record]

theorem R3_eq : StairLoanField7Transport.R3L StairSchedule.recordLoans = R3 := by
  simp only [StairLoanField7Transport.R3L, R3, R2_eq, StairLoanField7Transport.grpL_record]

theorem R4_eq : StairLoanField7Transport.R4L StairSchedule.recordLoans = R4 := by
  simp only [StairLoanField7Transport.R4L, R4, R3_eq, StairLoanField7Transport.grpL_record]

theorem R5_eq : StairLoanField7Transport.R5L StairSchedule.recordLoans = R5 := by
  simp only [StairLoanField7Transport.R5L, R5, R4_eq, StairLoanField7Transport.grpL_record]

theorem R6_eq : StairLoanField7Transport.R6L StairSchedule.recordLoans = R6 := by
  simp only [StairLoanField7Transport.R6L, R6, R5_eq, StairLoanField7Transport.grpL_record]


/-! ## Field 7 with every input discharged except LT21's record plans -/


/-! ## On CANON 1945 (LT19 endpoint landed in the `endPacket false 68` slot) -/




end ECDSAAdd.Entrant.StairLoanField7Values

end
end Merge_StairLoanField7Values_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairLoanExitReachX_at_BOptimizations` -/
section Merge_StairLoanExitReachX_at_BOptimizations

/-!
# Multiplication side: the loaned reference prefixes reach only record states (LT29)

LT43's multiplication plan `ExitPlanR p k x` states its reverse-segment steps for a
reference state reached through the RECORD prefixes `YA … YE` (`ReachE k x Y t`).  In the
`bestLoans` kernel the reference prefixes are the loaned ones (`headEL ++ grpFL …`).
This module proves that every state reached through a loaned prefix is reached through
the record prefix (same input, same tape):

* `exitHeadL_run` — LT32's `exitHead_run` with the head's backward slice list extended
  by any backward chain `M` (`headELL loans M`);
* `reachX_head`, `reachX_A … reachX_F` — the six transports, with the input `x` pinned.

It is the multiplication analogue of LT32's `entryReachTransport_best`, and the input
field 7 needs when the multiplication plan is `ExitPlanR`.  Variable programs only.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairLoanExitReachX

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairLoanRecordShape StairLoanField7Values StairField2V3ExitPlanR

attribute [local irreducible] wires run

/-! ## The head with an extended backward slice list -/











/-! ## Record-frame replay of the extended head -/



/-! ## The extended loaned head on `ExitMiddle` states -/

theorem exitHeadL_run (half : HalfReplayHypothesis)
    (hEnd : EndpointReplay StairConcrete.bestLoans) (k : Nat) (t : State)
    (ht : StairField2V3Core.ExitMiddle k t) (m : List Bool)
    (M : List (Nat × Nat × Nat)) (low : Nat) (chain : BackwardChain 100 low M)
    (hlow : 1 ≤ low) :
    run (headELL StairConcrete.bestLoans M) m t =
      run (headELL StairSchedule.recordLoans M) m t := by
  obtain ⟨s, ⟨f⟩, records, rfl⟩ := ht
  have opening : run StairField2V3Replay.exitReferenceOpening records s =
      run (Rolling1588.firstPhase false) records s :=
    first_phase_hosted false f.sharedNodup f.historyAbove f.x f.Y.val f.x_pos f.x_lt s
      records f.input
  rw [opening]
  obtain ⟨origin, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
    f.sharedNodup f.historyAbove f.selectorsAway f.x f.Y f.x_pos f.x_lt s records f.input
  have ctx := Rolling1588Lifetime.prepared_context f.sharedNodup f.selectorsAway
    f.transcript f.x f.Y s origin facts legal f.selectorG_zero f.selectorS_zero
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) records s = v := ⟨_, rfl⟩
  have input := frames false
  rw [lf_eq, hv] at input
  rw [hv]
  have bits := Rolling1588Lifetime.first_clean false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  have work := Rolling1588Lifetime.first_work_zero false f.sharedNodup f.x f.Y.val s
    records f.input
  have parity := Rolling1588Lifetime.first_parity false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  rw [lf_eq] at bits work parity
  rw [hv] at bits work parity
  have code := Rolling1588Frame.canonical_special_at origin.basis f.Y 0 v 511 (by simp) input
  have fixed : OB5.sig 511 (base 511) = base 511 := by decide +kernel
  rw [fixed] at code
  have in511 : v.basis (base 511) = true :=
    code.trans (trace_last f.x f.x_pos f.x_lt origin.basis facts.trace)
  have in1542 : v.basis (base 1542) = false :=
    bits _ (by simp [FrontierEntry1591Native.workSites])
  have flags := canonical_flags origin.basis ctx f.Y 0 v input
  -- the forced record frame
  let origin' := writeBit origin.basis (base 2400) true
  have ctx' := FrontierEntry1591.context_control_set origin.basis ctx true
  have ha' := FrontierEntry1591.source_zero_control_set origin.basis true facts.sourceZero
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (f.x : Int) (p : Int)) := by
    rw [FrontierEntry1591.trace_control_set]
    exact facts.trace
  have input' := Rolling1588.canonical_control_set origin.basis f.Y 0 v true input
  have enabled' : origin' (base 2400) = true := by
    simp only [origin', writeBit, Function.update_self]
  have codes := Rolling1588.canonical_prefix_codes origin' ctx' f.Y 0 (force v) input'
    f.x f.x_pos f.x_lt trace'
  have clean := FourScratchWindow.canonical_clean origin' ctx' ha' f.Y (force v) input'
    codes.1 codes.2.1
  have z768 := Rolling1588.canonical_768_zero origin' ctx' f.Y 0 (force v) input'
  -- split the head
  unfold headELL
  rw [run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram)
      (liftF (headShapeL StairConcrete.bestLoans M)),
    run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX ++
      StairSchedule.fieldRename FourScratchWindow.clearProgram)
      (liftF (headShapeL StairSchedule.recordLoans M)),
    StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run]
  apply congrArg StairField2V3Seg.pullOut
  apply StairLoanField7Transport.replay_transfer _ _ _ (force v) _ _
    (headShapeL_sub M low chain)
  · intro q hq
    obtain ⟨hE, hP⟩ := exitHead_avoid q (headShapeL_record_sub M low chain hlow hq)
    rw [run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX), field_pullIn]
    exact window_agree _ (force v) _
      (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity _)
      clean codes.2.2 z768 q hE hP
  · exact headShapeL_run_eq half hEnd origin' ctx' ha' enabled'
      f.Y (force v) input' M low chain _ _

/-! ## Shapes: head ++ groups = extended head -/



/-! ## Reach transports with the input pinned -/


/-- Generic transport: the extended loaned head reaches only states of the record one. -/
theorem reachX_gen (half : HalfReplayHypothesis) (k x : Nat)
    (M : List (Nat × Nat × Nat)) (low : Nat) (chain : BackwardChain 100 low M)
    (hlow : 1 ≤ low) (t : State)
    (ht : ReachBy (ExitMiddleX k x) (headELL StairConcrete.bestLoans M) t) :
    ReachBy (ExitMiddleX k x) (headELL StairSchedule.recordLoans M) t := by
  obtain ⟨s0, m, hs0, rfl⟩ := ht
  exact ⟨s0, m, hs0, exitHeadL_run half bestEnd k s0 (exitMiddle_of_x k x s0 hs0) m M low
    chain hlow⟩






theorem reachX_head (half : HalfReplayHypothesis) (k x : Nat) (t : State)
    (ht : ReachBy (ExitMiddleX k x) ZH t) : ReachE k x headE t := by
  obtain ⟨s0, m, hs0, rfl⟩ := ht
  refine ⟨s0, m, hs0, ?_⟩
  rw [← StairLoanField7Transport.headEL_record]
  exact exitHead_run half bestEnd k s0 (exitMiddle_of_x k x s0 hs0) m

theorem reachX_A (half : HalfReplayHypothesis) (k x : Nat) (t : State)
    (ht : ReachBy (ExitMiddleX k x) ZA t) : ReachE k x YA t := by
  rw [ZA_eq] at ht
  rw [YA_eq]
  exact reachX_gen half k x MA 98 (by simp [BackwardChain, MA]) (by omega) t ht

theorem reachX_B (half : HalfReplayHypothesis) (k x : Nat) (t : State)
    (ht : ReachBy (ExitMiddleX k x) ZB t) : ReachE k x YB t := by
  rw [ZB_eq] at ht
  rw [YB_eq]
  exact reachX_gen half k x MB 96 (by simp [BackwardChain, MB]) (by omega) t ht

theorem reachX_C (half : HalfReplayHypothesis) (k x : Nat) (t : State)
    (ht : ReachBy (ExitMiddleX k x) ZC t) : ReachE k x YC t := by
  rw [ZC_eq] at ht
  rw [YC_eq]
  exact reachX_gen half k x MC 93 (by simp [BackwardChain, MC]) (by omega) t ht

theorem reachX_D (half : HalfReplayHypothesis) (k x : Nat) (t : State)
    (ht : ReachBy (ExitMiddleX k x) ZD t) : ReachE k x YD t := by
  rw [ZD_eq] at ht
  rw [YD_eq]
  exact reachX_gen half k x MD 90 (by simp [BackwardChain, MD]) (by omega) t ht

theorem reachX_E (half : HalfReplayHypothesis) (k x : Nat) (t : State)
    (ht : ReachBy (ExitMiddleX k x) ZE t) : ReachE k x YE t := by
  rw [ZE_eq] at ht
  rw [YE_eq]
  exact reachX_gen half k x ME 85 (by simp [BackwardChain, ME]) (by omega) t ht


end ECDSAAdd.Entrant.StairLoanExitReachX

end
end Merge_StairLoanExitReachX_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairLoanField7R_at_BOptimizations` -/
section Merge_StairLoanField7R_at_BOptimizations

/-!
# LT43e: field 7 from the multiplication plan with reachability (`ExitPlanR`)

`StairLoanField7Values.loan_composition_final` needs LT21's generic `ExitPlan`, which
cannot be instantiated (its relations carry no reachability).  LT43's `ExitPlanR p k x`
carries `ReachBy (ExitMiddleX k x) Y t` for the RECORD reference prefixes `YA..YF`.
In the loaned chain the reference prefixes are the LOANED ones (`YAL..YFL bestLoans`), so
every step of the plan needs the exit reach transport

  `ReachBy (ExitMiddleX k x) (Y?L bestLoans) t → ReachBy (ExitMiddleX k x) Y? t`.

All six cuts (and the head) have the same shape

  `PRE ++ liftF (center ++ copyN ++ rename (sig 511) (endpoint 68 ++ slices L))`

with `L` a prefix of the multiplication slice list (a `BackwardChain 102 low L`), so one
run equality (`exitShape_run`, LT32's `exitHead_run` for an arbitrary backward chain `L`)
gives all of them; `lowTail` is a shared tail (`reach_tail`).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairLoanField7R

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan
open StairField2V3ExitPlanR StairLoanField7Transport StairLoanField7Values
open StairLoanRecordShape

attribute [local irreducible] wires run

/-! ## The common shape of the loaned reference prefixes -/





/-! ## Loaned reference prefixes (left-nested, as produced by `crel_track`) -/















/-! ## Wires -/






/-! ## Record-frame replay for an arbitrary backward chain -/



/-! ## The loaned prefix on `ExitMiddle` states -/

/-- LT32's `exitHead_run` for an arbitrary backward chain `L` (independent tapes for the
lifted block). -/
theorem exitShape_run (half : HalfReplayHypothesis)
    (hEnd : EndpointReplay StairConcrete.bestLoans) (k : Nat) (t : State)
    (ht : StairField2V3Core.ExitMiddle k t)
    (L : List (Nat × Nat × Nat)) (low : Nat) (hlow : 1 ≤ low)
    (chain : BackwardChain 102 low L) (mP a b : List Bool) :
    run (liftF (headShape StairConcrete.bestLoans L)) a (run PRE mP t) =
      run (liftF (headShape StairSchedule.recordLoans L)) b (run PRE mP t) := by
  obtain ⟨s, ⟨f⟩, records, rfl⟩ := ht
  have opening : run StairField2V3Replay.exitReferenceOpening records s =
      run (Rolling1588.firstPhase false) records s :=
    first_phase_hosted false f.sharedNodup f.historyAbove f.x f.Y.val f.x_pos f.x_lt s
      records f.input
  rw [opening]
  obtain ⟨origin, facts, legal, frames⟩ := Rolling1588Lifetime.first_prepared
    f.sharedNodup f.historyAbove f.selectorsAway f.x f.Y f.x_pos f.x_lt s records f.input
  have ctx := Rolling1588Lifetime.prepared_context f.sharedNodup f.selectorsAway
    f.transcript f.x f.Y s origin facts legal f.selectorG_zero f.selectorS_zero
  obtain ⟨v, hv⟩ : ∃ v : State, run (Rolling1588.firstPhase false) records s = v := ⟨_, rfl⟩
  have input := frames false
  rw [lf_eq, hv] at input
  rw [hv]
  have bits := Rolling1588Lifetime.first_clean false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  have work := Rolling1588Lifetime.first_work_zero false f.sharedNodup f.x f.Y.val s
    records f.input
  have parity := Rolling1588Lifetime.first_parity false f.sharedNodup f.historyAbove f.x
    f.Y.val f.x_pos f.x_lt s records f.input
  rw [lf_eq] at bits work parity
  rw [hv] at bits work parity
  have code := Rolling1588Frame.canonical_special_at origin.basis f.Y 0 v 511 (by simp) input
  have fixed : OB5.sig 511 (base 511) = base 511 := by decide +kernel
  rw [fixed] at code
  have in511 : v.basis (base 511) = true :=
    code.trans (trace_last f.x f.x_pos f.x_lt origin.basis facts.trace)
  have in1542 : v.basis (base 1542) = false :=
    bits _ (by simp [FrontierEntry1591Native.workSites])
  have flags := canonical_flags origin.basis ctx f.Y 0 v input
  -- the forced record frame
  let origin' := writeBit origin.basis (base 2400) true
  have ctx' := FrontierEntry1591.context_control_set origin.basis ctx true
  have ha' := FrontierEntry1591.source_zero_control_set origin.basis true facts.sourceZero
  have trace' : skywalkTapeControls origin' (skywalkSharedTape base) =
      SkywalkTrace.trace 512 (SkywalkRails.encode false false (f.x : Int) (p : Int)) := by
    rw [FrontierEntry1591.trace_control_set]
    exact facts.trace
  have input' := Rolling1588.canonical_control_set origin.basis f.Y 0 v true input
  have enabled' : origin' (base 2400) = true := by
    simp only [origin', writeBit, Function.update_self]
  have codes := Rolling1588.canonical_prefix_codes origin' ctx' f.Y 0 (force v) input'
    f.x f.x_pos f.x_lt trace'
  have clean := FourScratchWindow.canonical_clean origin' ctx' ha' f.Y (force v) input'
    codes.1 codes.2.1
  have z768 := Rolling1588.canonical_768_zero origin' ctx' f.Y 0 (force v) input'
  rw [StairField2V3Seg.liftF_run, StairField2V3Seg.liftF_run]
  apply congrArg StairField2V3Seg.pullOut
  apply replay_transfer _ _ _ (force v) _ _ (headShape_sub L 102 low chain)
  · intro q hq
    obtain ⟨hE, hP⟩ := exitHead_avoid q (headShape_record_sub L low hlow chain hq)
    unfold PRE
    rw [run_append (StairSchedule.paritySetup ++ StairSchedule.hostedX), field_pullIn]
    exact window_agree _ (force v) _
      (hosted_agree_force v flags.1 in511 flags.2 in1542 work parity _)
      clean codes.2.2 z768 q hE hP
  · exact headShape_run_eq half hEnd L low chain origin' ctx' ha' enabled'
      f.Y (force v) input' _ _

/-- One loaned reference prefix reaches only record-reachable states. -/
theorem reach_shape (half : HalfReplayHypothesis)
    (hEnd : EndpointReplay StairConcrete.bestLoans) (k x : Nat)
    (L : List (Nat × Nat × Nat)) (low : Nat) (hlow : 1 ≤ low)
    (chain : BackwardChain 102 low L) (t : State)
    (ht : ReachE k x (PRE ++ liftF (headShape StairConcrete.bestLoans L)) t) :
    ReachE k x (PRE ++ liftF (headShape StairSchedule.recordLoans L)) t := by
  obtain ⟨s0, m, hs0, rfl⟩ := ht
  refine ⟨s0, m, hs0, ?_⟩
  rw [run_append PRE, run_append PRE]
  exact exitShape_run half hEnd k s0 (exitMiddle_of_x k x s0 hs0) L low hlow chain _ _ _


/-! ## The exit reach transport -/

/-- VALUE-dependent input (record trajectory only): the loaned multiplication reference
prefixes reach, from `ExitMiddleX k x`, only states the record prefixes reach. -/
structure ExitReachTransportR (loans : StairSchedule.StairLoans) (k x : Nat) : Prop where
  head : ∀ t, ReachE k x (headEL loans) t → ReachE k x headE t
  a : ∀ t, ReachE k x (YAL loans) t → ReachE k x YA t
  b : ∀ t, ReachE k x (YBL loans) t → ReachE k x YB t
  c : ∀ t, ReachE k x (YCL loans) t → ReachE k x YC t
  d : ∀ t, ReachE k x (YDL loans) t → ReachE k x YD t
  e : ∀ t, ReachE k x (YEL loans) t → ReachE k x YE t
  f : ∀ t, ReachE k x (YFL loans) t → ReachE k x YF t

theorem exitReachTransportR_of (half : HalfReplayHypothesis)
    (hEnd : EndpointReplay StairConcrete.bestLoans) (k x : Nat) :
    ExitReachTransportR StairConcrete.bestLoans k x where
  head := by
    intro t ht
    rw [YHL_shape] at ht
    have h := reach_shape half hEnd k x SlH 100 (by omega) SlH_chain t ht
    rw [← YHL_shape, headEL_record] at h
    exact h
  a := by
    intro t ht
    rw [YAL_shape] at ht
    have h := reach_shape half hEnd k x SlA 98 (by omega) SlA_chain t ht
    rw [← YAL_shape, YA_eq] at h
    exact h
  b := by
    intro t ht
    rw [YBL_shape] at ht
    have h := reach_shape half hEnd k x SlB 96 (by omega) SlB_chain t ht
    rw [← YBL_shape, YB_eq] at h
    exact h
  c := by
    intro t ht
    rw [YCL_shape] at ht
    have h := reach_shape half hEnd k x SlC 93 (by omega) SlC_chain t ht
    rw [← YCL_shape, YC_eq] at h
    exact h
  d := by
    intro t ht
    rw [YDL_shape] at ht
    have h := reach_shape half hEnd k x SlD 90 (by omega) SlD_chain t ht
    rw [← YDL_shape, YD_eq] at h
    exact h
  e := by
    intro t ht
    rw [YEL_shape] at ht
    have h := reach_shape half hEnd k x SlE 85 (by omega) SlE_chain t ht
    rw [← YEL_shape, YE_eq] at h
    exact h
  f := by
    have g : ∀ u, ReachE k x (YGL StairConcrete.bestLoans) u →
        ReachE k x (YGL StairSchedule.recordLoans) u := by
      intro u hu
      rw [YGL_shape] at hu
      have h := reach_shape half hEnd k x SlF 1 (by omega) SlF_chain u hu
      rw [← YGL_shape] at h
      exact h
    intro t ht
    have h := reach_tail (ExitMiddleX k x) _ _ lowTail g t ht
    have e : YGL StairSchedule.recordLoans ++ lowTail = YF := YF_eq
    rw [e] at h
    exact h

/-- **`ExitReachTransportR bestLoans k x`** with no endpoint hypothesis (LT19's replay). -/
theorem exitReachTransportR_best (half : HalfReplayHypothesis) (k x : Nat) :
    ExitReachTransportR StairConcrete.bestLoans k x :=
  exitReachTransportR_of half (endpointReplay_loan44 _ bestEnd44) k x

/-! ## The loaned chain in the R form -/

def JEXL (loans : StairSchedule.StairLoans) (k x : Nat) (s t : State) : Prop :=
  s = t ∧ ReachE k x (headEL loans) s

theorem crel_headXL (loans : StairSchedule.StairLoans) (k x : Nat) :
    CRel (fun s t => ExitMiddleX k x s ∧ s = t) (JEXL loans k x)
      (headEL loans) (headEL loans) := by
  rintro s t ⟨hs, rfl⟩ fresh
  exact ⟨fresh, rfl, s, fresh, hs, rfl⟩


theorem stepL {k x B B' : Nat} {XL X Q : Program}
    (tr : ∀ t, ReachE k x XL t → ReachE k x X t)
    (h : CRel (RowRelE k x B X) (RelX x B') Q []) :
    CRel (RowRelE k x B XL) (RowRelE k x B' XL) Q [] :=
  segE (crel_mono (fun _ t hst => ⟨hst.1, tr t hst.2⟩) (fun _ _ y => y) h)



/-! ## Assembly: field 7 -/




/-! ## Wiring test (the two `StairOpenWiring` fields from the `Nonempty` plans) -/



end ECDSAAdd.Entrant.StairLoanField7R

end
end Merge_StairLoanField7R_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairLoanField7RR_at_BOptimizations` -/
section Merge_StairLoanField7RR_at_BOptimizations

/-!
# LT43g: field 7 with BOTH plans pinned (`EntryPlanR`, `ExitPlanR`)

`StairLoanField7R.loan_composition_R` (LT43e) still takes LT21's unpinned division
plan `EntryPlan`, which cannot be instantiated (the last step needs the genuine input,
LT43c F3).  Here the division half of LT32's transport is ported to the pinned chain:

  `ReachEn x (RᵢL bestLoans) t → ReachEn x Rᵢ t`      (`EntryReachTransportR`)

The proof is LT32's run equality `StairLoanField7Values.entryGroups_run` on the same
start state, so the pin is free.  `loan_composition_RR` is field 7 from the two pinned
plan families; `loan_composition_final_RR` plugs in LT43g's instances, leaving the two
record facts `LastRecX` / `JuncRecX` (owner LT43h).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairLoanField7RR

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField
open StairField2V3Replay StairField2V3Couple StairField2V3Entry
open StairField2V3ExitPlanR StairField2V3EntryPlanR
open StairLoanField7Transport StairLoanField7Values
open StairField2V3Delta

attribute [local irreducible] wires run


/-! ## The division reach transport with a pinned input -/

/-- One loaned reference prefix reaches, from a division input of input `x`, only
record-reachable states (LT32 `reach_transport`, pinned). -/
theorem reach_transportX (half : StairLoanRecordShape.HalfReplayHypothesis) (x : Nat)
    (L : List (Nat × Nat × Nat)) (hL : StairLoanRecordShape.ForwardChain 1 L)
    (hn : StairLoanRecordShape.sliceCount L ≤ 101) (t : State)
    (ht : ReachEn x ((R0 ++ firstPkt) ++ liftF (renameProgram (OB5.sig 511)
      (StairLoanRecordShape.slices StairConcrete.bestLoans true L))) t) :
    ReachEn x ((R0 ++ firstPkt) ++ liftF (renameProgram (OB5.sig 511)
      (StairLoanRecordShape.slices StairSchedule.recordLoans true L))) t := by
  obtain ⟨s0, m, hs0, rfl⟩ := ht
  refine ⟨s0, m, hs0, ?_⟩
  rw [run_append (R0 ++ firstPkt), run_append (R0 ++ firstPkt)]
  exact entryGroups_run half s0 (entryPre_of_x x s0 hs0) _ _ _ L hL hn

/-- VALUE-dependent input (record trajectory only): the loaned division reference
prefixes reach, from `EntryPreX x`, only states the record prefixes reach. -/
structure EntryReachTransportR (loans : StairSchedule.StairLoans) (x : Nat) : Prop where
  r1 : ∀ t, ReachEn x (R1L loans) t → ReachEn x R1 t
  r2 : ∀ t, ReachEn x (R2L loans) t → ReachEn x R2 t
  r3 : ∀ t, ReachEn x (R3L loans) t → ReachEn x R3 t
  r4 : ∀ t, ReachEn x (R4L loans) t → ReachEn x R4 t
  r5 : ∀ t, ReachEn x (R5L loans) t → ReachEn x R5 t
  r6 : ∀ t, ReachEn x (R6L loans) t → ReachEn x R6 t

/-- **`EntryReachTransportR bestLoans x`** (LT32 `entryReachTransport_best`, pinned). -/
theorem entryReachTransportR_best (half : StairLoanRecordShape.HalfReplayHypothesis)
    (x : Nat) : EntryReachTransportR StairConcrete.bestLoans x where
  r1 := by
    intro t ht
    rw [RL_shape1] at ht
    have h := reach_transportX half x _ (by simp [StairLoanRecordShape.ForwardChain])
      (by simp [StairLoanRecordShape.sliceCount]) t ht
    rw [← RL_shape1, R1_eq] at h
    exact h
  r2 := by
    intro t ht
    rw [RL_shape2] at ht
    have h := reach_transportX half x _ (by simp [StairLoanRecordShape.ForwardChain])
      (by simp [StairLoanRecordShape.sliceCount]) t ht
    rw [← RL_shape2, R2_eq] at h
    exact h
  r3 := by
    intro t ht
    rw [RL_shape3] at ht
    have h := reach_transportX half x _ (by simp [StairLoanRecordShape.ForwardChain])
      (by simp [StairLoanRecordShape.sliceCount]) t ht
    rw [← RL_shape3, R3_eq] at h
    exact h
  r4 := by
    intro t ht
    rw [RL_shape4] at ht
    have h := reach_transportX half x _ (by simp [StairLoanRecordShape.ForwardChain])
      (by simp [StairLoanRecordShape.sliceCount]) t ht
    rw [← RL_shape4, R4_eq] at h
    exact h
  r5 := by
    intro t ht
    rw [RL_shape5] at ht
    have h := reach_transportX half x _ (by simp [StairLoanRecordShape.ForwardChain])
      (by simp [StairLoanRecordShape.sliceCount]) t ht
    rw [← RL_shape5, R5_eq] at h
    exact h
  r6 := by
    intro t ht
    rw [RL_shape6] at ht
    have h := reach_transportX half x _ (by simp [StairLoanRecordShape.ForwardChain])
      (by simp [StairLoanRecordShape.sliceCount]) t ht
    rw [← RL_shape6, R6_eq] at h
    exact h

/-! ## The loaned division chain in the R form -/




/-! ## Assembly: field 7 -/





/-! ## Wiring test (the two `StairOpenWiring` fields from the `Nonempty` pinned plans) -/




end ECDSAAdd.Entrant.StairLoanField7RR

end
end Merge_StairLoanField7RR_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairPhysicalV3_at_BOptimizations` -/
section Merge_StairPhysicalV3_at_BOptimizations

/-!
# Field 9 for CANON v3, parametric in the slots

`Sound P` = `GatePhysical P` and every label of `P` in `InDom` (the 2,326
caller labels on which the record placement `wireFn2` is injective).  Every
rename inside the hosted rests preserves `InDom`, so soundness composes.

The v3 hosted rests are assembled from

* record pieces (proved here),
* the loaned packet groups (proved here from the field-9 antecedent),
* first packets rebound on a host list, exclusive roles (proved here, given
  the host list is in `InDom`),
* the **slots**: the primitive provider `p` (`PrimitiveSlots p`), the
  boundary programs of the loan provider `StairConcrete.bestLoans`
  (`BoundarySlots`: both endpoints, `canon`, `center`) and the host plan
  (`HostSlots h`).

`entryLocal_sound` / `exitLocal_sound` hold for ANY `p`, `h`; the concrete
field-9 statement `physical_composition_of_slots` then needs only the three
slot facts for `checkpointPrimitives`, `bestLoans` and `hostPlan`.  No proof
here unfolds `StairConcrete.bestLoans.endPacket/canon/center` or a field of
`p`, so replacing those programs only changes the slot proofs.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairPhysicalV3

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open StairRestSupport

/-! ## Soundness and its composition -/














/-! ## Record pieces -/




theorem movedForward_physical (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (i n : Nat)
    (bound : i + n ≤ 512) :
    GatePhysical (StairReplay.movedForward w i n) := by
  induction n generalizing i with
  | zero => simp [StairReplay.movedForward, GatePhysical]
  | succ n ih =>
      simp only [StairReplay.movedForward, gatePhysical_append]
      exact ⟨⟨TickRanges.tick_physical w i (by omega) hn,
          packFirst_physical w hn true i (by omega)⟩,
        ih (i + 1) (by omega)⟩

theorem movedReverse_physical (w : Nat → Wire)
    (hn : (skywalkPoolWires w).Nodup) (i n : Nat)
    (bound : i + n ≤ 512) :
    GatePhysical (StairReplay.movedReverse w i n) := by
  induction n generalizing i with
  | zero => simp [StairReplay.movedReverse, GatePhysical]
  | succ n ih =>
      simp only [StairReplay.movedReverse, gatePhysical_append]
      exact ⟨ih (i + 1) (by omega),
        unpackFirst_physical w hn true i (by omega),
        W.ReverseCarry.compactReceiverTick_physical w i (by omega) hn⟩




















/-! ## Loaned packet groups (from the field-9 antecedent's support) -/











/-! ## The slots -/






/-! ## Generic composition of the v3 schedule -/

section Generic















end Generic

/-! ## The literal outer caller chain of the v3 `concreteProgram` -/






end ECDSAAdd.Entrant.StairPhysicalV3

end
end Merge_StairPhysicalV3_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairPhysicalV3Instance_at_BOptimizations` -/
section Merge_StairPhysicalV3Instance_at_BOptimizations

/-!
# Field 9 on CANON v3: the slot instances for the tree as built

* `hostSlots_v3` — the v3 host plan (`StairV3Primitives.hostPlan`: LT13's
  `hosts` of the live row, first packets on `hosts 87`);
* `boundarySlots_current` — the loan provider as built in CANON 1719
  (division endpoint `endPacket760DivLoan` (LT8/LT18), `endPacket760Loan68 false`,
  LT8's `canon760Loan` / `center760Loan`);
* `PrimitiveRowFacts` — the v3 primitive provider, row by row, from LT13's
  site lemmas (`StairPhysicalPrimitives.*_rows`) and kernel checks.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairPhysicalV3

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed Secp256k1 BalancedField Baselines
open StairRestSupport

/-! ## Host plan -/



/-! ## Boundary programs of the loan provider as built -/










/-! ## The primitive provider, row by row -/

















theorem sound_tickForward_row (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    Sound (StairPhysicalPrimitives.tickForward (StairPhysicalLayout.startFor B)) := by
  obtain ⟨s1, -, -, s4, -, s6⟩ := StairPhysicalPrimitives.budget_shape B hB
  refine ⟨?_, good_of_mem_list (StairPhysicalPrimitives.tickForward_rows B hB)
    (rowSitesL_indom B hB)⟩
  unfold StairPhysicalPrimitives.tickForward
  rw [s1]
  exact TickRanges.tick_physical _ _ (by omega)
    (StairPhysicalLayout.segmentMap_pool_nodup B hB)


theorem sound_middleForward_row (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    Sound (StairPhysicalPrimitives.middleForward (StairPhysicalLayout.startFor B + 1)
      (StairPhysicalLayout.endFor B - StairPhysicalLayout.startFor B - 1)) := by
  obtain ⟨-, s2, s3, s4, -, -⟩ := StairPhysicalPrimitives.budget_shape B hB
  refine ⟨?_, good_of_mem_list (StairPhysicalPrimitives.middleForward_rows B hB)
    (rowSitesL_indom B hB)⟩
  unfold StairPhysicalPrimitives.middleForward
  rw [s2]
  exact movedForward_physical _ (StairPhysicalPrimitives.midSegmentMap_pool_nodup B hB)
    _ _ (by omega)

/-- LT1's fixed reverse middle segment (`revSegmentMap`, the terminal row
extended to untick 505 on its real wire). -/
theorem sound_middleReverse_row (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    Sound (StairPhysicalPrimitivesFix505.middleReverseFix (StairPhysicalLayout.startFor B + 1)
      (StairPhysicalPrimitivesFix505.reverseEnd B - StairPhysicalLayout.startFor B - 1)) := by
  obtain ⟨s2, s3, s4, -⟩ := StairPhysicalPrimitivesFix505.budget_shape_rev B hB
  refine ⟨?_, good_of_mem_list (StairPhysicalPrimitivesFix505.middleReverseFix_rows B hB)
    (rowSitesL_indom B hB)⟩
  unfold StairPhysicalPrimitivesFix505.middleReverseFix
  rw [s2]
  exact movedReverse_physical _
    (StairPhysicalPrimitivesFix505.revSegmentMap_pool_nodup B hB) _ _ (by omega)



/-- LT1's relabelled terminal blocks (`StairTerminalV3`, clear included). -/
theorem sound_forwardTerminalV3 : Sound StairTerminalV3.forwardTerminalV3 :=
  ⟨StairTerminalV3.forwardTerminalV3_physical,
    good_of_list _ StairTerminalV3.forwardTerminalV3_wires forwardSites_indom⟩








end ECDSAAdd.Entrant.StairPhysicalV3

end
end Merge_StairPhysicalV3Instance_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairCallerParts_at_BOptimizations` -/
section Merge_StairCallerParts_at_BOptimizations

/-!
# Caller-domain support of the record pieces of the hosted kernels (LT11)

Every hosted kernel of the staircase (current CANON and the k = 44 re-plan)
is assembled from (i) the placed checkpoint primitives (LT13:
`StairPhysicalPrimitives.physicalPrimitives_caller`), (ii) hosted/loaned
groups and boundary components, and (iii) unchanged record pieces: tick
ranges of the record walk, the six-tick bridge, the terminal reverse bridge,
packet writes/reads at checkpoint ticks, the native first tick, the clears and
the scalar glue.  This module proves (iii).

Method.  The record kernels `InverseFiveEntry23.entryKernel15` and
`ParityXExitInverse23Kernel.kernelXN k` have support in
`OB5Support.logicalSites ⊆ callerDomain` (record theorems `entry_support530`,
`kernelXN_support`).  Their phases contain the record pieces as literal
append factors (after the tick-range split lemmas below).  Since
`phaseHost` is a permutation whose inverse preserves the caller domain, the
pieces' own labels are caller labels (`own_of_renamed`); every new wrapper
(`phaseHost`, `Prefix1590.borrow`, `fieldRename`, `OB5.sig i`) preserves the
caller domain (`StairCallerCheck`), so the pieces stay inside it wherever the
re-planned schedule places them.  Small field pieces are checked by
`decide +kernel` on `allCaller`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSemanticFinal

open ECDSAAdd Arithmetic Challenge
open MappedCompressed

/-! ## Generic support tools -/









/-! ## Tick-range split lemmas -/

theorem tickGap_forward_split (isA : Bool) (m : Nat) : ∀ i n : Nat,
    Rolling1588TickGap.forward isA i (m + n) =
      Rolling1588TickGap.forward isA i m ++ Rolling1588TickGap.forward isA (i + m) n := by
  induction m with
  | zero =>
    intro i n
    simp [Rolling1588TickGap.forward]
  | succ m ih =>
    intro i n
    rw [Nat.succ_add]
    simp only [Rolling1588TickGap.forward]
    rw [ih (i + 1) n, List.append_assoc, show i + 1 + m = i + (m + 1) by omega]


/-! ## The record phases are caller-supported in their own coordinates -/








/-! ## Record pieces of the first phase -/









/-! ## Record pieces of the reverse phases -/








/-! ## Packet reads/writes at the checkpoint ticks (direct check) -/



/-! ## Scalar glue of the hosted field -/


end ECDSAAdd.Entrant.StairSemanticFinal

end
end Merge_StairCallerParts_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairCallerV3Inputs_at_BOptimizations` -/
section Merge_StairCallerV3Inputs_at_BOptimizations

/-!
# Inputs of the k = 44 re-plan for the caller-support assembly (LT11)

Own-label caller support of the re-planned primitives and hosts, from LT13's
placement facts:
* `primitive_own` — every wire of every placed primitive of a re-planned row
  (`StairPhysicalPrimitives.PrimitiveWire`) is a caller label
  (from `physicalPrimitives_caller`, kernel labels, via `own_of_fieldPlace`);
* `hosts_caller` — LT13's group hosts `StairPhysicalLayout.hosts B`;
* the phase-context first-row pieces (`phaseBMove`, `phaseBReturn`, the
  `phaseRelabel` relabelled codec; LT13's `phasePackTail` / `phaseUnpackHead`)
  from `StairPhysicalPhase.phaseKernel_caller`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSemanticFinal

open ECDSAAdd Arithmetic Challenge
open MappedCompressed



/-! ## Re-planned primitives -/

theorem primitive_own (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) (q : Wire)
    (hq : StairPhysicalPrimitives.PrimitiveWire B q) : q ∈ callerDomain :=
  caller_of_fieldPlaceB q
    ((callerList_iff _).mp (StairPhysicalPrimitives.physicalPrimitives_caller B hB q hq))

set_option maxHeartbeats 4000000 in
theorem pack_own (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    wires (StairPhysicalPrimitives.pack B) ⊆ callerDomain := by
  intro q hq
  apply primitive_own B hB q
  unfold StairPhysicalPrimitives.PrimitiveWire
  left
  exact hq

theorem unpack_own (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    wires (StairPhysicalPrimitives.unpack B) ⊆ callerDomain := by
  intro q hq
  exact primitive_own B hB q (Or.inr (Or.inl hq))


theorem tickForward_own (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    wires (StairPhysicalPrimitives.tickForward (StairPhysicalLayout.startFor B)) ⊆ callerDomain := by
  intro q hq
  exact primitive_own B hB q (Or.inr (Or.inr (Or.inr (Or.inl hq))))

theorem tickReverse_own (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    wires (StairPhysicalPrimitives.tickReverse (StairPhysicalLayout.startFor B)) ⊆ callerDomain := by
  intro q hq
  exact primitive_own B hB q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq)))))

theorem middleForward_own (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    wires (StairPhysicalPrimitives.middleForward (StairPhysicalLayout.startFor B + 1)
      (StairPhysicalLayout.endFor B - StairPhysicalLayout.startFor B - 1)) ⊆ callerDomain := by
  intro q hq
  exact primitive_own B hB q (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hq))))))


/-! ## Re-planned hosts -/


/-! ## Phase-context first row -/









end ECDSAAdd.Entrant.StairSemanticFinal

end
end Merge_StairCallerV3Inputs_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField13V3CleanTicks_at_BOptimizations` -/
section Merge_StairField13V3CleanTicks_at_BOptimizations

/-!
# Field 13 on v3: the record forward ticks never touch the 44 roles (LT29)

`forward_keeps : Keeps w (Rolling1588TickGap.forward isA i n)` for every role
`w` (raw window `[736, 781)`): each tick stays inside its compact layout
(`TickRanges.tick_support`, `W.repairedTick_support`), whose `a` side ends
below `base 515` and whose `b` side starts at `base 770`; the placement
`OB5.sig i` fixes the roles; the packet encoders are label renamings of
three small programs (kernel checks `chk_keep_enc*`).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField13V3Clean

open ECDSAAdd Arithmetic Challenge MappedCompressed




theorem tick_keeps (i : Nat) (hi : i < 512) {w : Wire} (hw : InWin w) :
    Keeps w (TickRanges.tick base i) := by
  apply keeps_of_not_mem
  intro hm
  have h1 := TickRanges.tick_support base i hi base_pool_nodup hm
  have h2 := W.repairedTick_support base i hi base_pool_nodup h1
  exact layout_avoids i hi hw (List.mem_toFinset.mp h2)





/-- The record forward ticks keep every role. -/
theorem forward_keeps (isA : Bool) {w : Wire} (hw : w ∈ rolesL) :
    ∀ n i, i + n ≤ 512 → Keeps w (Rolling1588TickGap.forward isA i n) := by
  have win : InWin w := inWin_of_role hw
  intro n
  induction n with
  | zero => intro i _; exact keeps_nil w
  | succ n ih =>
    intro i h
    rw [Rolling1588TickGap.forward]
    refine keeps_append (keeps_rename _ (sig_pre_role i (by omega) w win)
      (keeps_append (tick_keeps i (by omega) win) (packFirst_keeps isA i (by omega) hw)))
      (ih (i + 1) (by omega))

end ECDSAAdd.Entrant.StairField13V3Clean

end
end Merge_StairField13V3CleanTicks_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField13V3CleanPhaseX_at_BOptimizations` -/
section Merge_StairField13V3CleanPhaseX_at_BOptimizations

/-!
# Field 13 on v3: the 44 roles after the multiplication first phase (LT29)

`phaseRolesX_clean k : CutClean (ExitPre k) (cut (exitPieces …) 1) (exclusiveRoles.map fieldMap)`.

In phase coordinates the roles are `base 1542, 1026, 1541` (record phase work
sites, zero after the record forward walk: `forward_host_bits_of_boundary`
with `Rolling1588.stackForward_boundary`, via `TickGap.stackForward_run_eq`)
and `base 723 .. 764`, which the multiplication first phase never writes
(`forward_keeps` + kernel checks of the native seed, the six-tick tail and
the clear).
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace ECDSAAdd.Entrant.StairField13V3Clean

open ECDSAAdd Arithmetic Challenge MappedCompressed Secp256k1 BalancedField
open StairField13V3



theorem exitStack_keeps {w : Wire} (hw : w ∈ rolesL) :
    Keeps w (Rolling1588TickGap.stackForward false) := by
  have k (P : Program) (h : ztAll 736 45 true rolesL P = true) : Keeps w P :=
    keeps_of_ztAll h (fun _ x => x) w hw
  unfold Rolling1588TickGap.stackForward Six505.stackForward6
  exact keeps_append (forward_keeps false hw 504 1 (by decide))
    (keeps_append (k _ chk_keep_merged6) (keeps_append (k _ chk_keep_packP) (k _ chk_keep_after)))

theorem exitPhase_keeps {w : Wire} (hw : w ∈ rolesL) :
    Keeps w (FrontierEntry1591Native.forward base ++
      (Rolling1588TickGap.stackForward false ++ skywalkArithmeticClear base)) :=
  keeps_append (keeps_of_ztAll chk_keep_native (fun _ x => x) w hw)
    (keeps_append (exitStack_keeps hw) (keeps_of_ztAll chk_keep_skyClear (fun _ x => x) w hw))

theorem exitPhase_targets_zero {k : Nat} {s : State} (F : StairConcreteAssembly.ExitFrame k s)
    (m : List Bool) :
    ∀ q ∈ phaseTargets, (run (FrontierEntry1591Native.forward base ++
      (Rolling1588TickGap.stackForward false ++ skywalkArithmeticClear base)) m s).basis q = false := by
  intro q hq
  have hq' := hq
  simp only [phaseTargets, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq'
  rcases hq' with e | hd
  · -- the record phase work sites
    have clearFree : ∀ l, l = 1026 ∨ l = 1541 ∨ l = 1542 →
        base l ∉ wires (skywalkArithmeticClear base) := by
      intro l hl used
      rw [skywalkArithmeticClear, skywalkTerminalClear_wires] at used
      simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at used
      rcases used with e' | e' | e' <;> (have := base_injective e'; omega)
    have hl : ∃ l, q = base l ∧ (l = 1026 ∨ l = 1541 ∨ l = 1542) := by
      rcases e with rfl | rfl | rfl
      · exact ⟨1542, rfl, by omega⟩
      · exact ⟨1026, rfl, by omega⟩
      · exact ⟨1541, rfl, by omega⟩
    obtain ⟨l, rfl, hl⟩ := hl
    have main := three_stage (FrontierEntry1591Native.forward base)
      (Rolling1588TickGap.stackForward false) (skywalkArithmeticClear base) s (base l)
      (fun u => W.CompactSkywalkStage base (SkywalkRails.encode false false (F.x : Int) (p : Int)) 1
        u.basis)
      (fun u => u.basis (base l) = false)
      (fun m1 => FrontierEntry1591Native.caller_first_stageW base F.sharedNodup F.x F.Y.val
        F.x_pos F.x_lt s m1 F.input)
      (by
        intro u m2 stage1
        have e1 := Rolling1588TickGap.stackForward_run_eq false F.x F.x_pos F.x_lt u m2 stage1
        have bits := Rolling1588Lifetime.forward_host_bits_of_boundary false F.x F.x_pos F.x_lt u m2
          stage1 (Rolling1588.stackForward_boundary false F.sharedNodup F.historyAbove F.x F.x_pos
            F.x_lt u m2 stage1)
        show (run (Rolling1588TickGap.stackForward false) m2 u).basis (base l) = false
        rw [e1]
        rcases hl with rfl | rfl | rfl
        · exact bits.1
        · exact bits.2.1
        · exact bits.2.2)
      (by
        intro u m3 hu
        rw [run_preserves_outside _ _ _ _ (clearFree l hl)]
        exact hu)
    exact main m
  · -- base 723 .. 764: never written, zero in the input
    have hr : q ∈ rolesL := List.mem_of_mem_drop hd
    refine zt_sound q _ true m s (exitPhase_keeps hr) (fun _ => ?_)
    have win := inWin_of_role hr
    obtain ⟨h1, h2⟩ := win
    have key : ∀ x : Nat, 736 ≤ x → x < 781 → x = x - 16 + 16 ∧ x - 16 < 2314 ∧
        ¬(770 ≤ x - 16 ∧ x - 16 < 1026) ∧ ¬(2056 ≤ x - 16 ∧ x - 16 < 2312) := by
      intro x a b
      omega
    have kq := key q h1 h2
    have hq16 : ∃ l, q = base l ∧ l < 2314 ∧ ¬(770 ≤ l ∧ l < 1026) ∧ ¬(2056 ≤ l ∧ l < 2312) :=
      ⟨q - 16, kq.1, kq.2.1, kq.2.2.1, kq.2.2.2⟩
    obtain ⟨l, rfl, a, b, c⟩ := hq16
    exact exit_zero F l a b c

theorem chk_flastTerminal : ztAll 736 45 true (rolesL)
    StairTerminalV3.forwardTerminalV3 = true :=
  ztAll_true_of_not_mem 736 45 rolesL _ rolesL_window (fun w hw hm =>
    (StairTerminalV3.forwardTerminalV3_support w hm).2.2.2.1
      (by rw [StairPhysicalInventory.exclusiveSites_eq]; rw [rolesL_eq44] at hw; exact hw))




end ECDSAAdd.Entrant.StairField13V3Clean

end
end Merge_StairField13V3CleanPhaseX_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairField13V3CleanHostsR_at_BOptimizations` -/
section Merge_StairField13V3CleanHostsR_at_BOptimizations

/-!
# Field 13 on v3: the host halves from the plans that are actually open (LT29)

* Division: `entryHostsClean_of_rest` — `EntryHostsClean` from the integrator's
  `StairEntryOpen.EntryRest` (its plan has LT21's concrete side conditions
  `Cv (rowBudget i)`, so `HostsSide` holds by `hostsSide_cv`).
* Multiplication: `exitHostsClean_of_planR` — `ExitHostsClean k` from LT43's plans with
  reachability `∀ x, ExitPlanR checkpointPrimitives k x`.  The chain is LT43's
  `chain_of_planR` with the loaned groups, cut after each prefix; the reverse-segment
  steps of the plan are moved to the loaned reference prefixes by
  `StairLoanExitReachX.reachX_*`.

No concrete program is evaluated.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 400000

namespace ECDSAAdd.Entrant.StairField13V3Clean

open ECDSAAdd Arithmetic Challenge MappedCompressed
open StairField13V3
open StairField2V3Couple StairField2V3Entry StairField2V3ExitPlan StairLoanField7Transport
open StairField2V3Delta StairField2V3ExitPlanR StairLoanExitReachX

/-! ## Division -/



/-! ## Multiplication: hosts from the pinned side condition -/



/-- A coupled prefix for every pinned input gives a cut fact. -/
theorem cutClean_of_xchR (k B : Nat) {P Y : Program} {S : List Wire}
    (h : ∀ x, ∃ Q, CRel (fun s t => ExitMiddleX k x s ∧ s = t) (RelX x B) P Q)
    (hY : Y = StairField2V3Replay.exitReferenceOpening ++ P)
    (hS : ∀ x a b, CvX x B a b → ∀ q ∈ S, a q = false) :
    CutClean (StairConcreteAssembly.ExitPre k) Y S := by
  intro s hs m q hq
  subst hY
  rw [run_append]
  obtain ⟨x, hx⟩ := exitMiddle_x k
    (run StairField2V3Replay.exitReferenceOpening
      (m.take (measurementCount StairField2V3Replay.exitReferenceOpening)) s)
    ⟨s, hs, m.take (measurementCount StairField2V3Replay.exitReferenceOpening), rfl⟩
  obtain ⟨Q, h⟩ := h x
  obtain ⟨old, hb⟩ := h
    (run StairField2V3Replay.exitReferenceOpening
      (m.take (measurementCount StairField2V3Replay.exitReferenceOpening)) s)
    (run StairField2V3Replay.exitReferenceOpening
      (m.take (measurementCount StairField2V3Replay.exitReferenceOpening)) s)
    ⟨hx, rfl⟩
    (m.drop (measurementCount StairField2V3Replay.exitReferenceOpening))
  have hc : CvX x B _ _ := hb.2
  exact hS x _ _ hc q hq

/-! ## Multiplication: the coupled chain with loaned groups, cut after each prefix -/

/-- Pinned pre-relation. -/
abbrev XPreX (k x : Nat) : State → State → Prop := fun s t => ExitMiddleX k x s ∧ s = t

/-- Relation at a row: pinned side condition and reachability through a loaned prefix. -/
abbrev RowRelL (k x B : Nat) (Z : Program) : State → State → Prop :=
  fun s t => RelX x B s t ∧ ReachBy (ExitMiddleX k x) Z t

theorem sharedL (k x B : Nat) (P Z : Program) (away : ∀ q ∈ Δv B, q ∉ wires P) :
    CRel (RowRelL k x B Z) (RowRelL k x B (Z ++ P)) P P :=
  crel_track (shared_step (Δv B) (CvX x B) (cvX_local x B) P away) (ExitMiddleX k x) Z

theorem segL (k x : Nat) {B B' : Nat} {P Z Y : Program}
    (tr : ∀ t, ReachBy (ExitMiddleX k x) Z t → ReachE k x Y t)
    (h : CRel (RowRelE k x B Y) (RelX x B') P []) :
    CRel (RowRelL k x B Z) (RowRelL k x B' Z) P [] :=
  crel_sel_reach (ExitMiddleX k x) Z
    (crel_mono (fun _ t hst => ⟨hst.1, tr t hst.2⟩) (fun _ _ w => w) h)








theorem drop_reach {k x B : Nat} {Z P : Program}
    (h : ∃ Q, CRel (XPreX k x) (RowRelL k x B Z) P Q) :
    ∃ Q, CRel (fun s t => ExitMiddleX k x s ∧ s = t) (RelX x B) P Q := by
  obtain ⟨Q, h⟩ := h
  exact ⟨Q, crel_mono (fun _ _ w => w) (fun _ _ w => w.1) h⟩


/-! ## Deliverables in the final shapes -/



end ECDSAAdd.Entrant.StairField13V3Clean

end
end Merge_StairField13V3CleanHostsR_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairCallerV3Kernel_at_BOptimizations` -/
section Merge_StairCallerV3Kernel_at_BOptimizations

/-!
# Field 8 support premises on the frozen CANON v3 program (LT11)

For the v3 program of `../CANON/Entrant_1719`
(`StairConcreteAssembly.checkpointPrimitives = StairV3Primitives.primitives`
with LT1's terminal blocks `StairTerminalV3` and fixed reverse middle segments
`StairPhysicalPrimitivesFix505.middleReverseFix`, `StairConcreteAssembly.hostPlan
= StairV3Primitives.hostPlan`, division endpoint `bestLoans.divEndpoint`),
assembled leaf by leaf from the component lemmas of `StairCallerParts`,
`StairCallerHosted`, `StairCallerSchedule`, `StairCallerV3Inputs`,
`StairCallerV3Checks` and `StairCallerEndpointCheck`:

* `entrySupportV3 : EntrySupportD`;
* `exitSupportV3 : ExitSupportD`;
* `semantic_composition_v3` — field 8 (`StairOpen.semantic_composition`) for
  the concrete assembly from field 13 (`HostReplaySpec`) alone.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSemanticFinal

open ECDSAAdd Arithmetic Challenge
open MappedCompressed

/-! ## Host plan and roles -/








/-! ## The v3 primitive provider -/












/-- The fixed reverse middle segment of a row (LT1's `PrimitiveWireFix`). -/
theorem middleReverseFix_own (B : Nat) (hB : B ∈ StairPhysicalLayout.budgets) :
    wires (StairPhysicalPrimitivesFix505.middleReverseFix (StairPhysicalLayout.startFor B + 1)
      (StairPhysicalPrimitivesFix505.reverseEnd B - StairPhysicalLayout.startFor B - 1)) ⊆
      callerDomain := by
  intro q hq
  exact caller_of_fieldPlaceB q ((callerList_iff _).mp
    (StairPhysicalPrimitivesFix505.physicalPrimitivesFix_caller B hB q
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hq))))))))



/-! ## Segments of the v3 table -/





/-! ## Division kernel -/








/-! ## Multiplication kernel -/









end ECDSAAdd.Entrant.StairSemanticFinal

end
end Merge_StairCallerV3Kernel_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSiteEasyFrameX_at_BOptimizations` -/
section Merge_StairSiteEasyFrameX_at_BOptimizations

/-!
# Field 12: the X entry `entryXNew` (LT35)

The record's support lemma for the merged X entry (`E1QubitPlacement.merged_S`,
label list `mSites`) also covers the comparison prefix, whose carry block
`256 .. 511` contains the one label (`base 511`) that the placement sends to a
hole (pool 725).  `entryXNew` drops that prefix (the flag is read from `pk`),
so its wires lie in the smaller list `tSites` (the blocks used by the tail
`tailX`: `0 .. 257`, `770 .. 1284`, `1540 .. 1797` and `514, 721, 722, g`).
`tailX_tight` is the record's own support proof (`merged_support`) restricted to
the tail; the placed list is checked once against `Good39`.  The entry uses pool
720..724 (not among the 39 holes).  No program is evaluated.
-/

section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSiteEasy

open ECDSAAdd Arithmetic Challenge RecordedQuantum NativeFirstDirect
open MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairSiteAvoidance
open E1Merge E1WholeKAdd52Research











theorem e1_eq (q : Wire) : E1QubitPlacement.sig (E1QubitPlacement.rho q) = e1B q := by
  unfold E1QubitPlacement.sig E1QubitPlacement.phaseHost E1QubitPlacement.nativeSwap
    E1QubitPlacement.rho e1B
  simp only [Equiv.trans_apply, StairPlaceFast.swap_eq_sw, StairPlaceFast.swB_eq]
  rfl



/-! K4-B (replay budget): `xList_good` by affine intervals.  On each interval of the x-tail labels
every literal exchange of `e1B` / `kernelPlaceB` is the identity and `pwB` is one interval shift,
so goodness is proved symbolically; only a dozen exceptional labels are evaluated. -/





















end ECDSAAdd.Entrant.StairSiteEasy

end
end Merge_StairSiteEasyFrameX_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSiteEasyPhase_at_BOptimizations` -/
section Merge_StairSiteEasyPhase_at_BOptimizations

/-!
# Field 12 on CANON 1945: phase pieces (LT35)

Pieces under the phase placement `PP = kernelPlace ∘ phaseHost`:

* the record walks `Rolling1588TickGap.forward true 1 424` (entry ticks) and
  `Rolling1588.reverse true 1 424` (exit ticks): the record support chain
  `forward_support` → `forward_support_eq` → `NewStackOB5.forward_support_eq` →
  `StackOB5.support_gen` puts every label in `integerSites`
  (`base l`, `l < 515 ∨ 770 ≤ l < 1285 ∨ 1540 ≤ l < 1797`), all `PPI`;
* `InverseFive23.lastPhase15 false` (entry last) and
  `Rolling1588TickGap.tailPhase false` (exit tail): their long walks the same
  way, the native inverse by `FrontierEntry1591Native.support`, the short
  blocks by an `allSites` interval check;
* the v3 first row `firstPack` / `firstUnpack`: `allSites` interval check.

No concrete walk is evaluated; the decided programs are a few thousand gates.
-/

section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ECDSAAdd.Entrant.StairSiteEasy

open ECDSAAdd Arithmetic Challenge
open MappedCompressed Secp256k1 BalancedField
open StairConcreteAssembly StairSiteAvoidance

/-! K4-B (replay budget): `PPI` as one Boolean test with the kernel-primitive `Nat.blt` /
`Nat.ble` / `Nat.beq` only (the `Decidable (PPI x)` instance costs several ms per wire), and the
phase relabelling on its closed forms. -/






theorem tickGap_forward_ppi (isA : Bool) (n : Nat) (hn : n ≤ 511) :
    ∀ x ∈ wires (Rolling1588TickGap.forward isA 1 n), PPI x := by
  intro x hx
  have h1 := Rolling1588TickGap.forward_support isA 1 n (by omega) hx
  rw [Rolling1588.forward_support_eq, NewStackOB5.forward_support_eq] at h1
  exact ppi_of_int ((StackOB5.support_gen 1 n (by omega) (by omega)).1 x h1)


section
/- K4C (build budget): without these the elaborator unfolds the native inverse programs (and
their `wires`) while instantiating `wires_sub` / `support` (≈ 24 s + ≈ 4 s linting). -/
attribute [local irreducible] wires run FrontierEntry1591NativeH.inverse FrontierEntry1591Native.inverse


end

/-! K4-B (replay budget): the two large record blocks `Six505.cand6` / `candidate15` are not
evaluated: their exact supports (`StairTerminalV3.cand6_support` / `candidate15_support`, 30 and 35
labels) are checked once. -/

theorem kbMerged6_ppi : PieceOK StairCertificate.holes39 PP Six505.merged6 := by
  have hc : StairTerminalV3.cand6Sites.all (fun y => kbPpiB (OB5.sig 510 y)) = true := by
    decide +kernel
  apply ok39_of_ppi
  intro x hx
  unfold Six505.merged6 at hx
  rw [renameProgram_support] at hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact kbPpiB_ppi (List.all_eq_true.mp hc y
    (List.mem_toFinset.mp (StairTerminalV3.cand6_support hy)))


/-! ## The six phase pieces -/

theorem entryTicks39 :
    PieceOK StairCertificate.holes39 PP (Rolling1588TickGap.forward true 1 424) :=
  ok39_of_ppi (tickGap_forward_ppi true 424 (by omega))


theorem exitTail39 :
    PieceOK StairCertificate.holes39 PP (Rolling1588TickGap.tailPhase false) := by
  unfold Rolling1588TickGap.tailPhase Rolling1588TickGap.stackForward Six505.stackForward6
  refine PieceOK.append (PieceOK.append ?_ (PieceOK.append ?_ ?_)) ?_
  · exact ok39_of_ppi (tickGap_forward_ppi false 504 (by omega))
  · exact kbMerged6_ppi
  · exact kbOk39_of_ppiAllB (by decide +kernel)
  · exact kbOk39_of_ppiAllB (by decide +kernel)


/-! ### The v3 first row (LT46, replay budget)

`pack 87` / `unpack 87` are not evaluated: their wires lie in `rowSitesL 87`
(`StairPhysicalPrimitives.pack_rows` / `unpack_rows`), and the row sites are checked once
under `phaseRelabel`.  The three small components (x-word orientation, record packet 84,
b-rail move) are checked per instruction.  The proof is one lemma per component, combined
by `PieceOK.append`. -/













end ECDSAAdd.Entrant.StairSiteEasy

end
end Merge_StairSiteEasyPhase_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSlotsV3_at_BOptimizations` -/
section Merge_StairSlotsV3_at_BOptimizations

/-!
# Field 11 (`slot_composition`) on the frozen CANON v3.1 (`Entrant_1719`)

Instance of the plan-parametric ledger for the k = 44 re-plan:
`v3WalkFacts` (LT13 primitives + LT14 orientation + LT13 phase first row),
`v3GroupFacts` (any host plan: hosting is a rebinding), `v3BoundaryFacts`
(loaned division endpoint `endPacket760DivLoan` with a loose `+10,000`, LT8's
`canon760Loan` / `center760Loan` at `+440` each, the multiplication endpoint
`endPacket760Loan68` at `+680`).

Total overhead: at most `303,856 + 11,560 = 313,882` slots over the record
program, i.e. `gateSlots (concreteAssembly.program C) ≤ 50,829,625`, well inside
the certificate's `50,515,743 + bestSlotDelta = 51,155,937`.
-/

section

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Entrant.StairSlotsPlan

open ECDSAAdd Arithmetic RecordedQuantum Challenge
open MappedCompressed DirectSkywalk Secp256k1 BalancedField Baselines
open StairPhysicalLayout StairPhysicalPhase

attribute [local irreducible] gateSlots

/-! ## Walk facts of the CANON v3 primitive provider -/




theorem tickForward_slots (i : Nat) (h0 : 425 ≤ i) (h1 : i ≤ 500)
    (hB : 512 - i ∈ budgets) :
    gateSlots (StairPhysicalPrimitives.tickForward i) =
      gateSlots (TickRanges.tick base i) :=
  StairSlotsLib.tick_slots_map _ base i (by omega) (by omega)
    (segmentMap_pool_nodup _ hB) base_pool_nodup


theorem middleForward_slots (i n : Nat) (h0 : 385 ≤ i) (h1 : i + n ≤ 510)
    (hB : StairPhysicalPrimitives.segmentOf i ∈ budgets) :
    gateSlots (StairPhysicalPrimitives.middleForward i n) =
      gateSlots (Rolling1588TickGap.forward true i n) :=
  StairSlotsLib.movedForward_slots_eq _
    (StairPhysicalPrimitives.midSegmentMap_pool_nodup _ hB) i n h0 h1

theorem middleReverse_slots (i n : Nat) (h0 : 385 ≤ i) (h1 : i + n ≤ 510)
    (hB : StairPhysicalPrimitives.segmentOf i ∈ budgets) :
    gateSlots (StairPhysicalPrimitivesFix505.middleReverseFix i n) =
      gateSlots (Rolling1588.reverse true i n) :=
  StairSlotsLib.movedReverse_slots_eq _
    (StairPhysicalPrimitivesFix505.revSegmentMap_pool_nodup _ hB) i n h0 h1


/-! ## Groups: hosting is a rebinding of the placed loaned groups -/




/-! ## Boundary programs -/










/-! ## Field 11 on CANON v3 -/





end ECDSAAdd.Entrant.StairSlotsPlan

end
end Merge_StairSlotsV3_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareSitesK_at_BOptimizations` -/
section Merge_StairSquareSitesK_at_BOptimizations

/-! # LT40 U6: kernel-checked site tables for the arena half of field 12 (no proofs to edit here) -/

section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace ECDSAAdd.Entrant.StairSquareSites

open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout Challenge Baselines
  StairSquareContract StairSquareAssembly

/-! ## LT48 (replay budget): closed forms of the placement maps.
`Baselines.layout.core.poolWire i` is `List.getD` on `List.range' 4115 5699`, which the kernel walks on every
call; every map below is rewritten once (by proof) into Nat arithmetic, and the arena list test into the
interval test `StairPhysicalLayout.arenaB`, so the per-wire kernel checks are arithmetic. -/
namespace LT48K













theorem foldPerm_eq (x : Wire) : LowZero18Square.foldPerm K0 E0 x = swF 4834 5093 x := by
  have h : (SquareCarryLoan719.targets K0).zip (SquareCarryLoan719.foldHosts E0) = [(4834, 5093)] := by
    decide +kernel
  simp only [LowZero18Square.foldPerm, SquareCarryLoan719.foldPerm, h, SquareCarryLoan719.swaps,
    Equiv.trans_apply, Equiv.refl_apply, swap_eq]

theorem sqSwap_eq (x : Wire) : R2SqEp760.sqSwap K0 E0 x = swF 4875 5478 x := by
  have h1 : R2SqEp760.sqRet K0 = 4875 := by decide +kernel
  have h2 : R2SqEp760.sqHost E0 = 5478 := by decide +kernel
  simp only [R2SqEp760.sqSwap, h1, h2, swap_eq]


end LT48K






/-! ## K4-D (replay budget): closed-form bit masks and interval checks

The per-wire site tests are replaced by bits of closed-form masks (`K4D.YM`, `K4D.ZM`), tied to the original
predicates by symbolic soundness lemmas; the kernel then checks each wire range with one comparison
`(m >>> a) % 2 ^ n = 2 ^ n - 1` instead of evaluating the placement maps wire by wire. -/
namespace K4D



















/-! ### `bridge_all` -/







end K4D





/-! ### K4-D: `bodyGood_all` -/
namespace K4D
















end K4D





end ECDSAAdd.Entrant.StairSquareSites

end
end Merge_StairSquareSitesK_at_BOptimizations

/-! ### merged from `ECDSAAdd.Submission.Entrant.StairSquareSites_at_BOptimizations` -/
section Merge_StairSquareSites_at_BOptimizations

/-! # LT40 U6: arena half of field 12 for the new square

The record's site chain for the placed square is generic in the A and C bodies (given the record's
`coarse`/`fine` support shapes).  We re-run it for arbitrary bodies, add the bridge "record site and not an
old pool index ⇒ inside the arena and not an old omission after `UG`", and conclude the arena half of
`PieceOK` for the placed new core from a support inclusion into the record-shaped core plus explicit hosts. -/

section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace ECDSAAdd.Entrant.StairSquareSites

open ECDSAAdd Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlledPointLayout Challenge Baselines
  StairSquareContract StairSquareAssembly

attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

/-! ## Hole freedom of the placed new core -/




section Chain

variable (A C : Program)
  (ac : wires A ⊆ insert (layout.core.poolWire 1540)
    (layout.core.generic :: layout.dialogStreamedSquareWide.wires).toFinset)
  (af : wires A ⊆ insert (layout.core.poolWire 1540) (wires (InverseCarryDevelop.hostedADual
    layout.dialogStreamedSquareWide (LowZero18Square.foldPerm layout.dialogStreamedSquareWide
      (OwnDiagAll12Square.kext layout)) layout.core.generic)))
  (cf : wires C ⊆ insert C163Low4Middle.d
    (wires (OwnDiagAll12Square.bodyCKTq C163Low4Middle.L C163Low4Middle.g)))
include ac af cf

omit ac af in
theorem c163_fine : wires (C163Low4Square.program layout A C) ⊆
    insert C163Low4Middle.d (wires (A161Square.program layout A)) := by
  -- K4-D (replay budget): through the closed forms of `StairSquareSitesK` (no pool walks)
  have fb : R2SqEp760.sqSwap C163Low4Middle.L (OwnDiagAll12Square.kext layout) C163Low4Middle.d =
      C163Low4Middle.d := by
    refine (LT48K.sqSwap_eq C163Low4Middle.d).trans ?_
    show LT48K.swF 4875 5478 (Baselines.layout.core.poolWire 1540) = Baselines.layout.core.poolWire 1540
    rw [LT48K.pw_eq]
    decide
  have ff : LowZero18Square.foldPerm C163Low4Middle.L (OwnDiagAll12Square.kext layout) C163Low4Middle.d =
      C163Low4Middle.d := by
    refine (LT48K.foldPerm_eq C163Low4Middle.d).trans ?_
    show LT48K.swF 4834 5093 (Baselines.layout.core.poolWire 1540) = Baselines.layout.core.poolWire 1540
    rw [LT48K.pw_eq]
    decide
  exact C163Low4ProgramSupport.place_insert layout layout_widths layout_nodup _ _
    (C163Low4ProgramSupport.core_fine C163Low4Middle.L (OwnDiagAll12Square.kext layout) C163Low4Middle.g
      C163Low4Middle.d A C cf fb ff)

theorem c163_sites : wires (C163Low4Square.program layout A C) ⊆ (OB5Support.sites layout).toFinset := by
  have ds : C163Low4Middle.d ∈ (OB5Support.sites layout).toFinset := by
    have pm := OB5Support.pool_mem layout 1540 (Or.inr (Or.inr (Or.inl (by constructor <;> omega))))
    exact List.mem_toFinset.mpr (by unfold OB5Support.sites; exact List.mem_append_right _ pm)
  intro q hq
  exact (Finset.mem_insert.mp (c163_fine A C cf hq)).elim (fun eq => eq ▸ ds)
    (fun used => A161ProgramSupport.program_support layout layout_widths layout_nodup A ac af used)

theorem c163_free (i : Nat) (hi : i ∈ [1800,766,765,767,770,1285,1286,769,768,718,719]) :
    layout.core.poolWire i ∉ wires (C163Low4Square.program layout A C) := by
  have old := A161ProgramSupport.program_free_old layout layout_widths layout_nodup i hi A ac af
  have ne : layout.core.poolWire i ≠ C163Low4Middle.d := by
    -- K4-D (replay budget): `poolWire` by its closed form (no pool walks)
    show Baselines.layout.core.poolWire i ≠ Baselines.layout.core.poolWire 1540
    rw [LT48K.pw_eq, LT48K.pw_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact fun used => (Finset.mem_insert.mp (c163_fine A C cf used)).elim ne old

theorem c163_retired : layout.core.poolWire 760 ∉ wires (C163Low4Square.program layout A C) := by
  have ne : layout.core.poolWire 760 ≠ C163Low4Middle.d := by
    show Baselines.layout.core.poolWire 760 ≠ Baselines.layout.core.poolWire 1540
    rw [LT48K.pw_eq, LT48K.pw_eq]
    decide
  have old := A161ProgramSupport.square_free layout layout_widths layout_nodup A ac af
  exact fun used => (Finset.mem_insert.mp (c163_fine A C cf used)).elim ne old






end Chain

/-! ## Bridge: record generic-level sites are good physical sites after `UG` -/



/-! ## Arena half for the placed new core -/






/-! ## B branch with a non-record body: absolute check of the body image -/

/-- The B wrapper's wires: record-wrapper wires plus the renamed body. -/
theorem recBrB_split (X Y : Program) :
    wires (recBrB X) ⊆ wires (recBrB Y) ∪
      ((wires X).image (R2SqEp760.sqSwap K0 E0)).image (LowZero18Square.foldPerm K0 E0) := by
  intro q hq
  simp only [recBrB, ParkCopy.withLowK2P, ParkCopy.pB, R2SqEp760.bodySwap, wires_append,
    renameProgram_support, Finset.mem_union] at hq ⊢
  tauto




end ECDSAAdd.Entrant.StairSquareSites

end
end Merge_StairSquareSites_at_BOptimizations
