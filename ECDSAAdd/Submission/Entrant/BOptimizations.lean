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
import ECDSAAdd.Submission.Entrant.ACCache

-- Rebalanced closed source chunks; all ordinary declarations and circuit literals retained.
section

-- Verified ABC18 optimization component C105CacheFrames
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop MixedLiteralAdderDevelop
set_option autoImplicit false
set_option Elab.async false
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
#print axioms sub_frame
#print axioms forward_frame
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105ForwardErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms forward_erased
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105ForwardClean
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms forward_zero
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CHeadArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CHeadArithmeticResearch
open InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
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
#print axioms ready
end ECDSAAdd.Entrant.CHeadArithmeticResearch

end

-- Verified ABC18 optimization component C105ForwardValues
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms forward_values
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CPreInverseArithmetic
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CPreInverseArithmeticResearch
open InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
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
#print axioms ready
end ECDSAAdd.Entrant.CPreInverseArithmeticResearch

end

-- Verified ABC18 optimization component C105InverseReady
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option Elab.async false
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
#print axioms inverse_ready
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105MiddleErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms middle_erased
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Restore
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms restored
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105UnbuildSplit
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem erased_suffix(H:Nat)(u:State)(m:List Bool)(ready:WReady acc pad bank cin src H u):
 run (I++C105LowEraseResearch.clear++tail) m (C105LowEraseResearch.erase u)=run (I++tail) m u:=by
 exact ClearContextResearch.suffix I C105LowEraseResearch.clear tail C105LowEraseResearch.counts.2.1
  (C105LowEraseResearch.erase u) u m (restored H u m ready)

#print axioms erased_suffix
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105PlainLoop
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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

#print axioms plain_loop
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105CacheLoop
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option Elab.async false
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
#print axioms cache_loop
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Core
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option Elab.async false
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
#print axioms core_plain
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component CKKnownMiddle
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.CKKnownMiddleResearch
open ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
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
#print axioms equivalent
#print axioms middle_eq
end ECDSAAdd.Entrant.CKKnownMiddleResearch

end

-- Verified ABC18 optimization component C105Frame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.C105Research
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
 InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option Elab.async false
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


#print axioms core_frame
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
set_option Elab.async false
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

#print axioms loop_eq
#print axioms body_frame
end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Counts
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105SignResearch
open C105PrefixResearch C105Research Challenge
set_option autoImplicit false
set_option Elab.async false
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
 simp only [xs,ys,cs,HighConsumedC105Research.xs,HighConsumedC105Research.ys,
  HighConsumedC105Research.cs,HighConsumedC105Research.cin,HighConsumedC105Research.hs,
  C105PrefixResearch.cin,CKAliasesResearch.original,Ghost3CacheC.middle,
  GhostRelocatedKnown.C.original,HighSignCResearch.hosts,C105SignResearch.hosts,aa,ap,ab,ax,ai] at *
 exact ⟨by omega,by omega⟩

 theorem body_counts:toffoliCount body+3=toffoliCount HighSignCResearch.body ∧
 measurementCount body=measurementCount HighSignCResearch.body:=by
 have h:=loop_counts
 simp only [body,rawBody,HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,
  toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩
#print axioms loop_counts
#print axioms body_counts
end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Slots
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105SignResearch
open C105PrefixResearch C105Research Challenge
set_option autoImplicit false
set_option Elab.async false
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
 simp only [xs,ys,cs,HighConsumedC105Research.xs,HighConsumedC105Research.ys,
  HighConsumedC105Research.cs,HighConsumedC105Research.cin,HighConsumedC105Research.hs,
  C105PrefixResearch.cin,CKAliasesResearch.original,Ghost3CacheC.middle,
  GhostRelocatedKnown.C.program,GhostRelocatedKnown.C.original,HighSignCResearch.hosts,C105SignResearch.hosts,aa,ap,ab,ax,ai] at *
 omega
 theorem body_slots:gateSlots body+12=gateSlots HighSignCResearch.body:=by
 have h:=loop_slots
 simp only [body,rawBody,HighSignCResearch.body,HighSignCResearch.rawBody,C163Low4Body.bodyProgram,gateSlots_append]
 omega
#print axioms loop_slots
#print axioms body_slots
end ECDSAAdd.Entrant.C105SignResearch

end

-- Verified ABC18 optimization component C105Scope
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms checked
#print axioms middle_support
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Physical
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms body_physical
end ECDSAAdd.Entrant.C105Research

end

-- Verified ABC18 optimization component C105Support
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.C105Research
open C105PrefixResearch ControlLoan1589BFFold
set_option autoImplicit false
set_option Elab.async false
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

#print axioms body_support
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
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false

def newBuild:Program:=ReorderedABuild.build 89 acc pad bank cin src hosts
def newInv:Program:=ReorderedAUnbuild.unbuild 89 acc pad bank cin src hosts

theorem counts:
 toffoliCount newBuild+toffoliCount newInv+2=
  toffoliCount SixCarryLoopAnchor.build+toffoliCount LocalEightLoop.unbuild ∧
 measurementCount newBuild+measurementCount newInv+4=
  measurementCount SixCarryLoopAnchor.build+measurementCount LocalEightLoop.unbuild ∧
 Challenge.gateSlots newBuild+Challenge.gateSlots newInv+178=
  Challenge.gateSlots SixCarryLoopAnchor.build+Challenge.gateSlots LocalEightLoop.unbuild:=by decide +kernel
#print axioms counts
end ECDSAAdd.Entrant.BArithmeticCountsResearch

end

-- Verified B optimization component BBodyBalance
section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.BBodyBalanceResearch
open ReorderedBPrefixResearch ControlLoan1589BFFold
set_option autoImplicit false
set_option Elab.async false
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
#print axioms toffoli
#print axioms measurements

end ECDSAAdd.Entrant.BBodyBalanceResearch

end

-- Verified B optimization component BPatchedPaddedFrame
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BPatchedPaddedResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ReorderedBPrefixResearch
set_option autoImplicit false
set_option Elab.async false
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
set_option Elab.async false
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

#print axioms toffoli
#print axioms measurements

end ECDSAAdd.Entrant.BPatchedPaddedResearch

end

-- Verified B optimization component BPatchedPaddedSupport
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.BPatchedPaddedResearch
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ReorderedBPrefixResearch
set_option autoImplicit false
set_option Elab.async false
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
set_option Elab.async false
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
set_option Elab.async false
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

theorem selected_sublist : selected.Sublist LocalEightBody99.body := by decide +kernel

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
set_option Elab.async false
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
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] BPatchedPaddedResearch.body ZeroSetDevelop.compileS? ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots


























def selectedBody (K : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
 match FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse _ => FullB99OptTemp.selectedBody K g
 | isTrue _ => if g=LowAccCarryDevelop.c then BPatchedPaddedResearch.body else FullB99OptTemp.selectedBody K g



















































































































































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
set_option Elab.async false
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
set_option Elab.async false
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
set_option Elab.async false
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
set_option Elab.async false
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
set_option Elab.async false
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
set_option Elab.async false
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
set_option Elab.async false
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
 intro q hq
 simp only [UniformAdderSpliceResearch.cs,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>apply HighConsumedStreamResearch.untouched <;>decide +kernel

theorem post_fresh:∀q∈UniformAdderSpliceResearch.ys ports,q∉wires post:=by
 intro q hq
 simp only [UniformAdderSpliceResearch.ys,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl|rfl <;>apply HighConsumedStreamResearch.untouched <;>decide +kernel

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
#print axioms toffoli
#print axioms pre_fresh
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
#print axioms high_word
#print axioms inner_run_eq
#print axioms sub_run_eq
end ECDSAAdd.Entrant.HighConsumedB95Research


end

-- Verified B95 optimization component HighB95Resources
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
set_option autoImplicit false
set_option Elab.async false
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
set_option Elab.async false
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
set_option Elab.async false
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
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem run_erased(s:State)(m:List Bool)
 (q0:s.basis 4757=false)(q1:s.basis 4758=false)(q2:s.basis 4759=false)
 (ci:s.basis 4760=false)(fl:s.basis 4762=false):
 run program m s=erase 4758 (run ReorderedBMiddlePatchesResearch.output m s):=by
 let t:=run a (m.take (measurementCount a)) s
 rcases BShortGhostFactsResearch.checked with ⟨ciA,_,_,flA,_,q2A,_,_,_,_,_,_,_,fbm,_,_,_⟩
 have tc:t.basis 4760=false:=(PairedWritesResearch.preserved 4760 a ciA s _).trans ci
 have tq1:t.basis 4758=false:=(PairedWritesResearch.preserved 4758 a B95FactsResearch.checked.2.2.2.1 s _).trans q1
 have tq2:t.basis 4759=false:=(PairedWritesResearch.preserved 4759 a q2A s _).trans q2
 have tf:t.basis 4762=false:=(PairedWritesResearch.preserved 4762 a flA s _).trans fl
 have eq:∀r,run fastWindow r t=run (exchange 4758 4762) [] (run b0 r t):=
  fun r=>window_eq t r tc tq2 tq1 tf
 have off:4762∉wires b0:=fresh_fixed (Equiv.swap 4757 4760) (Equiv.swap 4757 4760).injective b 4762
  (by decide) (not_wire b 4762 fbm)
 have hz:∀r,(run b0 r t).basis 4762=false:=fun r=>(run_preserves_outside b0 r t 4762 off).trans tf
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


#print axioms equivalent
end ECDSAAdd.Entrant.B95MiddleResearch

end

-- Verified B95 optimization component B95Ready
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95MiddleResearch
open ReorderedBPrefixResearch InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
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
#print axioms ready_eq
end ECDSAAdd.Entrant.B95MiddleResearch

end

-- Verified B95 optimization component B95Aliases (semantic)
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95AliasesResearch
open ReorderedBPrefixResearch InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms equivalent
end ECDSAAdd.Entrant.B95AliasesResearch

end

-- Verified B95 optimization component B95LowErase
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95LowEraseResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms restore
#print axioms clear_eq_erase
end ECDSAAdd.Entrant.B95LowEraseResearch

end

-- Verified B95 optimization component B95LowErasedComposition
section
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Arithmetic
namespace ECDSAAdd.Entrant.B95LowEraseResearch
open InverseCarryDevelop ReorderedBPrefixResearch ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
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
#print axioms forward_erased
#print axioms aliases_erased
end ECDSAAdd.Entrant.B95LowEraseResearch

end


end
