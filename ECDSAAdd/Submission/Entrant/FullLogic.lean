import ECDSAAdd.Arithmetic.PhysicalGateCheck
import ECDSAAdd.Submission.Entrant.ParkAMany

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.WholePadDevelop
open InverseCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

theorem state_eq_of_frame (acc:List Wire) (base:BasisState) (V:Nat) (s t:State)
 (hp:s.phase=t.phase) (hs:SquareFrame acc base V s.basis) (ht:SquareFrame acc base V t.basis):s=t := by
 apply State.extensionality _ _ hp
 funext w
 by_cases hw:w∈acc
 · exact (regValue_eq_iff acc _ _).mp (hs.1.trans ht.1.symm) w hw
 · exact (hs.2 w hw).trans (ht.2 w hw).symm

theorem build_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (hf':∀f∈earlyHTerms src,Acc.Fits acc Z' bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hz':∀w∈Z',s.basis w=false)
 (hb:∀w∈bank,s.basis w=false) (hi:s.basis cin=false) (zero:regValue acc s.basis=0):
 run (NarrowAcc.build8 acc Z bank cin src) m s=run (NarrowAcc.build8 acc Z' bank cin src) m s := by
 have a:=NarrowAcc.build8_triple acc Z bank cin src ha (by omega) hf s.basis hz hb hi s m ⟨zero,fun _ _=>rfl⟩
 have b:=NarrowAcc.build8_triple acc Z' bank cin src ha (by omega) hf' s.basis hz' hb hi s m ⟨zero,fun _ _=>rfl⟩
 exact state_eq_of_frame acc s.basis _ _ _ (a.1.trans b.1.symm) a.2 b.2

theorem unbuild_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (hf':∀f∈earlyHTerms src,Acc.Fits acc Z' bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hz':∀w∈Z',s.basis w=false)
 (hb:∀w∈bank,s.basis w=false) (hi:s.basis cin=false)
 (value:regValue acc s.basis=4294968272*regValue src s.basis):
 run (SourceAddFourDevelop.unbuild acc Z bank cin src) m s=run (SourceAddFourDevelop.unbuild acc Z' bank cin src) m s := by
 have a:=SourceAddFourDevelop.unbuild_triple acc Z bank cin src ha hs hf s.basis hz hb hi s m ⟨value,fun _ _=>rfl⟩
 have b:=SourceAddFourDevelop.unbuild_triple acc Z' bank cin src ha hs hf' s.basis hz' hb hi s m ⟨value,fun _ _=>rfl⟩
 exact state_eq_of_frame acc s.basis 0 _ _ (a.1.trans b.1.symm) a.2 b.2

theorem build_measurements_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.FitsLen Z bank 163 f)
 (hf':∀f∈earlyHTerms src,Acc.FitsLen Z' bank 163 f):
 measurementCount (NarrowAcc.build8 acc Z bank cin src)=measurementCount (NarrowAcc.build8 acc Z' bank cin src) :=
 (NarrowAcc.build8_counts acc Z bank cin src ha (by omega) hf).1.2.trans
  (NarrowAcc.build8_counts acc Z' bank cin src ha (by omega) hf').1.2.symm

theorem plain_loop_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire) (middle:Program)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (hf':∀f∈earlyHTerms src,Acc.Fits acc Z' bank cin 163 f)
 (sub:Z'⊆Z) (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false)
 (hb:∀w∈bank,s.basis w=false) (hi:s.basis cin=false) (zero:regValue acc s.basis=0)
 (H:Nat) (post:WReady acc Z bank cin src H
  (run middle (m.drop (measurementCount (NarrowAcc.build8 acc Z bank cin src)))
   (run (NarrowAcc.build8 acc Z bank cin src) m s))):
 run (NarrowAcc.build8 acc Z bank cin src++middle++SourceAddFourDevelop.unbuild acc Z bank cin src) m s=
 run (NarrowAcc.build8 acc Z' bank cin src++middle++SourceAddFourDevelop.unbuild acc Z' bank cin src) m s := by
 have ct:=build_measurements_repad acc Z Z' bank cin src ha hs (fun f h=>(hf f h).toFitsLen) (fun f h=>(hf' f h).toFitsLen)
 have forward:=build_repad acc Z Z' bank cin src ha hs hf hf' s m hz (fun w hw=>hz w (sub hw)) hb hi zero
 simp only [run_cat,measurementCount_append]
 rw [←ct,←forward]
 apply unbuild_repad acc Z Z' bank cin src ha hs hf hf'
 · exact post.2.2.1
 · exact fun w hw=>post.2.2.1 w (sub hw)
 · exact post.2.2.2.1
 · exact post.2.2.2.2
 · rw [post.2.1]
   exact post.1

#print axioms build_repad
#print axioms unbuild_repad
#print axioms plain_loop_repad
end ECDSAAdd.Entrant.WholePadDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullPadDevelop
open CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def pad (L:CuccaroStreamedSquareWideLayout):List Wire :=
 (L.foldPad.drop 160).take 31

theorem pad_sublist (L:CuccaroStreamedSquareWideLayout) : (pad L).Sublist (accZ L) :=
 (List.take_sublist 31 _).trans (List.sublist_append_right _ _)

theorem domain_sublist (L:CuccaroStreamedSquareWideLayout) (src:List Wire) :
 (L.core.cin::(src++accReg L++pad L++accBank L)).Sublist
 (L.core.cin::(src++accReg L++accZ L++accBank L)) := by
 simp only [List.append_assoc]
 exact List.Sublist.cons₂ _ ((List.Sublist.refl _).append
  ((List.Sublist.refl _).append ((pad_sublist L).append (List.Sublist.refl _))))

theorem pad_length (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) : (pad L).length=31 := by
 simp [pad,hw.core.work,L.foldPad_length hw]

theorem terms_fits (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (accReg L) (pad L) (accBank L) L.core.cin 163 f := by
 intro f mem
 have old:=wTerms_fits L hw hn f mem
 have small:163-f.shift-f.src.length≤31 := by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl <;> simp [Acc.earlyTerm,hiReg_length L hw]
 refine {len:=old.len,zpad:=?_,bankLen:=old.bankLen,nd:=?_}
 · rw [pad_length L hw]
   exact small
 · exact List.Nodup.sublist (domain_sublist L f.src) old.nd

#print axioms terms_fits
end ECDSAAdd.Entrant.FullPadDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.WholePadDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 4000000
 theorem middle_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire) (middle:Program)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (hf':∀f∈earlyHTerms src,Acc.Fits acc Z' bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hz':∀w∈Z',s.basis w=false)
 (hb:∀w∈bank,s.basis w=false) (hi:s.basis cin=false) (zero:regValue acc s.basis=0):
 middleState (NarrowAcc.build8 acc Z bank cin src) middle s m=
 middleState (NarrowAcc.build8 acc Z' bank cin src) middle s m := by
 have ct:=build_measurements_repad acc Z Z' bank cin src ha hs (fun f h=>(hf f h).toFitsLen) (fun f h=>(hf' f h).toFitsLen)
 simp only [middleState,ct]
 rw [build_repad acc Z Z' bank cin src ha hs hf hf' s _ hz hz' hb hi zero]
#print axioms middle_repad
end ECDSAAdd.Entrant.WholePadDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.WholePadTriple
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedVariables false
theorem triple_plain_eq (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire) (middle:Program)
 (hacc:acc.length=163) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (NarrowAcc.build8 acc Z bank cin src) middle s m)):
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s=
 run (NarrowAcc.build8 acc Z bank cin src++middle++SourceAddFourDevelop.unbuild acc Z bank cin src) m s := by
 have a:=cached_wloop_triple_eq acc Z bank cin src q r p middle hacc hsrc hf s m hz hb hi ha zero zeroR zeroP fresh freshR rq freshP pq pr offF offM offI offFR offMR offIR offFP offMP offIP good
 have b:=cached_wloop_dual_eq acc Z bank cin src q r middle hacc hsrc hf s m hz hb hi ha zero zeroR fresh freshR rq offF offM offI offFR offMR offIR good
 exact a.trans b
#print axioms triple_plain_eq
end ECDSAAdd.Entrant.WholePadTriple

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.WholePadTriple
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
 theorem physical (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f) (rq:r≠q)
 (offF:q∉wires (NarrowAcc.build8 acc Z bank cin src))
 (offI:q∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFR:r∉wires (NarrowAcc.build8 acc Z bank cin src))
 (offIR:r∉wires (SourceAddFourDevelop.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r))
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r)):
 GatePhysical (buildTriple acc Z bank cin src q r p) ∧ GatePhysical (unbuildTriple acc Z bank cin src q r p) := by
 have fit:=hf _ (NarrowAcc.terms_mem src).2.2.1
 have hz:5≤Z.length:=by have h:=fit.zpad;norm_num [Acc.earlyTerm,hs] at h;omega
 have hb:132≤bank.length:=by have h:=fit.bankLen;norm_num [Acc.earlyTerm] at h;omega
 have plainF:=(NarrowAcc.build8_physical acc Z bank cin src ha (by omega) hf).1
 have plainI:=SourceAddFourDevelop.unbuild_physical acc Z bank cin src ha hs hf
 have cachedF:=buildCached_physical acc Z bank cin src q ha hs hz hb offF plainF
 have cachedI:=unbuildConsumed_physical acc Z bank cin src q ha hs hb offI plainI
 have offCF:r∉wires (buildCached acc Z bank cin src q):=by
  intro h
  exact (Finset.mem_insert.mp (buildCached_support acc Z bank cin src q ha hs hz hb h)).elim rq offFR
 have offCI:r∉wires (unbuildConsumed acc Z bank cin src q):=by
  intro h
  exact (Finset.mem_insert.mp (unbuildConsumed_support acc Z bank cin src q ha hs hb h)).elim rq offIR
 have dualF:=buildDual_physical acc Z bank cin src q r ha hs hz hb offCF cachedF
 have dualI:=unbuildDual_physical acc Z bank cin src q r ha hs hb offCI cachedI
 exact ⟨buildTriple_physical acc Z bank cin src q r p ha hs hz hb offFP dualF,
  unbuildTriple_physical acc Z bank cin src q r p ha hs hb offIP dualI⟩
#print axioms physical
end ECDSAAdd.Entrant.WholePadTriple

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.WholePadTriple
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
 theorem support (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire)
 (ha:acc.length=163) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 163 f):
 wires (buildTriple acc Z bank cin src q r p) ⊆ (p::r::q::cin::(src++acc++Z++bank)).toFinset ∧
 wires (unbuildTriple acc Z bank cin src q r p) ⊆ (p::r::q::cin::(src++acc++Z++bank)).toFinset := by
 have fit:=hf _ (NarrowAcc.terms_mem src).2.2.1
 have hz:5≤Z.length:=by have h:=fit.zpad;norm_num [Acc.earlyTerm,hs] at h;omega
 have hb:132≤bank.length:=by have h:=fit.bankLen;norm_num [Acc.earlyTerm] at h;omega
 have plain:=NarrowAcc.build8_support acc Z bank cin src ha (by omega) hf
 have unbuild:=SourceAddFourDevelop.unbuild_resources acc Z bank cin src ha hs (fun f h=>(hf f h).toFitsLen)
 constructor
 · intro w hw
   rcases Finset.mem_insert.mp (buildTriple_support acc Z bank cin src q r p ha hs hz hb hw) with eq|hw
   · simp [eq]
   rcases Finset.mem_insert.mp (buildDual_support acc Z bank cin src q r ha hs hz hb hw) with eq|hw
   · simp [eq]
   rcases Finset.mem_insert.mp (buildCached_support acc Z bank cin src q ha hs hz hb hw) with eq|hw
   · simp [eq]
   have h:=List.mem_toFinset.mp (plain.1 hw)
   simp only [List.mem_toFinset,List.mem_cons]
   exact Or.inr (Or.inr (Or.inr (by simpa only [List.mem_cons] using h)))
 · intro w hw
   rcases Finset.mem_insert.mp (unbuildTriple_support acc Z bank cin src q r p ha hs hb hw) with eq|hw
   · simp [eq]
   rcases Finset.mem_insert.mp (unbuildDual_support acc Z bank cin src q r ha hs hb hw) with eq|hw
   · simp [eq]
   rcases Finset.mem_insert.mp (unbuildConsumed_support acc Z bank cin src q ha hs hb hw) with eq|hw
   · simp [eq]
   have oldI := (CodexNarrowTail.build8_support acc Z bank cin src ha (by omega) hf).2
   have h:=List.mem_toFinset.mp (oldI (unbuild.2.2.1 hw))
   simp only [List.mem_toFinset,List.mem_cons]
   exact Or.inr (Or.inr (Or.inr (by simpa only [List.mem_cons] using h)))
#print axioms support
end ECDSAAdd.Entrant.WholePadTriple

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.WholePadConcrete
open InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
 def L := Baselines.layout.dialogStreamedSquareWide
 def pad : List Wire := (L.foldPad.drop 160).take 31
                                                                                      
                                                                                 
                                                                                                    
                                                                                               
                                                                                                                  
                                                                                                                        
                          
                            
end ECDSAAdd.Entrant.WholePadConcrete

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.WholePadConcrete
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
 def oldTripleBuild := buildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
 def newTripleBuild := buildTriple (accReg L) pad (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
 def oldTripleUnbuild := unbuildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
 def newTripleUnbuild := unbuildTriple (accReg L) pad (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)
 theorem triple_build_counts : SeedPadDevelop.Counts newTripleBuild oldTripleBuild := by unfold SeedPadDevelop.Counts; decide +kernel
 theorem triple_unbuild_counts : SeedPadDevelop.Counts newTripleUnbuild oldTripleUnbuild := by unfold SeedPadDevelop.Counts; decide +kernel
#print axioms triple_build_counts
#print axioms triple_unbuild_counts
end ECDSAAdd.Entrant.WholePadConcrete

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullAFoldDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold ManyACarryDevelop
open ECDSAAdd.Entrant.FullPadDevelop (pad)
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def aFoldMany (k:Nat) (L:CuccaroStreamedSquareWideLayout) (g:Wire) (hs:List Wire) (middle:Program):Program:=
 buildMany k (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) hs L.core.sumCarry (eV L) (spare L)++middle++
 unbuildMany k (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) hs L.core.sumCarry (eV L) (spare L)

theorem aFoldMany_eq (k:Nat) (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (hg:g∉L.wires)
 (hk:k≤119) (ndhs:hs.Nodup) (hostlen:hs.length=k)
 (work:∀u∈hs,u∈L.core.work)
 (freshU:∀u∈hs,u∉L.core.cin::(hiReg L++accReg L++pad L++accBank L))
 (oldNe:∀u∈hs,u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L)
 (cert:ZeroSetDevelop.SRewrites hs (aMiddle L g) newMiddle) (base : BasisState) (hc:L.PairClean base)
 (hsum:base L.core.sumCarry=false) (hV:base (eV L)=false) (hP:base (spare L)=false)
 (O : Nat) (hO:O<SquareReduction.p) (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
 run (aFoldMany k L g hs newMiddle) m s=run (aFoldTriple L g) m s := by
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have lens:=acc_lengths L hw
 have fullfit:=wTerms_fits L hw hn
 have newfit:=FullPadDevelop.terms_fits L hw hn
 have seedmem:= (NarrowAcc.terms_mem (hiReg L)).1
 have hzFull:∀q∈accZ L,s.basis q=false := by
  intro q hq
  rcases accZ_mem L q hq with h|h
  · exact (regValue_zero _ _).mp clean.pad q h
  · exact (regValue_zero _ _).mp clean.work q (List.mem_of_mem_drop h)
 have hz:∀q∈pad L,s.basis q=false := fun q hq=>hzFull q ((FullPadDevelop.pad_sublist L).subset hq)
 have hb:∀q∈accBank L,s.basis q=false := fun q hq=>
  (regValue_zero _ _).mp clean.pad q (List.mem_of_mem_take hq)
 have ha:regValue (accReg L) s.basis=0 :=
  (regValue_zero _ _).mpr (fun q hq=>(regValue_zero _ _).mp clean.work q (accReg_work L q hq))
 have away:=ParkCarryDevelop.sumCarry_off_regs L hn
 have zero:s.basis L.core.sumCarry=false := (hf.2 _ away.1).trans hsum
 have originalOff:=a_wloop_sumCarry_free L hw hn g hg
 have zeroR:s.basis (eV L)=false :=
  (hf.2 _ (eReg_away L hn _ (eK_mem L hw).2.2.1).1).trans hV
 have freshR:eV L∉L.core.cin::(hiReg L++accReg L++pad L++accBank L) := by
  intro h
  exact eV_fresh_domain L hw hn ((FullPadDevelop.domain_sublist L _).subset h)
 have fresh:L.core.sumCarry∉L.core.cin::(hiReg L++accReg L++pad L++accBank L) := by
  intro h
  exact sumCarry_fresh_domain L hn ((FullPadDevelop.domain_sublist L _).subset h)
 have off:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry
  lens.1 (hiReg_length L hw) newfit fresh
 have offR:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (eV L)
  lens.1 (hiReg_length L hw) newfit freshR
 have zeroP:s.basis (spare L)=false:=
  (hf.2 _ (eReg_away L hn _ (spare_mem_eReg L hw)).1).trans hP
 have freshP:spare L∉L.core.cin::(hiReg L++accReg L++pad L++accBank L) := by
  intro h
  exact spare_fresh_domain L hw hn ((FullPadDevelop.domain_sublist L _).subset h)
 have offPlainP:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (spare L)
  lens.1 (hiReg_length L hw) newfit freshP
 have offP:=SeedPadDevelop.dual_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (eV L) (spare L) lens.1 (hiReg_length L hw)
  (by rw [FullPadDevelop.pad_length L hw];decide) (by omega)
  offPlainP.1 offPlainP.2 (spare_ne_sumCarry L hw hn) (spare_ne_eV L hw hn)
 have zeroU:∀u∈hs,s.basis u=false:=by
  intro u hu
  exact (regValue_zero _ _).mp clean.work u (work u hu)
 have offU (u:Wire) (hu:u∈hs):u∉wires (buildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)) ∧
  u∉wires (unbuildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)):=
  fresh_off_triple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
   L.core.sumCarry (eV L) (spare L) u lens.1 (hiReg_length L hw) newfit
   (freshU u hu) (oldNe u hu).1 (oldNe u hu).2.1 (oldNe u hu).2.2
 have oldGood:=a_middle_good L hw hn g hg base hc O hO s m hf
 have middleEq:=WholePadDevelop.middle_repad (accReg L) (accZ L) (pad L) (accBank L) L.core.cin
  (hiReg L) (aMiddle L g) lens.1 (hiReg_length L hw) fullfit newfit s m hzFull hz hb clean.cin ha
 have good:WReady (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (regValue (hiReg L) s.basis)
  (middleState (NarrowAcc.build8 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)) (aMiddle L g) s m) := by
  rw [←middleEq]
  exact ⟨oldGood.1,oldGood.2.1,(fun w hw=>oldGood.2.2.1 w ((FullPadDevelop.pad_sublist L).subset hw)),oldGood.2.2.2⟩
 have eq:=compiled_wloop_many_eq_set k (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L) (aMiddle L g) newMiddle
  lens.1 (hiReg_length L hw) newfit s m hz hb clean.cin ha zero zeroR zeroP
  fresh freshR (eV_ne_sumCarry L hw hn) freshP (spare_ne_sumCarry L hw hn) (spare_ne_eV L hw hn)
  off.1 originalOff.2.1 off.2 offR.1 (eV_off_amiddle L hw hn g hg) offR.2
  offP.1 (spare_off_amiddle L hw hn g hg) offP.2 hk ndhs hostlen zeroU freshU oldNe
  (fun u hu=>(offU u hu).1) (fun u hu=>(offU u hu).2) cert good
 have oldOffR:=wloop_original_off (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) (eV L)
  lens.1 (hiReg_length L hw) fullfit (eV_fresh_domain L hw hn)
 have oldOffP:=spare_off_dual L hw hn
 have newPlain:=WholePadTriple.triple_plain_eq (accReg L) (pad L) (accBank L) L.core.cin
  (hiReg L) L.core.sumCarry (eV L) (spare L) (aMiddle L g) lens.1 (hiReg_length L hw) newfit
  s m hz hb clean.cin ha zero zeroR zeroP fresh freshR (eV_ne_sumCarry L hw hn)
  freshP (spare_ne_sumCarry L hw hn) (spare_ne_eV L hw hn)
  off.1 originalOff.2.1 off.2 offR.1 (eV_off_amiddle L hw hn g hg) offR.2
  offP.1 (spare_off_amiddle L hw hn g hg) offP.2 good
 have oldPlain:=WholePadTriple.triple_plain_eq (accReg L) (accZ L) (accBank L) L.core.cin
  (hiReg L) L.core.sumCarry (eV L) (spare L) (aMiddle L g) lens.1 (hiReg_length L hw) fullfit
  s m hzFull hb clean.cin ha zero zeroR zeroP
  (sumCarry_fresh_domain L hn) (eV_fresh_domain L hw hn) (eV_ne_sumCarry L hw hn)
  (spare_fresh_domain L hw hn) (spare_ne_sumCarry L hw hn) (spare_ne_eV L hw hn)
  originalOff.1 originalOff.2.1 originalOff.2.2 oldOffR.1 (eV_off_amiddle L hw hn g hg) oldOffR.2
  oldOffP.1 (spare_off_amiddle L hw hn g hg) oldOffP.2 oldGood
 have repad:=WholePadDevelop.plain_loop_repad (accReg L) (accZ L) (pad L) (accBank L) L.core.cin
  (hiReg L) (aMiddle L g) lens.1 (hiReg_length L hw) fullfit newfit
  (FullPadDevelop.pad_sublist L).subset s m hzFull hb clean.cin ha (regValue (hiReg L) s.basis)
  (by simpa only [middleState,run_take] using oldGood)
 exact eq.trans (newPlain.trans (repad.symm.trans (by simpa only [aFoldTriple] using oldPlain.symm)))

#print axioms aFoldMany_eq
end ECDSAAdd.Entrant.FullAFoldDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullAFoldDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold ManyACarryDevelop
open ECDSAAdd.Entrant.FullPadDevelop (pad)
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
 def MetricReady (L:CuccaroStreamedSquareWideLayout):Prop :=
 SeedPadDevelop.Counts
  (buildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L))
  (buildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)) ∧
 SeedPadDevelop.Counts
  (unbuildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L))
  (unbuildTriple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L))
 instance (L:CuccaroStreamedSquareWideLayout):Decidable (MetricReady L):=by
  unfold MetricReady SeedPadDevelop.Counts
  infer_instance
 theorem metric_ready : MetricReady Baselines.layout.dialogStreamedSquareWide :=
  ⟨WholePadConcrete.triple_build_counts, WholePadConcrete.triple_unbuild_counts⟩
theorem aFoldMany_resources (k:Nat) (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire) (hs:List Wire) (middle:Program)
 (metric:MetricReady L) (hk:k≤119) (hostlen:hs.length=k) (cert:ZeroSetDevelop.SRewrites hs (aMiddle L g) middle):
 toffoliCount (aFoldMany k L g hs middle)+k≤toffoliCount (aFoldTriple L g) ∧
 measurementCount (aFoldMany k L g hs middle)=measurementCount (aFoldTriple L g) ∧
 Challenge.gateSlots (aFoldMany k L g hs middle)+3*k≤Challenge.gateSlots (aFoldTriple L g) := by
 have lens:=acc_lengths L hw
 have plen:=FullPadDevelop.pad_length L hw
 have h:=compiled_counts_set k (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) hs L.core.sumCarry (eV L) (spare L)
  (aMiddle L g) middle lens.1 (hiReg_length L hw) (by omega) (by omega) hk hostlen cert
 have mid : SeedPadDevelop.Counts (aMiddle L g) (aMiddle L g) := ⟨rfl,rfl,rfl⟩
 have r := (metric.1.append mid).append metric.2
 change SeedPadDevelop.Counts _ (aFoldTriple L g) at r
 change toffoliCount _+k≤toffoliCount (aFoldTriple L g) ∧
  measurementCount _=measurementCount (aFoldTriple L g) ∧ Challenge.gateSlots _+3*k≤Challenge.gateSlots (aFoldTriple L g)
 refine ⟨?_,?_,?_⟩
 · rw [←r.1]
   exact h.1
 · exact h.2.1.trans r.2.1
 · rw [←r.2.2]
   exact h.2.2


#print axioms metric_ready
#print axioms aFoldMany_resources
end ECDSAAdd.Entrant.FullAFoldDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullFitReady
open InverseCarryDevelop ZeroReadDevelop
set_option maxHeartbeats 4000000
 def Fields (L:CuccaroStreamedSquareWideLayout) (f:MeasuredSquareFold):Prop :=
  f.src.length+f.shift<163 ∧ 163-f.shift-f.src.length≤(FullPadDevelop.pad L).length ∧
  163-f.shift-1≤(accBank L).length ∧
  (L.core.cin::(f.src++accReg L++FullPadDevelop.pad L++accBank L)).Nodup
 def Ready (L:CuccaroStreamedSquareWideLayout):Prop := ∀ f∈earlyHTerms (hiReg L),Fields L f
 instance (L:CuccaroStreamedSquareWideLayout):Decidable (Ready L):=by
  unfold Ready Fields
  infer_instance
 theorem sound (L:CuccaroStreamedSquareWideLayout) (h:Ready L):
  ∀f∈earlyHTerms (hiReg L),Acc.Fits (accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin 163 f := by
  intro f hf
  have h:=h f hf
  exact {len:=h.1,zpad:=h.2.1,bankLen:=h.2.2.1,nd:=h.2.2.2}
 theorem actual : Ready Baselines.layout.dialogStreamedSquareWide := by
  intro f hf
  have h:=FullPadDevelop.terms_fits Baselines.layout.dialogStreamedSquareWide (Baselines.layout.dialogStreamedSquareWide_widths Baselines.layout_widths) (Baselines.layout.dialogStreamedSquareWide_nodup Baselines.layout_widths Baselines.layout_nodup) f hf
  exact ⟨h.len,h.zpad,h.bankLen,h.nd⟩
#print axioms sound
#print axioms actual
end ECDSAAdd.Entrant.FullFitReady

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullPadSupport
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
 def supportDomain (L:CuccaroStreamedSquareWideLayout):List Wire :=
  L.core.sumCarry::eV L::spare L::L.core.cin::(hiReg L++accReg L++FullPadDevelop.pad L++accBank L)
 def SupportReady (L:CuccaroStreamedSquareWideLayout) (g:Wire):Prop :=
  ∀w∈supportDomain L,hasWire (aBodyTriple L g) w=true
 instance (L:CuccaroStreamedSquareWideLayout) (g:Wire):Decidable (SupportReady L g):=by
  unfold SupportReady
  infer_instance
 def L := Baselines.layout.dialogStreamedSquareWide
 def c := Baselines.layout.core.generic
 theorem used0 : ∀w∈((supportDomain L).drop 0).take 80,hasWire (aBodyTriple L c) w=true := by decide +kernel
#print axioms used0
 theorem used1 : ∀w∈((supportDomain L).drop 80).take 80,hasWire (aBodyTriple L c) w=true := by decide +kernel
#print axioms used1
 theorem used2 : ∀w∈((supportDomain L).drop 160).take 80,hasWire (aBodyTriple L c) w=true := by decide +kernel
#print axioms used2
 theorem used3 : ∀w∈((supportDomain L).drop 240).take 80,hasWire (aBodyTriple L c) w=true := by decide +kernel
#print axioms used3
 theorem used4 : ∀w∈((supportDomain L).drop 320).take 80,hasWire (aBodyTriple L c) w=true := by decide +kernel
#print axioms used4
 theorem used5 : ∀w∈((supportDomain L).drop 400).take 80,hasWire (aBodyTriple L c) w=true := by decide +kernel
#print axioms used5
 theorem used6 : ∀w∈((supportDomain L).drop 480).take 80,hasWire (aBodyTriple L c) w=true := by decide +kernel
#print axioms used6
 theorem domain_split : supportDomain L = ((supportDomain L).drop 0).take 80 ++ ((supportDomain L).drop 80).take 80 ++ ((supportDomain L).drop 160).take 80 ++ ((supportDomain L).drop 240).take 80 ++ ((supportDomain L).drop 320).take 80 ++ ((supportDomain L).drop 400).take 80 ++ ((supportDomain L).drop 480).take 80 := by decide +kernel
 theorem actual_support_ready : SupportReady L c := by
  unfold SupportReady
  rw [domain_split]
  simp only [List.mem_append,or_imp,forall_and]
  exact ⟨⟨⟨⟨⟨⟨used0, used1⟩, used2⟩, used3⟩, used4⟩, used5⟩, used6⟩
#print axioms actual_support_ready
end ECDSAAdd.Entrant.FullPadSupport

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullAFoldDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold ManyACarryDevelop
open ECDSAAdd.Entrant.FullPadDevelop (pad)
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
 theorem triple_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) (g:Wire)
 (physical:GatePhysical (aFoldTriple L g)):
 GatePhysical (buildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)++aMiddle L g++
 unbuildTriple (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry (eV L) (spare L)) := by
 have lens:=acc_lengths L hw
 have newfit:=FullPadDevelop.terms_fits L hw hn
 have fresh:L.core.sumCarry∉L.core.cin::(hiReg L++accReg L++pad L++accBank L):=by
  intro h
  exact sumCarry_fresh_domain L hn ((FullPadDevelop.domain_sublist L _).subset h)
 have freshR:eV L∉L.core.cin::(hiReg L++accReg L++pad L++accBank L):=by
  intro h
  exact eV_fresh_domain L hw hn ((FullPadDevelop.domain_sublist L _).subset h)
 have freshP:spare L∉L.core.cin::(hiReg L++accReg L++pad L++accBank L):=by
  intro h
  exact spare_fresh_domain L hw hn ((FullPadDevelop.domain_sublist L _).subset h)
 have off:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry lens.1 (hiReg_length L hw) newfit fresh
 have offR:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (eV L) lens.1 (hiReg_length L hw) newfit freshR
 have offP:=wloop_original_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (spare L) lens.1 (hiReg_length L hw) newfit freshP
 have dualP:=SeedPadDevelop.dual_off (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (eV L) (spare L) lens.1 (hiReg_length L hw)
  (by rw [FullPadDevelop.pad_length L hw];decide) (by omega)
  offP.1 offP.2 (spare_ne_sumCarry L hw hn) (spare_ne_eV L hw hn)
 have pp:=WholePadTriple.physical (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (eV L) (spare L) lens.1 (hiReg_length L hw) newfit (eV_ne_sumCarry L hw hn)
  off.1 off.2 offR.1 offR.2 dualP.1 dualP.2
 simp only [aFoldTriple,gatePhysical_append] at physical
 simp only [gatePhysical_append]
 exact ⟨⟨pp.1,physical.1.2⟩,pp.2⟩
#print axioms triple_physical
end ECDSAAdd.Entrant.FullAFoldDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullAFoldDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop ControlLoan1589BFFold ManyACarryDevelop
open ECDSAAdd.Entrant.FullPadDevelop (pad)
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
 theorem aFoldMany_support_body (k:Nat) (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire) (hs:List Wire) (middle:Program)
 (fit:FullFitReady.Ready L) (support:FullPadSupport.SupportReady L g)
 (used:∀u∈hs,hasWire (aBodyTriple L g) u=true)
 (hk:k≤119) (cert:ZeroSetDevelop.SRewrites hs (aMiddle L g) middle):
 wires (aFoldMany k L g hs middle) ⊆ wires (aBodyTriple L g) := by
 have lens:=acc_lengths L hw
 have plen:=FullPadDevelop.pad_length L hw
 have h:=compiled_support_set k (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) hs L.core.sumCarry (eV L) (spare L)
  (aMiddle L g) middle lens.1 (hiReg_length L hw) (by omega) (by omega) hk cert
 have tri:=WholePadTriple.support (accReg L) (pad L) (accBank L) L.core.cin (hiReg L)
  L.core.sumCarry (eV L) (spare L) lens.1 (hiReg_length L hw) (FullFitReady.sound L fit)
 have domain (w:Wire) (mem:w∈(spare L::eV L::L.core.sumCarry::L.core.cin::(hiReg L++accReg L++pad L++accBank L)).toFinset):
  w∈wires (aBodyTriple L g) := by
  apply (FourthASavedCarryDevelop.hasWire_iff _ _).mp
  apply support w
  simp only [FullPadSupport.supportDomain,List.mem_cons] at mem ⊢
  simp only [List.mem_toFinset,List.mem_cons] at mem
  rcases mem with h|h|h|h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr h))
 have oldfold:wires (aFoldTriple L g)⊆wires (aBodyTriple L g):=by
  intro w hw
  simp only [aBodyTriple,wires_append,Finset.mem_union]
  exact Or.inr (Or.inr hw)
 intro w hw
 rcases Finset.mem_union.mp (h hw) with hw|hw
 · simp only [wires_append,Finset.mem_union] at hw
   rcases hw with (hw|hw)|hw
   · exact domain w (tri.1 hw)
   · apply oldfold
     simp only [aFoldTriple,wires_append,Finset.mem_union]
     exact Or.inl (Or.inr hw)
   · exact domain w (tri.2 hw)
 · exact (FourthASavedCarryDevelop.hasWire_iff _ _).mp (used w (List.mem_toFinset.mp hw))
#print axioms aFoldMany_support_body
end ECDSAAdd.Entrant.FullAFoldDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
open ECDSAAdd.Entrant.FullPadDevelop (pad)
open ECDSAAdd.Entrant.FullAFoldDevelop (aFoldMany aFoldMany_eq aFoldMany_resources)
namespace ECDSAAdd.Entrant.FullASelectedDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop
open ControlLoan1589BFFold FourthASavedCarryDevelop

def PadReady (L:CuccaroStreamedSquareWideLayout) (g:Wire):Prop :=
 FullAFoldDevelop.MetricReady L ∧ FullFitReady.Ready L ∧ FullPadSupport.SupportReady L g

end ECDSAAdd.Entrant.FullASelectedDevelop

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullASelectedDevelop
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option maxHeartbeats 6000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def loans (L:CuccaroStreamedSquareWideLayout):List Wire:=(L.core.work.drop 163).take 33 ++ (L.core.work.drop 255).take 1 ++ (L.core.work.drop 227).take 28 ++ (L.core.work.drop 201).take 10 ++ (L.core.work.drop 212).take 15 ++ (L.core.work.drop 211).take 1 ++ (L.core.work.drop 196).take 5

def LoanReadyWide (L : CuccaroStreamedSquareWideLayout) (g u : Wire) : Prop :=
 u∈L.core.work ∧ u∉L.core.cin::(hiReg L++accReg L++pad L++accBank L) ∧
 u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L ∧ hasWire (aBodyTriple L g) u=true
instance (L : CuccaroStreamedSquareWideLayout) (g u : Wire) : Decidable (LoanReadyWide L g u) := by
 unfold LoanReadyWide
 infer_instance

def BankReady (L:CuccaroStreamedSquareWideLayout) (g:Wire) (hs:List Wire):Prop:=
 hs.length=93 ∧ hs.Nodup ∧ (∀u∈hs,LoanReadyWide L g u) ∧ PadReady L g
instance (L:CuccaroStreamedSquareWideLayout) (g:Wire) (hs:List Wire):Decidable (BankReady L g hs):=by
 unfold BankReady PadReady
 infer_instance

def aFoldSelected (L:CuccaroStreamedSquareWideLayout) (g:Wire):Program:=
 let hs:=loans L
 if hr:BankReady L g hs then
  match ZeroSetDevelop.compileS? hs (aMiddle L g) with
  | none=>aFoldTriple L g
  | some cm=>aFoldMany 93 L g hs cm.out
 else aFoldTriple L g

theorem aFoldSelected_eq (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false) (O:Nat) (hO:O<SquareReduction.p)
 (s:State) (m:List Bool) (hf:SquareFrame L.core.out base O s.basis):
 run (aFoldSelected L g) m s=run (aFoldTriple L g) m s:=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:ZeroSetDevelop.compileS? (loans L) (aMiddle L g) with
   | none=>rfl
   | some cm=>
    exact aFoldMany_eq 93 L hw hn g (loans L) cm.out hg (by decide) hr.2.1 hr.1
     (fun u hu=>(hr.2.2.1 u hu).1) (fun u hu=>(hr.2.2.1 u hu).2.1)
     (fun u hu=>⟨(hr.2.2.1 u hu).2.2.1,(hr.2.2.1 u hu).2.2.2.1,(hr.2.2.1 u hu).2.2.2.2.1⟩)
     cm.proof base hc hsum hV hP O hO s m hf
 · rfl

#print axioms aFoldSelected_eq
end ECDSAAdd.Entrant.FullASelectedDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullASelectedDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem aFoldSelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 toffoliCount (aFoldSelected L g)≤toffoliCount (aFoldTriple L g) ∧
 measurementCount (aFoldSelected L g)=measurementCount (aFoldTriple L g) ∧
 Challenge.gateSlots (aFoldSelected L g)≤Challenge.gateSlots (aFoldTriple L g):=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:ZeroSetDevelop.compileS? (loans L) (aMiddle L g) with
   | none=>exact ⟨le_rfl,rfl,le_rfl⟩
   | some cm=>
    dsimp only
    have h:=aFoldMany_resources 93 L hw g (loans L) cm.out hr.2.2.2.1 (by decide) hr.1 cm.proof
    exact ⟨by omega,h.2.1,by omega⟩
 · exact ⟨le_rfl,rfl,le_rfl⟩
#print axioms aFoldSelected_resources
end ECDSAAdd.Entrant.FullASelectedDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullASelectedDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem aFoldSelected_frame (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false) (O:Nat) (hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) (aFoldSelected L g)
  (SquareFrame L.core.out base (((if base g then OwnDiagAll12Square.cFlipK-4294968272*regValue (hiReg L) base
   else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hs
 rw[aFoldSelected_eq L hw hn g hg base hc hsum hV hP O hO s m hs]
 exact aFoldTriple_frame L hw hn g hg base hc hsum hV hP O hO s m hs

#print axioms aFoldSelected_frame
end ECDSAAdd.Entrant.FullASelectedDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullASelectedDevelop
open ThirdSavedCarryDevelop Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def aBodySelected (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++aFoldSelected L c)
theorem aBodySelected_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) :
    Triple (SquareFrame L.core.out base O) (aBodySelected L c) (SquareFrame L.core.out base (resAF (M^2) O (base c))) := by
  have pmod : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
  have hb : M^2<2^256 := by simpa using square_bound M 128 hM
  have vZero:base (eV L)=false := eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
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
  have t1 : Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)) (SquareFrame L.core.out base O1) := by
    have h := measuredFoldQ_frameTq L hw hn base (negP L) v1 rfl hc O hO
    rwa [pay1] at h
  have t2 : Triple (SquareFrame L.core.out base O1) (measuredFoldQTq L (rot128F L))
      (SquareFrame L.core.out base O2) := by
    have h := measuredFoldQ_frameTq L hw hn base (rot128F L) v2 rfl hc O1 hO1
    rwa [pay2] at h
  have hAeq : Acc.accVal base 0 (aAcc L).spec=4294968272*regValue (hiReg L) base := by
    rw [show (aAcc L).spec=earlyHTerms (L.core.product.drop 128) from rfl,accVal_earlyH]
    congr 1
    rw [hiReg,regValue_drop_div _ 128 (by simp [hw.core.product]),
      regValue_drop_div _ 128 (by simp [hw.core.product]),
      L.product_take_value hw base (M^2) hP 256 (by omega),Nat.mod_eq_of_lt hb,hP]
  have t3 := aFoldSelected_frame L hw hn c hcw base hc hzero vZero (spare_zero L hw base M hP) O2 hO2
  rw [← hAeq] at t3
  have all := t1.seq (t2.seq t3)
  apply Triple.conseq (fun s h => h) all
  intro s hs
  refine ⟨hs.1.trans ?_,hs.2⟩
  let A := Acc.accVal base 0 (aAcc L).spec
  have hA : A<2^163 := Acc.accVal_lt base 163 (aAcc L).spec 0 (by norm_num) v3.specValid
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
  have bound : ((if base c then OwnDiagAll12Square.cFlipK-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p) else 0)))).symm
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
    have hAle : A≤OwnDiagAll12Square.cFlipK := by simp only [OwnDiagAll12Square.cFlipK]; omega
    have hoff : ((OwnDiagAll12Square.cFlipK-A : Nat) : ZMod SquareReduction.p)=(OwnDiagAll12Square.cFlipK : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum

#print axioms aBodySelected_frame
end ECDSAAdd.Entrant.FullASelectedDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullASelectedDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ZeroReadDevelop
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem aFoldSelected_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 wires (aFoldSelected L g)⊆wires (aBodyTriple L g) := by
 have oldfold:wires (aFoldTriple L g)⊆wires (aBodyTriple L g):=by
  intro w hw
  simp only [aBodyTriple,wires_append,Finset.mem_union]
  exact Or.inr (Or.inr hw)
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:ZeroSetDevelop.compileS? (loans L) (aMiddle L g) with
   | none=>exact oldfold
   | some cm=>
    exact FullAFoldDevelop.aFoldMany_support_body 93 L hw g (loans L) cm.out
      hr.2.2.2.2.1 hr.2.2.2.2.2 (fun u hu=>(hr.2.2.1 u hu).2.2.2.2.2) (by decide) cm.proof
 · exact oldfold

theorem aFoldSelected_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) (g:Wire)
 (physical:GatePhysical (aFoldTriple L g)):GatePhysical (aFoldSelected L g):=by
 unfold aFoldSelected
 dsimp only
 split
 · rename_i hr
   cases he:ZeroSetDevelop.compileS? (loans L) (aMiddle L g) with
   | none=>exact physical
   | some cm=>
    have lens:=acc_lengths L hw
    have plen:=FullPadDevelop.pad_length L hw
    have fresh:∀u∈loans L,u∉accBank L:=by
     intro u hu bad
     exact (hr.2.2.1 u hu).2.1 (by simp[bad])
    exact ManyACarryDevelop.compiled_physical_set 93 (accReg L) (pad L) (accBank L) L.core.cin (hiReg L) (loans L) L.core.sumCarry (eV L) (spare L)
     (aMiddle L g) cm.out lens.1 (hiReg_length L hw) (by omega) (by omega) (by decide) fresh cm.proof (FullAFoldDevelop.triple_physical L hw hn g physical)
 · exact physical

theorem aBodySelected_subset (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 wires (aBodySelected L g)⊆wires (aBodyTriple L g):=by
 have fold:=aFoldSelected_support L hw g
 intro w hw
 simp only[aBodySelected,wires_append,Finset.mem_union]at hw
 rcases hw with hw|(hw|hw)
 · simp only[aBodyTriple,wires_append,Finset.mem_union];exact Or.inl hw
 · simp only[aBodyTriple,wires_append,Finset.mem_union];exact Or.inr (Or.inl hw)
 · exact fold hw

theorem aBodySelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire):
 toffoliCount (aBodySelected L g)≤2915 ∧ measurementCount (aBodySelected L g)=3077 ∧
 Challenge.gateSlots (aBodySelected L g)≤Challenge.gateSlots (aBodyTriple L g):=by
 have old:=aBodyTriple_counts L hw g
 have h:=aFoldSelected_resources L hw g
 simp only[aBodySelected,aBodyTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]at old ⊢
 exact ⟨by omega,by omega,by omega⟩

theorem aBodySelected_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g:Wire)
 (hn:(g::L.wires).Nodup):GatePhysical (aBodySelected L g):=by
 have old:=aBodyTriple_physical L hw g hn
 simp only[aBodyTriple,gatePhysical_append]at old
 have fold:=aFoldSelected_physical L hw (List.nodup_cons.mp hn).2 g old.2.2
 simp only[aBodySelected,gatePhysical_append]
 exact ⟨old.1,old.2.1,fold⟩
#print axioms aBodySelected_subset
#print axioms aBodySelected_resources
#print axioms aBodySelected_physical
end ECDSAAdd.Entrant.FullASelectedDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullASelectedDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ControlLoan1589BFFold ParkCarryDevelop
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def hostedASelected (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire):Program:=aBodySelected (hostLayout L rho) c

theorem hostedASelected_eq (L:CuccaroStreamedSquareWideLayout) (rho:Equiv.Perm Wire) (c:Wire)
 (h:rho L.core.sumCarry=L.core.sumCarry):hostedASelected L rho c=aBodySelected L c:=by
 rw[hostedASelected,host_eq L rho h]

theorem hostedASelected_subset (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 wires (hostedASelected L rho c)⊆wires (hostedATriple L rho c):=
 aBodySelected_subset (hostLayout L rho) (host_widths L hw rho) c

theorem hostedASelected_resources (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (rho:Equiv.Perm Wire) (c:Wire):
 toffoliCount (hostedASelected L rho c)≤toffoliCount (hostedATriple L rho c) ∧
 measurementCount (hostedASelected L rho c)=measurementCount (hostedATriple L rho c) ∧
 Challenge.gateSlots (hostedASelected L rho c)≤Challenge.gateSlots (hostedATriple L rho c):=by
 have h:=aBodySelected_resources (hostLayout L rho) (host_widths L hw rho) c
 have o:=aBodyTriple_counts (hostLayout L rho) (host_widths L hw rho) c
 exact ⟨by simpa only[hostedASelected,hostedATriple,o.1]using h.1,
  by simp only[hostedASelected,hostedATriple,h.2.1,o.2],h.2.2⟩
#print axioms hostedASelected_subset
#print axioms hostedASelected_resources
end ECDSAAdd.Entrant.FullASelectedDevelop

end

section
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.FullASelectedDevelop
open Arithmetic.CuccaroStreamedSquareWideLayout ThirdSavedCarryDevelop
set_option linter.unusedSimpArgs false

theorem aBodySelected_refined (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 wires (aBodySelected L c)⊆insert (spare L) (wires (InverseCarryDevelop.aBodyDual L c)):=
 (aBodySelected_subset L hw c).trans (aBodyTriple_refined L hw c)

theorem aBodySelected_support (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) (c:Wire):
 wires (aBodySelected L c)⊆(c::L.wires).toFinset:=
 (aBodySelected_subset L hw c).trans (aBodyTriple_support L hw hn c)
end ECDSAAdd.Entrant.FullASelectedDevelop

end


end


-- Verified gate replacement helper: B84PostLiteral
section
namespace B84PostLiteralResearch
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false

def actualLayout := Baselines.layout.dialogStreamedSquareWide
def actualPost : Program := InverseCarryDevelop.buildPost (accReg actualLayout)
 (FullPadDevelop.pad actualLayout) (accBank actualLayout) actualLayout.core.cin (hiReg actualLayout)

def dataChunk0 : Program := [
 .CX 4243 4533,
 .CX 4243 4760,
 .CCX 4533 4760 4373,
 .CX 4243 4373,
 .CX 4243 4760,
 .CX 4243 4533,
 .CX 4244 4534,
 .CX 4244 4373,
 .CCX 4534 4373 4374,
 .CX 4244 4374,
 .CX 4244 4373,
 .CX 4244 4534,
 .CX 4245 4535,
 .CX 4245 4374,
 .CCX 4535 4374 4375,
 .CX 4245 4375,
 .CX 4245 4374,
 .CX 4245 4535,
 .CX 4246 4536,
 .CX 4246 4375,
 .CCX 4536 4375 4376,
 .CX 4246 4376,
 .CX 4246 4375,
 .CX 4246 4536,
 .CX 4247 4537,
 .CX 4247 4376,
 .CCX 4537 4376 4377,
 .CX 4247 4377,
 .CX 4247 4376,
 .CX 4247 4537,
 .CX 4248 4538,
 .CX 4248 4377,
 .CCX 4538 4377 4378,
 .CX 4248 4378,
 .CX 4248 4377,
 .CX 4248 4538,
 .CX 4249 4539,
 .CX 4249 4378,
 .CCX 4539 4378 4379,
 .CX 4249 4379,
 .CX 4249 4378,
 .CX 4249 4539,
 .CX 4250 4540,
 .CX 4250 4379,
 .CCX 4540 4379 4380,
 .CX 4250 4380,
 .CX 4250 4379,
 .CX 4250 4540,
 .CX 4251 4541,
 .CX 4251 4380,
 .CCX 4541 4380 4381,
 .CX 4251 4381,
 .CX 4251 4380,
 .CX 4251 4541,
 .CX 4252 4542,
 .CX 4252 4381,
 .CCX 4542 4381 4382,
 .CX 4252 4382,
 .CX 4252 4381,
 .CX 4252 4542,
 .CX 4253 4543,
 .CX 4253 4382,
 .CCX 4543 4382 4383,
 .CX 4253 4383,
 .CX 4253 4382,
 .CX 4253 4543,
 .CX 4254 4544,
 .CX 4254 4383,
 .CCX 4544 4383 4384,
 .CX 4254 4384,
 .CX 4254 4383,
 .CX 4254 4544,
 .CX 4255 4545,
 .CX 4255 4384,
 .CCX 4545 4384 4385,
 .CX 4255 4385,
 .CX 4255 4384,
 .CX 4255 4545,
 .CX 4256 4546,
 .CX 4256 4385,
 .CCX 4546 4385 4386,
 .CX 4256 4386,
 .CX 4256 4385,
 .CX 4256 4546,
 .CX 4257 4547,
 .CX 4257 4386,
 .CCX 4547 4386 4387,
 .CX 4257 4387,
 .CX 4257 4386,
 .CX 4257 4547,
 .CX 4258 4548,
 .CX 4258 4387,
 .CCX 4548 4387 4388,
 .CX 4258 4388,
 .CX 4258 4387,
 .CX 4258 4548,
 .CX 4259 4549,
 .CX 4259 4388,
 .CCX 4549 4388 4389,
 .CX 4259 4389,
 .CX 4259 4388,
 .CX 4259 4549,
 .CX 4260 4550,
 .CX 4260 4389,
 .CCX 4550 4389 4390,
 .CX 4260 4390,
 .CX 4260 4389,
 .CX 4260 4550,
 .CX 4261 4551,
 .CX 4261 4390,
 .CCX 4551 4390 4391,
 .CX 4261 4391,
 .CX 4261 4390,
 .CX 4261 4551,
 .CX 4262 4552,
 .CX 4262 4391,
 .CCX 4552 4391 4392,
 .CX 4262 4392,
 .CX 4262 4391,
 .CX 4262 4552,
 .CX 4263 4553,
 .CX 4263 4392,
 .CCX 4553 4392 4393,
 .CX 4263 4393,
 .CX 4263 4392,
 .CX 4263 4553,
 .CX 4264 4554,
 .CX 4264 4393]

def dataChunk1 : Program := [
 .CCX 4554 4393 4394,
 .CX 4264 4394,
 .CX 4264 4393,
 .CX 4264 4554,
 .CX 4265 4555,
 .CX 4265 4394,
 .CCX 4555 4394 4395,
 .CX 4265 4395,
 .CX 4265 4394,
 .CX 4265 4555,
 .CX 4266 4556,
 .CX 4266 4395,
 .CCX 4556 4395 4396,
 .CX 4266 4396,
 .CX 4266 4395,
 .CX 4266 4556,
 .CX 4267 4557,
 .CX 4267 4396,
 .CCX 4557 4396 4397,
 .CX 4267 4397,
 .CX 4267 4396,
 .CX 4267 4557,
 .CX 4268 4558,
 .CX 4268 4397,
 .CCX 4558 4397 4398,
 .CX 4268 4398,
 .CX 4268 4397,
 .CX 4268 4558,
 .CX 4269 4559,
 .CX 4269 4398,
 .CCX 4559 4398 4399,
 .CX 4269 4399,
 .CX 4269 4398,
 .CX 4269 4559,
 .CX 4270 4560,
 .CX 4270 4399,
 .CCX 4560 4399 4400,
 .CX 4270 4400,
 .CX 4270 4399,
 .CX 4270 4560,
 .CX 4271 4561,
 .CX 4271 4400,
 .CCX 4561 4400 4401,
 .CX 4271 4401,
 .CX 4271 4400,
 .CX 4271 4561,
 .CX 4272 4562,
 .CX 4272 4401,
 .CCX 4562 4401 4402,
 .CX 4272 4402,
 .CX 4272 4401,
 .CX 4272 4562,
 .CX 4273 4563,
 .CX 4273 4402,
 .CCX 4563 4402 4403,
 .CX 4273 4403,
 .CX 4273 4402,
 .CX 4273 4563,
 .CX 4274 4564,
 .CX 4274 4403,
 .CCX 4564 4403 4404,
 .CX 4274 4404,
 .CX 4274 4403,
 .CX 4274 4564,
 .CX 4275 4565,
 .CX 4275 4404,
 .CCX 4565 4404 4405,
 .CX 4275 4405,
 .CX 4275 4404,
 .CX 4275 4565,
 .CX 4276 4566,
 .CX 4276 4405,
 .CCX 4566 4405 4406,
 .CX 4276 4406,
 .CX 4276 4405,
 .CX 4276 4566,
 .CX 4277 4567,
 .CX 4277 4406,
 .CCX 4567 4406 4407,
 .CX 4277 4407,
 .CX 4277 4406,
 .CX 4277 4567,
 .CX 4278 4568,
 .CX 4278 4407,
 .CCX 4568 4407 4408,
 .CX 4278 4408,
 .CX 4278 4407,
 .CX 4278 4568,
 .CX 4279 4569,
 .CX 4279 4408,
 .CCX 4569 4408 4409,
 .CX 4279 4409,
 .CX 4279 4408,
 .CX 4279 4569,
 .CX 4280 4570,
 .CX 4280 4409,
 .CCX 4570 4409 4410,
 .CX 4280 4410,
 .CX 4280 4409,
 .CX 4280 4570,
 .CX 4281 4571,
 .CX 4281 4410,
 .CCX 4571 4410 4411,
 .CX 4281 4411,
 .CX 4281 4410,
 .CX 4281 4571,
 .CX 4282 4572,
 .CX 4282 4411,
 .CCX 4572 4411 4412,
 .CX 4282 4412,
 .CX 4282 4411,
 .CX 4282 4572,
 .CX 4283 4573,
 .CX 4283 4412,
 .CCX 4573 4412 4413,
 .CX 4283 4413,
 .CX 4283 4412,
 .CX 4283 4573,
 .CX 4284 4574,
 .CX 4284 4413,
 .CCX 4574 4413 4414,
 .CX 4284 4414,
 .CX 4284 4413,
 .CX 4284 4574,
 .CX 4285 4575,
 .CX 4285 4414,
 .CCX 4575 4414 4415,
 .CX 4285 4415]

def dataChunk2 : Program := [
 .CX 4285 4414,
 .CX 4285 4575,
 .CX 4286 4576,
 .CX 4286 4415,
 .CCX 4576 4415 4416,
 .CX 4286 4416,
 .CX 4286 4415,
 .CX 4286 4576,
 .CX 4287 4577,
 .CX 4287 4416,
 .CCX 4577 4416 4417,
 .CX 4287 4417,
 .CX 4287 4416,
 .CX 4287 4577,
 .CX 4288 4578,
 .CX 4288 4417,
 .CCX 4578 4417 4418,
 .CX 4288 4418,
 .CX 4288 4417,
 .CX 4288 4578,
 .CX 4289 4579,
 .CX 4289 4418,
 .CCX 4579 4418 4419,
 .CX 4289 4419,
 .CX 4289 4418,
 .CX 4289 4579,
 .CX 4290 4580,
 .CX 4290 4419,
 .CCX 4580 4419 4420,
 .CX 4290 4420,
 .CX 4290 4419,
 .CX 4290 4580,
 .CX 4291 4581,
 .CX 4291 4420,
 .CCX 4581 4420 4421,
 .CX 4291 4421,
 .CX 4291 4420,
 .CX 4291 4581,
 .CX 4292 4582,
 .CX 4292 4421,
 .CCX 4582 4421 4422,
 .CX 4292 4422,
 .CX 4292 4421,
 .CX 4292 4582,
 .CX 4293 4583,
 .CX 4293 4422,
 .CCX 4583 4422 4423,
 .CX 4293 4423,
 .CX 4293 4422,
 .CX 4293 4583,
 .CX 4294 4584,
 .CX 4294 4423,
 .CCX 4584 4423 4424,
 .CX 4294 4424,
 .CX 4294 4423,
 .CX 4294 4584,
 .CX 4295 4585,
 .CX 4295 4424,
 .CCX 4585 4424 4425,
 .CX 4295 4425,
 .CX 4295 4424,
 .CX 4295 4585,
 .CX 4296 4586,
 .CX 4296 4425,
 .CCX 4586 4425 4426,
 .CX 4296 4426,
 .CX 4296 4425,
 .CX 4296 4586,
 .CX 4297 4587,
 .CX 4297 4426,
 .CCX 4587 4426 4427,
 .CX 4297 4427,
 .CX 4297 4426,
 .CX 4297 4587,
 .CX 4298 4588,
 .CX 4298 4427,
 .CCX 4588 4427 4428,
 .CX 4298 4428,
 .CX 4298 4427,
 .CX 4298 4588,
 .CX 4299 4589,
 .CX 4299 4428,
 .CCX 4589 4428 4429,
 .CX 4299 4429,
 .CX 4299 4428,
 .CX 4299 4589,
 .CX 4300 4590,
 .CX 4300 4429,
 .CCX 4590 4429 4430,
 .CX 4300 4430,
 .CX 4300 4429,
 .CX 4300 4590,
 .CX 4301 4591,
 .CX 4301 4430,
 .CCX 4591 4430 4431,
 .CX 4301 4431,
 .CX 4301 4430,
 .CX 4301 4591,
 .CX 4302 4592,
 .CX 4302 4431,
 .CCX 4592 4431 4432,
 .CX 4302 4432,
 .CX 4302 4431,
 .CX 4302 4592,
 .CX 4303 4593,
 .CX 4303 4432,
 .CCX 4593 4432 4433,
 .CX 4303 4433,
 .CX 4303 4432,
 .CX 4303 4593,
 .CX 4304 4594,
 .CX 4304 4433,
 .CCX 4594 4433 4434,
 .CX 4304 4434,
 .CX 4304 4433,
 .CX 4304 4594,
 .CX 4305 4595,
 .CX 4305 4434,
 .CCX 4595 4434 4435,
 .CX 4305 4435,
 .CX 4305 4434,
 .CX 4305 4595,
 .CX 4306 4596,
 .CX 4306 4435,
 .CCX 4596 4435 4436,
 .CX 4306 4436,
 .CX 4306 4435,
 .CX 4306 4596]

def dataChunk3 : Program := [
 .CX 4307 4597,
 .CX 4307 4436,
 .CCX 4597 4436 4437,
 .CX 4307 4437,
 .CX 4307 4436,
 .CX 4307 4597,
 .CX 4308 4598,
 .CX 4308 4437,
 .CCX 4598 4437 4438,
 .CX 4308 4438,
 .CX 4308 4437,
 .CX 4308 4598,
 .CX 4309 4599,
 .CX 4309 4438,
 .CCX 4599 4438 4439,
 .CX 4309 4439,
 .CX 4309 4438,
 .CX 4309 4599,
 .CX 4310 4600,
 .CX 4310 4439,
 .CCX 4600 4439 4440,
 .CX 4310 4440,
 .CX 4310 4439,
 .CX 4310 4600,
 .CX 4311 4601,
 .CX 4311 4440,
 .CCX 4601 4440 4441,
 .CX 4311 4441,
 .CX 4311 4440,
 .CX 4311 4601,
 .CX 4312 4602,
 .CX 4312 4441,
 .CCX 4602 4441 4442,
 .CX 4312 4442,
 .CX 4312 4441,
 .CX 4312 4602,
 .CX 4313 4603,
 .CX 4313 4442,
 .CCX 4603 4442 4443,
 .CX 4313 4443,
 .CX 4313 4442,
 .CX 4313 4603,
 .CX 4314 4604,
 .CX 4314 4443,
 .CCX 4604 4443 4444,
 .CX 4314 4444,
 .CX 4314 4443,
 .CX 4314 4604,
 .CX 4315 4605,
 .CX 4315 4444,
 .CCX 4605 4444 4445,
 .CX 4315 4445,
 .CX 4315 4444,
 .CX 4315 4605,
 .CX 4316 4606,
 .CX 4316 4445,
 .CCX 4606 4445 4446,
 .CX 4316 4446,
 .CX 4316 4445,
 .CX 4316 4606,
 .CX 4317 4607,
 .CX 4317 4446,
 .CCX 4607 4446 4447,
 .CX 4317 4447,
 .CX 4317 4446,
 .CX 4317 4607,
 .CX 4318 4608,
 .CX 4318 4447,
 .CCX 4608 4447 4448,
 .CX 4318 4448,
 .CX 4318 4447,
 .CX 4318 4608,
 .CX 4319 4609,
 .CX 4319 4448,
 .CCX 4609 4448 4449,
 .CX 4319 4449,
 .CX 4319 4448,
 .CX 4319 4609,
 .CX 4320 4610,
 .CX 4320 4449,
 .CCX 4610 4449 4450,
 .CX 4320 4450,
 .CX 4320 4449,
 .CX 4320 4610,
 .CX 4321 4611,
 .CX 4321 4450,
 .CCX 4611 4450 4451,
 .CX 4321 4451,
 .CX 4321 4450,
 .CX 4321 4611,
 .CX 4322 4612,
 .CX 4322 4451,
 .CCX 4612 4451 4452,
 .CX 4322 4452,
 .CX 4322 4451,
 .CX 4322 4612,
 .CX 4323 4613,
 .CX 4323 4452,
 .CCX 4613 4452 4453,
 .CX 4323 4453,
 .CX 4323 4452,
 .CX 4323 4613,
 .CX 4324 4614,
 .CX 4324 4453,
 .CCX 4614 4453 4454,
 .CX 4324 4454,
 .CX 4324 4453,
 .CX 4324 4614,
 .CX 4325 4615,
 .CX 4325 4454,
 .CCX 4615 4454 4455,
 .CX 4325 4455,
 .CX 4325 4454,
 .CX 4325 4615,
 .CX 4326 4616,
 .CX 4326 4455,
 .CCX 4616 4455 4456,
 .CX 4326 4456,
 .CX 4326 4455,
 .CX 4326 4616,
 .CX 4327 4617,
 .CX 4327 4456,
 .CCX 4617 4456 4457,
 .CX 4327 4457,
 .CX 4327 4456,
 .CX 4327 4617,
 .CX 4328 4618,
 .CX 4328 4457]

def dataChunk4 : Program := [
 .CCX 4618 4457 4458,
 .CX 4328 4458,
 .CX 4328 4457,
 .CX 4328 4618,
 .CX 4329 4619,
 .CX 4329 4458,
 .CCX 4619 4458 4459,
 .CX 4329 4459,
 .CX 4329 4458,
 .CX 4329 4619,
 .CX 4330 4620,
 .CX 4330 4459,
 .CCX 4620 4459 4460,
 .CX 4330 4460,
 .CX 4330 4459,
 .CX 4330 4620,
 .CX 4331 4621,
 .CX 4331 4460,
 .CCX 4621 4460 4461,
 .CX 4331 4461,
 .CX 4331 4460,
 .CX 4331 4621,
 .CX 4332 4622,
 .CX 4332 4461,
 .CCX 4622 4461 4462,
 .CX 4332 4462,
 .CX 4332 4461,
 .CX 4332 4622,
 .CX 4333 4623,
 .CX 4333 4462,
 .CCX 4623 4462 4463,
 .CX 4333 4463,
 .CX 4333 4462,
 .CX 4333 4623,
 .CX 4334 4624,
 .CX 4334 4463,
 .CCX 4624 4463 4464,
 .CX 4334 4464,
 .CX 4334 4463,
 .CX 4334 4624,
 .CX 4335 4625,
 .CX 4335 4464,
 .CCX 4625 4464 4465,
 .CX 4335 4465,
 .CX 4335 4464,
 .CX 4335 4625,
 .CX 4336 4626,
 .CX 4336 4465,
 .CCX 4626 4465 4466,
 .CX 4336 4466,
 .CX 4336 4465,
 .CX 4336 4626,
 .CX 4337 4627,
 .CX 4337 4466,
 .CCX 4627 4466 4467,
 .CX 4337 4467,
 .CX 4337 4466,
 .CX 4337 4627,
 .CX 4338 4628,
 .CX 4338 4467,
 .CCX 4628 4467 4468,
 .CX 4338 4468,
 .CX 4338 4467,
 .CX 4338 4628,
 .CX 4339 4629,
 .CX 4339 4468,
 .CCX 4629 4468 4469,
 .CX 4339 4469,
 .CX 4339 4468,
 .CX 4339 4629,
 .CX 4340 4630,
 .CX 4340 4469,
 .CCX 4630 4469 4470,
 .CX 4340 4470,
 .CX 4340 4469,
 .CX 4340 4630,
 .CX 4341 4631,
 .CX 4341 4470,
 .CCX 4631 4470 4471,
 .CX 4341 4471,
 .CX 4341 4470,
 .CX 4341 4631,
 .CX 4342 4632,
 .CX 4342 4471,
 .CCX 4632 4471 4472,
 .CX 4342 4472,
 .CX 4342 4471,
 .CX 4342 4632,
 .CX 4343 4633,
 .CX 4343 4472,
 .CCX 4633 4472 4473,
 .CX 4343 4473,
 .CX 4343 4472,
 .CX 4343 4633,
 .CX 4344 4634,
 .CX 4344 4473,
 .CCX 4634 4473 4474,
 .CX 4344 4474,
 .CX 4344 4473,
 .CX 4344 4634,
 .CX 4345 4635,
 .CX 4345 4474,
 .CCX 4635 4474 4475,
 .CX 4345 4475,
 .CX 4345 4474,
 .CX 4345 4635,
 .CX 4346 4636,
 .CX 4346 4475,
 .CCX 4636 4475 4476,
 .CX 4346 4476,
 .CX 4346 4475,
 .CX 4346 4636,
 .CX 4347 4637,
 .CX 4347 4476,
 .CCX 4637 4476 4477,
 .CX 4347 4477,
 .CX 4347 4476,
 .CX 4347 4637,
 .CX 4348 4638,
 .CX 4348 4477,
 .CCX 4638 4477 4478,
 .CX 4348 4478,
 .CX 4348 4477,
 .CX 4348 4638,
 .CX 4349 4639,
 .CX 4349 4478,
 .CCX 4639 4478 4479,
 .CX 4349 4479]

def dataChunk5 : Program := [
 .CX 4349 4478,
 .CX 4349 4639,
 .CX 4350 4640,
 .CX 4350 4479,
 .CCX 4640 4479 4480,
 .CX 4350 4480,
 .CX 4350 4479,
 .CX 4350 4640,
 .CX 4351 4641,
 .CX 4351 4480,
 .CCX 4641 4480 4481,
 .CX 4351 4481,
 .CX 4351 4480,
 .CX 4351 4641,
 .CX 4352 4642,
 .CX 4352 4481,
 .CCX 4642 4481 4482,
 .CX 4352 4482,
 .CX 4352 4481,
 .CX 4352 4642,
 .CX 4353 4643,
 .CX 4353 4482,
 .CCX 4643 4482 4483,
 .CX 4353 4483,
 .CX 4353 4482,
 .CX 4353 4643,
 .CX 4354 4644,
 .CX 4354 4483,
 .CCX 4644 4483 4484,
 .CX 4354 4484,
 .CX 4354 4483,
 .CX 4354 4644,
 .CX 4355 4645,
 .CX 4355 4484,
 .CCX 4645 4484 4485,
 .CX 4355 4485,
 .CX 4355 4484,
 .CX 4355 4645,
 .CX 4356 4646,
 .CX 4356 4485,
 .CCX 4646 4485 4486,
 .CX 4356 4486,
 .CX 4356 4485,
 .CX 4356 4646,
 .CX 4357 4647,
 .CX 4357 4486,
 .CCX 4647 4486 4487,
 .CX 4357 4487,
 .CX 4357 4486,
 .CX 4357 4647,
 .CX 4358 4648,
 .CX 4358 4487,
 .CCX 4648 4487 4488,
 .CX 4358 4488,
 .CX 4358 4487,
 .CX 4358 4648,
 .CX 4359 4649,
 .CX 4359 4488,
 .CCX 4649 4488 4489,
 .CX 4359 4489,
 .CX 4359 4488,
 .CX 4359 4649,
 .CX 4360 4650,
 .CX 4360 4489,
 .CCX 4650 4489 4490,
 .CX 4360 4490,
 .CX 4360 4489,
 .CX 4360 4650,
 .CX 4361 4651,
 .CX 4361 4490,
 .CCX 4651 4490 4491,
 .CX 4361 4491,
 .CX 4361 4490,
 .CX 4361 4651,
 .CX 4362 4652,
 .CX 4362 4491,
 .CCX 4652 4491 4492,
 .CX 4362 4492,
 .CX 4362 4491,
 .CX 4362 4652,
 .CX 4363 4653,
 .CX 4363 4492,
 .CCX 4653 4492 4493,
 .CX 4363 4493,
 .CX 4363 4492,
 .CX 4363 4653,
 .CX 4364 4654,
 .CX 4364 4493,
 .CCX 4654 4493 4494,
 .CX 4364 4494,
 .CX 4364 4493,
 .CX 4364 4654,
 .CX 4365 4655,
 .CX 4365 4494,
 .CCX 4655 4494 4495,
 .CX 4365 4495,
 .CX 4365 4494,
 .CX 4365 4655,
 .CX 4366 4656,
 .CX 4366 4495,
 .CCX 4656 4495 4496,
 .CX 4366 4496,
 .CX 4366 4495,
 .CX 4366 4656,
 .CX 4367 4657,
 .CX 4367 4496,
 .CCX 4657 4496 4497,
 .CX 4367 4497,
 .CX 4367 4496,
 .CX 4367 4657,
 .CX 4368 4658,
 .CX 4368 4497,
 .CCX 4658 4497 4498,
 .CX 4368 4498,
 .CX 4368 4497,
 .CX 4368 4658,
 .CX 4369 4659,
 .CX 4369 4498,
 .CCX 4659 4498 4499,
 .CX 4369 4499,
 .CX 4369 4498,
 .CX 4369 4659,
 .CX 4370 4660,
 .CX 4370 4499,
 .CCX 4660 4499 4500,
 .CX 4370 4500,
 .CX 4370 4499,
 .CX 4370 4660]

def dataChunk6 : Program := [
 .CX 4796 4661,
 .CX 4500 4661,
 .measureX 4500 [] [.CZ 4370 4660, .CZ 4370 4499, .CZ 4660 4499],
 .CX 4370 4660,
 .CX 4499 4660,
 .measureX 4499 [] [.CZ 4369 4659, .CZ 4369 4498, .CZ 4659 4498],
 .CX 4369 4659,
 .CX 4498 4659,
 .measureX 4498 [] [.CZ 4368 4658, .CZ 4368 4497, .CZ 4658 4497],
 .CX 4368 4658,
 .CX 4497 4658,
 .measureX 4497 [] [.CZ 4367 4657, .CZ 4367 4496, .CZ 4657 4496],
 .CX 4367 4657,
 .CX 4496 4657,
 .measureX 4496 [] [.CZ 4366 4656, .CZ 4366 4495, .CZ 4656 4495],
 .CX 4366 4656,
 .CX 4495 4656,
 .measureX 4495 [] [.CZ 4365 4655, .CZ 4365 4494, .CZ 4655 4494],
 .CX 4365 4655,
 .CX 4494 4655,
 .measureX 4494 [] [.CZ 4364 4654, .CZ 4364 4493, .CZ 4654 4493],
 .CX 4364 4654,
 .CX 4493 4654,
 .measureX 4493 [] [.CZ 4363 4653, .CZ 4363 4492, .CZ 4653 4492],
 .CX 4363 4653,
 .CX 4492 4653,
 .measureX 4492 [] [.CZ 4362 4652, .CZ 4362 4491, .CZ 4652 4491],
 .CX 4362 4652,
 .CX 4491 4652,
 .measureX 4491 [] [.CZ 4361 4651, .CZ 4361 4490, .CZ 4651 4490],
 .CX 4361 4651,
 .CX 4490 4651,
 .measureX 4490 [] [.CZ 4360 4650, .CZ 4360 4489, .CZ 4650 4489],
 .CX 4360 4650,
 .CX 4489 4650,
 .measureX 4489 [] [.CZ 4359 4649, .CZ 4359 4488, .CZ 4649 4488],
 .CX 4359 4649,
 .CX 4488 4649,
 .measureX 4488 [] [.CZ 4358 4648, .CZ 4358 4487, .CZ 4648 4487],
 .CX 4358 4648,
 .CX 4487 4648,
 .measureX 4487 [] [.CZ 4357 4647, .CZ 4357 4486, .CZ 4647 4486],
 .CX 4357 4647,
 .CX 4486 4647,
 .measureX 4486 [] [.CZ 4356 4646, .CZ 4356 4485, .CZ 4646 4485],
 .CX 4356 4646,
 .CX 4485 4646,
 .measureX 4485 [] [.CZ 4355 4645, .CZ 4355 4484, .CZ 4645 4484],
 .CX 4355 4645,
 .CX 4484 4645,
 .measureX 4484 [] [.CZ 4354 4644, .CZ 4354 4483, .CZ 4644 4483],
 .CX 4354 4644,
 .CX 4483 4644,
 .measureX 4483 [] [.CZ 4353 4643, .CZ 4353 4482, .CZ 4643 4482],
 .CX 4353 4643,
 .CX 4482 4643,
 .measureX 4482 [] [.CZ 4352 4642, .CZ 4352 4481, .CZ 4642 4481],
 .CX 4352 4642,
 .CX 4481 4642,
 .measureX 4481 [] [.CZ 4351 4641, .CZ 4351 4480, .CZ 4641 4480],
 .CX 4351 4641,
 .CX 4480 4641,
 .measureX 4480 [] [.CZ 4350 4640, .CZ 4350 4479, .CZ 4640 4479],
 .CX 4350 4640,
 .CX 4479 4640,
 .measureX 4479 [] [.CZ 4349 4639, .CZ 4349 4478, .CZ 4639 4478],
 .CX 4349 4639,
 .CX 4478 4639,
 .measureX 4478 [] [.CZ 4348 4638, .CZ 4348 4477, .CZ 4638 4477],
 .CX 4348 4638,
 .CX 4477 4638,
 .measureX 4477 [] [.CZ 4347 4637, .CZ 4347 4476, .CZ 4637 4476],
 .CX 4347 4637,
 .CX 4476 4637,
 .measureX 4476 [] [.CZ 4346 4636, .CZ 4346 4475, .CZ 4636 4475],
 .CX 4346 4636,
 .CX 4475 4636,
 .measureX 4475 [] [.CZ 4345 4635, .CZ 4345 4474, .CZ 4635 4474],
 .CX 4345 4635,
 .CX 4474 4635,
 .measureX 4474 [] [.CZ 4344 4634, .CZ 4344 4473, .CZ 4634 4473],
 .CX 4344 4634,
 .CX 4473 4634,
 .measureX 4473 [] [.CZ 4343 4633, .CZ 4343 4472, .CZ 4633 4472],
 .CX 4343 4633,
 .CX 4472 4633,
 .measureX 4472 [] [.CZ 4342 4632, .CZ 4342 4471, .CZ 4632 4471],
 .CX 4342 4632,
 .CX 4471 4632,
 .measureX 4471 [] [.CZ 4341 4631, .CZ 4341 4470, .CZ 4631 4470],
 .CX 4341 4631,
 .CX 4470 4631,
 .measureX 4470 [] [.CZ 4340 4630, .CZ 4340 4469, .CZ 4630 4469],
 .CX 4340 4630,
 .CX 4469 4630,
 .measureX 4469 [] [.CZ 4339 4629, .CZ 4339 4468, .CZ 4629 4468],
 .CX 4339 4629,
 .CX 4468 4629,
 .measureX 4468 [] [.CZ 4338 4628, .CZ 4338 4467, .CZ 4628 4467],
 .CX 4338 4628,
 .CX 4467 4628,
 .measureX 4467 [] [.CZ 4337 4627, .CZ 4337 4466, .CZ 4627 4466],
 .CX 4337 4627,
 .CX 4466 4627,
 .measureX 4466 [] [.CZ 4336 4626, .CZ 4336 4465, .CZ 4626 4465],
 .CX 4336 4626,
 .CX 4465 4626,
 .measureX 4465 [] [.CZ 4335 4625, .CZ 4335 4464, .CZ 4625 4464],
 .CX 4335 4625,
 .CX 4464 4625,
 .measureX 4464 [] [.CZ 4334 4624, .CZ 4334 4463, .CZ 4624 4463],
 .CX 4334 4624,
 .CX 4463 4624,
 .measureX 4463 [] [.CZ 4333 4623, .CZ 4333 4462, .CZ 4623 4462],
 .CX 4333 4623,
 .CX 4462 4623,
 .measureX 4462 [] [.CZ 4332 4622, .CZ 4332 4461, .CZ 4622 4461],
 .CX 4332 4622,
 .CX 4461 4622,
 .measureX 4461 [] [.CZ 4331 4621, .CZ 4331 4460, .CZ 4621 4460],
 .CX 4331 4621,
 .CX 4460 4621,
 .measureX 4460 [] [.CZ 4330 4620, .CZ 4330 4459, .CZ 4620 4459],
 .CX 4330 4620,
 .CX 4459 4620,
 .measureX 4459 [] [.CZ 4329 4619, .CZ 4329 4458, .CZ 4619 4458],
 .CX 4329 4619,
 .CX 4458 4619]

def dataChunk7 : Program := [
 .measureX 4458 [] [.CZ 4328 4618, .CZ 4328 4457, .CZ 4618 4457],
 .CX 4328 4618,
 .CX 4457 4618,
 .measureX 4457 [] [.CZ 4327 4617, .CZ 4327 4456, .CZ 4617 4456],
 .CX 4327 4617,
 .CX 4456 4617,
 .measureX 4456 [] [.CZ 4326 4616, .CZ 4326 4455, .CZ 4616 4455],
 .CX 4326 4616,
 .CX 4455 4616,
 .measureX 4455 [] [.CZ 4325 4615, .CZ 4325 4454, .CZ 4615 4454],
 .CX 4325 4615,
 .CX 4454 4615,
 .measureX 4454 [] [.CZ 4324 4614, .CZ 4324 4453, .CZ 4614 4453],
 .CX 4324 4614,
 .CX 4453 4614,
 .measureX 4453 [] [.CZ 4323 4613, .CZ 4323 4452, .CZ 4613 4452],
 .CX 4323 4613,
 .CX 4452 4613,
 .measureX 4452 [] [.CZ 4322 4612, .CZ 4322 4451, .CZ 4612 4451],
 .CX 4322 4612,
 .CX 4451 4612,
 .measureX 4451 [] [.CZ 4321 4611, .CZ 4321 4450, .CZ 4611 4450],
 .CX 4321 4611,
 .CX 4450 4611,
 .measureX 4450 [] [.CZ 4320 4610, .CZ 4320 4449, .CZ 4610 4449],
 .CX 4320 4610,
 .CX 4449 4610,
 .measureX 4449 [] [.CZ 4319 4609, .CZ 4319 4448, .CZ 4609 4448],
 .CX 4319 4609,
 .CX 4448 4609,
 .measureX 4448 [] [.CZ 4318 4608, .CZ 4318 4447, .CZ 4608 4447],
 .CX 4318 4608,
 .CX 4447 4608,
 .measureX 4447 [] [.CZ 4317 4607, .CZ 4317 4446, .CZ 4607 4446],
 .CX 4317 4607,
 .CX 4446 4607,
 .measureX 4446 [] [.CZ 4316 4606, .CZ 4316 4445, .CZ 4606 4445],
 .CX 4316 4606,
 .CX 4445 4606,
 .measureX 4445 [] [.CZ 4315 4605, .CZ 4315 4444, .CZ 4605 4444],
 .CX 4315 4605,
 .CX 4444 4605,
 .measureX 4444 [] [.CZ 4314 4604, .CZ 4314 4443, .CZ 4604 4443],
 .CX 4314 4604,
 .CX 4443 4604,
 .measureX 4443 [] [.CZ 4313 4603, .CZ 4313 4442, .CZ 4603 4442],
 .CX 4313 4603,
 .CX 4442 4603,
 .measureX 4442 [] [.CZ 4312 4602, .CZ 4312 4441, .CZ 4602 4441],
 .CX 4312 4602,
 .CX 4441 4602,
 .measureX 4441 [] [.CZ 4311 4601, .CZ 4311 4440, .CZ 4601 4440],
 .CX 4311 4601,
 .CX 4440 4601,
 .measureX 4440 [] [.CZ 4310 4600, .CZ 4310 4439, .CZ 4600 4439],
 .CX 4310 4600,
 .CX 4439 4600,
 .measureX 4439 [] [.CZ 4309 4599, .CZ 4309 4438, .CZ 4599 4438],
 .CX 4309 4599,
 .CX 4438 4599,
 .measureX 4438 [] [.CZ 4308 4598, .CZ 4308 4437, .CZ 4598 4437],
 .CX 4308 4598,
 .CX 4437 4598,
 .measureX 4437 [] [.CZ 4307 4597, .CZ 4307 4436, .CZ 4597 4436],
 .CX 4307 4597,
 .CX 4436 4597,
 .measureX 4436 [] [.CZ 4306 4596, .CZ 4306 4435, .CZ 4596 4435],
 .CX 4306 4596,
 .CX 4435 4596,
 .measureX 4435 [] [.CZ 4305 4595, .CZ 4305 4434, .CZ 4595 4434],
 .CX 4305 4595,
 .CX 4434 4595,
 .measureX 4434 [] [.CZ 4304 4594, .CZ 4304 4433, .CZ 4594 4433],
 .CX 4304 4594,
 .CX 4433 4594,
 .measureX 4433 [] [.CZ 4303 4593, .CZ 4303 4432, .CZ 4593 4432],
 .CX 4303 4593,
 .CX 4432 4593,
 .measureX 4432 [] [.CZ 4302 4592, .CZ 4302 4431, .CZ 4592 4431],
 .CX 4302 4592,
 .CX 4431 4592,
 .measureX 4431 [] [.CZ 4301 4591, .CZ 4301 4430, .CZ 4591 4430],
 .CX 4301 4591,
 .CX 4430 4591,
 .measureX 4430 [] [.CZ 4300 4590, .CZ 4300 4429, .CZ 4590 4429],
 .CX 4300 4590,
 .CX 4429 4590,
 .measureX 4429 [] [.CZ 4299 4589, .CZ 4299 4428, .CZ 4589 4428],
 .CX 4299 4589,
 .CX 4428 4589,
 .measureX 4428 [] [.CZ 4298 4588, .CZ 4298 4427, .CZ 4588 4427],
 .CX 4298 4588,
 .CX 4427 4588,
 .measureX 4427 [] [.CZ 4297 4587, .CZ 4297 4426, .CZ 4587 4426],
 .CX 4297 4587,
 .CX 4426 4587,
 .measureX 4426 [] [.CZ 4296 4586, .CZ 4296 4425, .CZ 4586 4425],
 .CX 4296 4586,
 .CX 4425 4586,
 .measureX 4425 [] [.CZ 4295 4585, .CZ 4295 4424, .CZ 4585 4424],
 .CX 4295 4585,
 .CX 4424 4585,
 .measureX 4424 [] [.CZ 4294 4584, .CZ 4294 4423, .CZ 4584 4423],
 .CX 4294 4584,
 .CX 4423 4584,
 .measureX 4423 [] [.CZ 4293 4583, .CZ 4293 4422, .CZ 4583 4422],
 .CX 4293 4583,
 .CX 4422 4583,
 .measureX 4422 [] [.CZ 4292 4582, .CZ 4292 4421, .CZ 4582 4421],
 .CX 4292 4582,
 .CX 4421 4582,
 .measureX 4421 [] [.CZ 4291 4581, .CZ 4291 4420, .CZ 4581 4420],
 .CX 4291 4581,
 .CX 4420 4581,
 .measureX 4420 [] [.CZ 4290 4580, .CZ 4290 4419, .CZ 4580 4419],
 .CX 4290 4580,
 .CX 4419 4580,
 .measureX 4419 [] [.CZ 4289 4579, .CZ 4289 4418, .CZ 4579 4418],
 .CX 4289 4579,
 .CX 4418 4579,
 .measureX 4418 [] [.CZ 4288 4578, .CZ 4288 4417, .CZ 4578 4417],
 .CX 4288 4578,
 .CX 4417 4578,
 .measureX 4417 [] [.CZ 4287 4577, .CZ 4287 4416, .CZ 4577 4416],
 .CX 4287 4577,
 .CX 4416 4577,
 .measureX 4416 [] [.CZ 4286 4576, .CZ 4286 4415, .CZ 4576 4415],
 .CX 4286 4576]

def dataChunk8 : Program := [
 .CX 4415 4576,
 .measureX 4415 [] [.CZ 4285 4575, .CZ 4285 4414, .CZ 4575 4414],
 .CX 4285 4575,
 .CX 4414 4575,
 .measureX 4414 [] [.CZ 4284 4574, .CZ 4284 4413, .CZ 4574 4413],
 .CX 4284 4574,
 .CX 4413 4574,
 .measureX 4413 [] [.CZ 4283 4573, .CZ 4283 4412, .CZ 4573 4412],
 .CX 4283 4573,
 .CX 4412 4573,
 .measureX 4412 [] [.CZ 4282 4572, .CZ 4282 4411, .CZ 4572 4411],
 .CX 4282 4572,
 .CX 4411 4572,
 .measureX 4411 [] [.CZ 4281 4571, .CZ 4281 4410, .CZ 4571 4410],
 .CX 4281 4571,
 .CX 4410 4571,
 .measureX 4410 [] [.CZ 4280 4570, .CZ 4280 4409, .CZ 4570 4409],
 .CX 4280 4570,
 .CX 4409 4570,
 .measureX 4409 [] [.CZ 4279 4569, .CZ 4279 4408, .CZ 4569 4408],
 .CX 4279 4569,
 .CX 4408 4569,
 .measureX 4408 [] [.CZ 4278 4568, .CZ 4278 4407, .CZ 4568 4407],
 .CX 4278 4568,
 .CX 4407 4568,
 .measureX 4407 [] [.CZ 4277 4567, .CZ 4277 4406, .CZ 4567 4406],
 .CX 4277 4567,
 .CX 4406 4567,
 .measureX 4406 [] [.CZ 4276 4566, .CZ 4276 4405, .CZ 4566 4405],
 .CX 4276 4566,
 .CX 4405 4566,
 .measureX 4405 [] [.CZ 4275 4565, .CZ 4275 4404, .CZ 4565 4404],
 .CX 4275 4565,
 .CX 4404 4565,
 .measureX 4404 [] [.CZ 4274 4564, .CZ 4274 4403, .CZ 4564 4403],
 .CX 4274 4564,
 .CX 4403 4564,
 .measureX 4403 [] [.CZ 4273 4563, .CZ 4273 4402, .CZ 4563 4402],
 .CX 4273 4563,
 .CX 4402 4563,
 .measureX 4402 [] [.CZ 4272 4562, .CZ 4272 4401, .CZ 4562 4401],
 .CX 4272 4562,
 .CX 4401 4562,
 .measureX 4401 [] [.CZ 4271 4561, .CZ 4271 4400, .CZ 4561 4400],
 .CX 4271 4561,
 .CX 4400 4561,
 .measureX 4400 [] [.CZ 4270 4560, .CZ 4270 4399, .CZ 4560 4399],
 .CX 4270 4560,
 .CX 4399 4560,
 .measureX 4399 [] [.CZ 4269 4559, .CZ 4269 4398, .CZ 4559 4398],
 .CX 4269 4559,
 .CX 4398 4559,
 .measureX 4398 [] [.CZ 4268 4558, .CZ 4268 4397, .CZ 4558 4397],
 .CX 4268 4558,
 .CX 4397 4558,
 .measureX 4397 [] [.CZ 4267 4557, .CZ 4267 4396, .CZ 4557 4396],
 .CX 4267 4557,
 .CX 4396 4557,
 .measureX 4396 [] [.CZ 4266 4556, .CZ 4266 4395, .CZ 4556 4395],
 .CX 4266 4556,
 .CX 4395 4556,
 .measureX 4395 [] [.CZ 4265 4555, .CZ 4265 4394, .CZ 4555 4394],
 .CX 4265 4555,
 .CX 4394 4555,
 .measureX 4394 [] [.CZ 4264 4554, .CZ 4264 4393, .CZ 4554 4393],
 .CX 4264 4554,
 .CX 4393 4554,
 .measureX 4393 [] [.CZ 4263 4553, .CZ 4263 4392, .CZ 4553 4392],
 .CX 4263 4553,
 .CX 4392 4553,
 .measureX 4392 [] [.CZ 4262 4552, .CZ 4262 4391, .CZ 4552 4391],
 .CX 4262 4552,
 .CX 4391 4552,
 .measureX 4391 [] [.CZ 4261 4551, .CZ 4261 4390, .CZ 4551 4390],
 .CX 4261 4551,
 .CX 4390 4551,
 .measureX 4390 [] [.CZ 4260 4550, .CZ 4260 4389, .CZ 4550 4389],
 .CX 4260 4550,
 .CX 4389 4550,
 .measureX 4389 [] [.CZ 4259 4549, .CZ 4259 4388, .CZ 4549 4388],
 .CX 4259 4549,
 .CX 4388 4549,
 .measureX 4388 [] [.CZ 4258 4548, .CZ 4258 4387, .CZ 4548 4387],
 .CX 4258 4548,
 .CX 4387 4548,
 .measureX 4387 [] [.CZ 4257 4547, .CZ 4257 4386, .CZ 4547 4386],
 .CX 4257 4547,
 .CX 4386 4547,
 .measureX 4386 [] [.CZ 4256 4546, .CZ 4256 4385, .CZ 4546 4385],
 .CX 4256 4546,
 .CX 4385 4546,
 .measureX 4385 [] [.CZ 4255 4545, .CZ 4255 4384, .CZ 4545 4384],
 .CX 4255 4545,
 .CX 4384 4545,
 .measureX 4384 [] [.CZ 4254 4544, .CZ 4254 4383, .CZ 4544 4383],
 .CX 4254 4544,
 .CX 4383 4544,
 .measureX 4383 [] [.CZ 4253 4543, .CZ 4253 4382, .CZ 4543 4382],
 .CX 4253 4543,
 .CX 4382 4543,
 .measureX 4382 [] [.CZ 4252 4542, .CZ 4252 4381, .CZ 4542 4381],
 .CX 4252 4542,
 .CX 4381 4542,
 .measureX 4381 [] [.CZ 4251 4541, .CZ 4251 4380, .CZ 4541 4380],
 .CX 4251 4541,
 .CX 4380 4541,
 .measureX 4380 [] [.CZ 4250 4540, .CZ 4250 4379, .CZ 4540 4379],
 .CX 4250 4540,
 .CX 4379 4540,
 .measureX 4379 [] [.CZ 4249 4539, .CZ 4249 4378, .CZ 4539 4378],
 .CX 4249 4539,
 .CX 4378 4539,
 .measureX 4378 [] [.CZ 4248 4538, .CZ 4248 4377, .CZ 4538 4377],
 .CX 4248 4538,
 .CX 4377 4538,
 .measureX 4377 [] [.CZ 4247 4537, .CZ 4247 4376, .CZ 4537 4376],
 .CX 4247 4537,
 .CX 4376 4537,
 .measureX 4376 [] [.CZ 4246 4536, .CZ 4246 4375, .CZ 4536 4375],
 .CX 4246 4536,
 .CX 4375 4536,
 .measureX 4375 [] [.CZ 4245 4535, .CZ 4245 4374, .CZ 4535 4374],
 .CX 4245 4535,
 .CX 4374 4535,
 .measureX 4374 [] [.CZ 4244 4534, .CZ 4244 4373, .CZ 4534 4373],
 .CX 4244 4534,
 .CX 4373 4534,
 .measureX 4373 [] [.CZ 4243 4533, .CZ 4243 4760, .CZ 4533 4760]]

def dataChunk9 : Program := [
 .CX 4243 4533,
 .CX 4760 4533]

def postLiteral : Program := dataChunk0 ++ dataChunk1 ++ dataChunk2 ++ dataChunk3 ++ dataChunk4 ++ dataChunk5 ++ dataChunk6 ++ dataChunk7 ++ dataChunk8 ++ dataChunk9

theorem post_eq : actualPost = postLiteral := by decide +kernel

#print axioms post_eq
end B84PostLiteralResearch

end


-- Verified gate replacement helper: B84CachedBlockPieces
section
namespace B84CachedBlockResearch
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant B84WindowResearch B84ReplacementResearch B84ReplaceGenericResearch
open ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open B84PostLiteralResearch

def original : Program := actualPost ++ FullPadBData.p5
def headPart : Program := original.take 9124
def remainder : Program := original.drop 9125
def optimized : Program := headPart ++ (repair ++ remainder)

theorem original_gate : original[9124]? = some (.CCX 4660 4403 4404) := by
 unfold original
 rw [post_eq]
 decide +kernel

theorem original_shape : original = headPart ++ ([.CCX 4660 4403 4404] ++ remainder) :=
 old_shape_of_lookup original 9124 (.CCX 4660 4403 4404) original_gate

theorem piece0 : B84ReplaceGenericResearch.segment original 971 128 = windowChunk0 := by
 calc
  B84ReplaceGenericResearch.segment original 971 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 971 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 971 128) post_eq
  _ = windowChunk0 := by decide +kernel

theorem piece1 : B84ReplaceGenericResearch.segment original 1099 128 = windowChunk1 := by
 calc
  B84ReplaceGenericResearch.segment original 1099 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 1099 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 1099 128) post_eq
  _ = windowChunk1 := by decide +kernel

theorem piece2 : B84ReplaceGenericResearch.segment original 1227 128 = windowChunk2 := by
 calc
  B84ReplaceGenericResearch.segment original 1227 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 1227 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 1227 128) post_eq
  _ = windowChunk2 := by decide +kernel

theorem piece3 : B84ReplaceGenericResearch.segment original 1355 128 = windowChunk3 := by
 calc
  B84ReplaceGenericResearch.segment original 1355 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 1355 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 1355 128) post_eq
  _ = windowChunk3 := by decide +kernel

theorem piece4 : B84ReplaceGenericResearch.segment original 1483 128 = windowChunk4 := by
 calc
  B84ReplaceGenericResearch.segment original 1483 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 1483 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 1483 128) post_eq
  _ = windowChunk4 := by decide +kernel

theorem piece5 : B84ReplaceGenericResearch.segment original 1611 128 = windowChunk5 := by
 calc
  B84ReplaceGenericResearch.segment original 1611 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 1611 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 1611 128) post_eq
  _ = windowChunk5 := by decide +kernel

theorem piece6 : B84ReplaceGenericResearch.segment original 1739 128 = windowChunk6 := by
 calc
  B84ReplaceGenericResearch.segment original 1739 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 1739 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 1739 128) post_eq
  _ = windowChunk6 := by decide +kernel

theorem piece7 : B84ReplaceGenericResearch.segment original 1867 128 = windowChunk7 := by
 calc
  B84ReplaceGenericResearch.segment original 1867 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 1867 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 1867 128) post_eq
  _ = windowChunk7 := by decide +kernel

theorem piece8 : B84ReplaceGenericResearch.segment original 1995 128 = windowChunk8 := by
 calc
  B84ReplaceGenericResearch.segment original 1995 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 1995 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 1995 128) post_eq
  _ = windowChunk8 := by decide +kernel

theorem piece9 : B84ReplaceGenericResearch.segment original 2123 128 = windowChunk9 := by
 calc
  B84ReplaceGenericResearch.segment original 2123 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 2123 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 2123 128) post_eq
  _ = windowChunk9 := by decide +kernel

theorem piece10 : B84ReplaceGenericResearch.segment original 2251 128 = windowChunk10 := by
 calc
  B84ReplaceGenericResearch.segment original 2251 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 2251 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 2251 128) post_eq
  _ = windowChunk10 := by decide +kernel

theorem piece11 : B84ReplaceGenericResearch.segment original 2379 128 = windowChunk11 := by
 calc
  B84ReplaceGenericResearch.segment original 2379 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 2379 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 2379 128) post_eq
  _ = windowChunk11 := by decide +kernel

theorem piece12 : B84ReplaceGenericResearch.segment original 2507 128 = windowChunk12 := by
 calc
  B84ReplaceGenericResearch.segment original 2507 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 2507 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 2507 128) post_eq
  _ = windowChunk12 := by decide +kernel

theorem piece13 : B84ReplaceGenericResearch.segment original 2635 128 = windowChunk13 := by
 calc
  B84ReplaceGenericResearch.segment original 2635 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 2635 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 2635 128) post_eq
  _ = windowChunk13 := by decide +kernel

theorem piece14 : B84ReplaceGenericResearch.segment original 2763 128 = windowChunk14 := by
 calc
  B84ReplaceGenericResearch.segment original 2763 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 2763 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 2763 128) post_eq
  _ = windowChunk14 := by decide +kernel

theorem piece15 : B84ReplaceGenericResearch.segment original 2891 128 = windowChunk15 := by
 calc
  B84ReplaceGenericResearch.segment original 2891 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 2891 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 2891 128) post_eq
  _ = windowChunk15 := by decide +kernel

theorem piece16 : B84ReplaceGenericResearch.segment original 3019 128 = windowChunk16 := by
 calc
  B84ReplaceGenericResearch.segment original 3019 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 3019 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 3019 128) post_eq
  _ = windowChunk16 := by decide +kernel

theorem piece17 : B84ReplaceGenericResearch.segment original 3147 128 = windowChunk17 := by
 calc
  B84ReplaceGenericResearch.segment original 3147 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 3147 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 3147 128) post_eq
  _ = windowChunk17 := by decide +kernel

theorem piece18 : B84ReplaceGenericResearch.segment original 3275 128 = windowChunk18 := by
 calc
  B84ReplaceGenericResearch.segment original 3275 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 3275 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 3275 128) post_eq
  _ = windowChunk18 := by decide +kernel

theorem piece19 : B84ReplaceGenericResearch.segment original 3403 128 = windowChunk19 := by
 calc
  B84ReplaceGenericResearch.segment original 3403 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 3403 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 3403 128) post_eq
  _ = windowChunk19 := by decide +kernel

theorem piece20 : B84ReplaceGenericResearch.segment original 3531 128 = windowChunk20 := by
 calc
  B84ReplaceGenericResearch.segment original 3531 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 3531 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 3531 128) post_eq
  _ = windowChunk20 := by decide +kernel

theorem piece21 : B84ReplaceGenericResearch.segment original 3659 128 = windowChunk21 := by
 calc
  B84ReplaceGenericResearch.segment original 3659 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 3659 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 3659 128) post_eq
  _ = windowChunk21 := by decide +kernel

theorem piece22 : B84ReplaceGenericResearch.segment original 3787 128 = windowChunk22 := by
 calc
  B84ReplaceGenericResearch.segment original 3787 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 3787 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 3787 128) post_eq
  _ = windowChunk22 := by decide +kernel

theorem piece23 : B84ReplaceGenericResearch.segment original 3915 128 = windowChunk23 := by
 calc
  B84ReplaceGenericResearch.segment original 3915 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 3915 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 3915 128) post_eq
  _ = windowChunk23 := by decide +kernel

theorem piece24 : B84ReplaceGenericResearch.segment original 4043 128 = windowChunk24 := by
 calc
  B84ReplaceGenericResearch.segment original 4043 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 4043 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 4043 128) post_eq
  _ = windowChunk24 := by decide +kernel

theorem piece25 : B84ReplaceGenericResearch.segment original 4171 128 = windowChunk25 := by
 calc
  B84ReplaceGenericResearch.segment original 4171 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 4171 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 4171 128) post_eq
  _ = windowChunk25 := by decide +kernel

theorem piece26 : B84ReplaceGenericResearch.segment original 4299 128 = windowChunk26 := by
 calc
  B84ReplaceGenericResearch.segment original 4299 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 4299 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 4299 128) post_eq
  _ = windowChunk26 := by decide +kernel

theorem piece27 : B84ReplaceGenericResearch.segment original 4427 128 = windowChunk27 := by
 calc
  B84ReplaceGenericResearch.segment original 4427 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 4427 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 4427 128) post_eq
  _ = windowChunk27 := by decide +kernel

theorem piece28 : B84ReplaceGenericResearch.segment original 4555 128 = windowChunk28 := by
 calc
  B84ReplaceGenericResearch.segment original 4555 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 4555 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 4555 128) post_eq
  _ = windowChunk28 := by decide +kernel

theorem piece29 : B84ReplaceGenericResearch.segment original 4683 128 = windowChunk29 := by
 calc
  B84ReplaceGenericResearch.segment original 4683 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 4683 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 4683 128) post_eq
  _ = windowChunk29 := by decide +kernel

theorem piece30 : B84ReplaceGenericResearch.segment original 4811 128 = windowChunk30 := by
 calc
  B84ReplaceGenericResearch.segment original 4811 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 4811 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 4811 128) post_eq
  _ = windowChunk30 := by decide +kernel

theorem piece31 : B84ReplaceGenericResearch.segment original 4939 128 = windowChunk31 := by
 calc
  B84ReplaceGenericResearch.segment original 4939 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 4939 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 4939 128) post_eq
  _ = windowChunk31 := by decide +kernel

theorem piece32 : B84ReplaceGenericResearch.segment original 5067 128 = windowChunk32 := by
 calc
  B84ReplaceGenericResearch.segment original 5067 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 5067 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 5067 128) post_eq
  _ = windowChunk32 := by decide +kernel

theorem piece33 : B84ReplaceGenericResearch.segment original 5195 128 = windowChunk33 := by
 calc
  B84ReplaceGenericResearch.segment original 5195 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 5195 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 5195 128) post_eq
  _ = windowChunk33 := by decide +kernel

theorem piece34 : B84ReplaceGenericResearch.segment original 5323 128 = windowChunk34 := by
 calc
  B84ReplaceGenericResearch.segment original 5323 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 5323 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 5323 128) post_eq
  _ = windowChunk34 := by decide +kernel

theorem piece35 : B84ReplaceGenericResearch.segment original 5451 128 = windowChunk35 := by
 calc
  B84ReplaceGenericResearch.segment original 5451 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 5451 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 5451 128) post_eq
  _ = windowChunk35 := by decide +kernel

theorem piece36 : B84ReplaceGenericResearch.segment original 5579 128 = windowChunk36 := by
 calc
  B84ReplaceGenericResearch.segment original 5579 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 5579 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 5579 128) post_eq
  _ = windowChunk36 := by decide +kernel

theorem piece37 : B84ReplaceGenericResearch.segment original 5707 128 = windowChunk37 := by
 calc
  B84ReplaceGenericResearch.segment original 5707 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 5707 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 5707 128) post_eq
  _ = windowChunk37 := by decide +kernel

theorem piece38 : B84ReplaceGenericResearch.segment original 5835 128 = windowChunk38 := by
 calc
  B84ReplaceGenericResearch.segment original 5835 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 5835 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 5835 128) post_eq
  _ = windowChunk38 := by decide +kernel

theorem piece39 : B84ReplaceGenericResearch.segment original 5963 128 = windowChunk39 := by
 calc
  B84ReplaceGenericResearch.segment original 5963 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 5963 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 5963 128) post_eq
  _ = windowChunk39 := by decide +kernel

theorem piece40 : B84ReplaceGenericResearch.segment original 6091 128 = windowChunk40 := by
 calc
  B84ReplaceGenericResearch.segment original 6091 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 6091 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 6091 128) post_eq
  _ = windowChunk40 := by decide +kernel

theorem piece41 : B84ReplaceGenericResearch.segment original 6219 128 = windowChunk41 := by
 calc
  B84ReplaceGenericResearch.segment original 6219 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 6219 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 6219 128) post_eq
  _ = windowChunk41 := by decide +kernel

theorem piece42 : B84ReplaceGenericResearch.segment original 6347 128 = windowChunk42 := by
 calc
  B84ReplaceGenericResearch.segment original 6347 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 6347 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 6347 128) post_eq
  _ = windowChunk42 := by decide +kernel

theorem piece43 : B84ReplaceGenericResearch.segment original 6475 128 = windowChunk43 := by
 calc
  B84ReplaceGenericResearch.segment original 6475 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 6475 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 6475 128) post_eq
  _ = windowChunk43 := by decide +kernel

theorem piece44 : B84ReplaceGenericResearch.segment original 6603 128 = windowChunk44 := by
 calc
  B84ReplaceGenericResearch.segment original 6603 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 6603 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 6603 128) post_eq
  _ = windowChunk44 := by decide +kernel

theorem piece45 : B84ReplaceGenericResearch.segment original 6731 128 = windowChunk45 := by
 calc
  B84ReplaceGenericResearch.segment original 6731 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 6731 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 6731 128) post_eq
  _ = windowChunk45 := by decide +kernel

theorem piece46 : B84ReplaceGenericResearch.segment original 6859 128 = windowChunk46 := by
 calc
  B84ReplaceGenericResearch.segment original 6859 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 6859 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 6859 128) post_eq
  _ = windowChunk46 := by decide +kernel

theorem piece47 : B84ReplaceGenericResearch.segment original 6987 128 = windowChunk47 := by
 calc
  B84ReplaceGenericResearch.segment original 6987 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 6987 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 6987 128) post_eq
  _ = windowChunk47 := by decide +kernel

theorem piece48 : B84ReplaceGenericResearch.segment original 7115 128 = windowChunk48 := by
 calc
  B84ReplaceGenericResearch.segment original 7115 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 7115 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 7115 128) post_eq
  _ = windowChunk48 := by decide +kernel

theorem piece49 : B84ReplaceGenericResearch.segment original 7243 128 = windowChunk49 := by
 calc
  B84ReplaceGenericResearch.segment original 7243 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 7243 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 7243 128) post_eq
  _ = windowChunk49 := by decide +kernel

theorem piece50 : B84ReplaceGenericResearch.segment original 7371 128 = windowChunk50 := by
 calc
  B84ReplaceGenericResearch.segment original 7371 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 7371 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 7371 128) post_eq
  _ = windowChunk50 := by decide +kernel

theorem piece51 : B84ReplaceGenericResearch.segment original 7499 128 = windowChunk51 := by
 calc
  B84ReplaceGenericResearch.segment original 7499 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 7499 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 7499 128) post_eq
  _ = windowChunk51 := by decide +kernel

theorem piece52 : B84ReplaceGenericResearch.segment original 7627 128 = windowChunk52 := by
 calc
  B84ReplaceGenericResearch.segment original 7627 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 7627 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 7627 128) post_eq
  _ = windowChunk52 := by decide +kernel

theorem piece53 : B84ReplaceGenericResearch.segment original 7755 128 = windowChunk53 := by
 calc
  B84ReplaceGenericResearch.segment original 7755 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 7755 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 7755 128) post_eq
  _ = windowChunk53 := by decide +kernel

theorem piece54 : B84ReplaceGenericResearch.segment original 7883 128 = windowChunk54 := by
 calc
  B84ReplaceGenericResearch.segment original 7883 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 7883 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 7883 128) post_eq
  _ = windowChunk54 := by decide +kernel

theorem piece55 : B84ReplaceGenericResearch.segment original 8011 128 = windowChunk55 := by
 calc
  B84ReplaceGenericResearch.segment original 8011 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 8011 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 8011 128) post_eq
  _ = windowChunk55 := by decide +kernel

theorem piece56 : B84ReplaceGenericResearch.segment original 8139 128 = windowChunk56 := by
 calc
  B84ReplaceGenericResearch.segment original 8139 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 8139 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 8139 128) post_eq
  _ = windowChunk56 := by decide +kernel

theorem piece57 : B84ReplaceGenericResearch.segment original 8267 128 = windowChunk57 := by
 calc
  B84ReplaceGenericResearch.segment original 8267 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 8267 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 8267 128) post_eq
  _ = windowChunk57 := by decide +kernel

theorem piece58 : B84ReplaceGenericResearch.segment original 8395 128 = windowChunk58 := by
 calc
  B84ReplaceGenericResearch.segment original 8395 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 8395 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 8395 128) post_eq
  _ = windowChunk58 := by decide +kernel

theorem piece59 : B84ReplaceGenericResearch.segment original 8523 128 = windowChunk59 := by
 calc
  B84ReplaceGenericResearch.segment original 8523 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 8523 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 8523 128) post_eq
  _ = windowChunk59 := by decide +kernel

theorem piece60 : B84ReplaceGenericResearch.segment original 8651 128 = windowChunk60 := by
 calc
  B84ReplaceGenericResearch.segment original 8651 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 8651 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 8651 128) post_eq
  _ = windowChunk60 := by decide +kernel

theorem piece61 : B84ReplaceGenericResearch.segment original 8779 128 = windowChunk61 := by
 calc
  B84ReplaceGenericResearch.segment original 8779 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 8779 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 8779 128) post_eq
  _ = windowChunk61 := by decide +kernel

theorem piece62 : B84ReplaceGenericResearch.segment original 8907 128 = windowChunk62 := by
 calc
  B84ReplaceGenericResearch.segment original 8907 128 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 8907 128 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 8907 128) post_eq
  _ = windowChunk62 := by decide +kernel

theorem piece63 : B84ReplaceGenericResearch.segment original 9035 89 = windowChunk63 := by
 calc
  B84ReplaceGenericResearch.segment original 9035 89 = B84ReplaceGenericResearch.segment (postLiteral ++ FullPadBData.p5) 9035 89 :=
   congrArg (fun p => B84ReplaceGenericResearch.segment (p ++ FullPadBData.p5) 9035 89) post_eq
  _ = windowChunk63 := by decide +kernel

#print axioms piece63
end B84CachedBlockResearch

end


-- Verified gate replacement helper: B84CachedBlockJoins
section
namespace B84CachedBlockResearch
open ECDSAAdd B84WindowResearch B84ReplacementResearch B84ReplaceGenericResearch B84PostLiteralResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


attribute [local irreducible] B84ReplaceGenericResearch.segment

theorem join0 : B84ReplaceGenericResearch.segment original 971 256 = (windowChunk0 ++ windowChunk1) := by
 calc
  B84ReplaceGenericResearch.segment original 971 256 = B84ReplaceGenericResearch.segment original 971 128 ++ B84ReplaceGenericResearch.segment original (971+128) 128 := segment_split original 971 128 128
  _ = (windowChunk0 ++ windowChunk1) := by rw [piece0,piece1]

theorem join1 : B84ReplaceGenericResearch.segment original 1227 256 = (windowChunk2 ++ windowChunk3) := by
 calc
  B84ReplaceGenericResearch.segment original 1227 256 = B84ReplaceGenericResearch.segment original 1227 128 ++ B84ReplaceGenericResearch.segment original (1227+128) 128 := segment_split original 1227 128 128
  _ = (windowChunk2 ++ windowChunk3) := by rw [piece2,piece3]

theorem join2 : B84ReplaceGenericResearch.segment original 971 512 = ((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) := by
 calc
  B84ReplaceGenericResearch.segment original 971 512 = B84ReplaceGenericResearch.segment original 971 256 ++ B84ReplaceGenericResearch.segment original (971+256) 256 := segment_split original 971 256 256
  _ = ((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) := by rw [join0,join1]

theorem join3 : B84ReplaceGenericResearch.segment original 1483 256 = (windowChunk4 ++ windowChunk5) := by
 calc
  B84ReplaceGenericResearch.segment original 1483 256 = B84ReplaceGenericResearch.segment original 1483 128 ++ B84ReplaceGenericResearch.segment original (1483+128) 128 := segment_split original 1483 128 128
  _ = (windowChunk4 ++ windowChunk5) := by rw [piece4,piece5]

theorem join4 : B84ReplaceGenericResearch.segment original 1739 256 = (windowChunk6 ++ windowChunk7) := by
 calc
  B84ReplaceGenericResearch.segment original 1739 256 = B84ReplaceGenericResearch.segment original 1739 128 ++ B84ReplaceGenericResearch.segment original (1739+128) 128 := segment_split original 1739 128 128
  _ = (windowChunk6 ++ windowChunk7) := by rw [piece6,piece7]

theorem join5 : B84ReplaceGenericResearch.segment original 1483 512 = ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7)) := by
 calc
  B84ReplaceGenericResearch.segment original 1483 512 = B84ReplaceGenericResearch.segment original 1483 256 ++ B84ReplaceGenericResearch.segment original (1483+256) 256 := segment_split original 1483 256 256
  _ = ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7)) := by rw [join3,join4]

theorem join6 : B84ReplaceGenericResearch.segment original 971 1024 = (((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) ++ ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7))) := by
 calc
  B84ReplaceGenericResearch.segment original 971 1024 = B84ReplaceGenericResearch.segment original 971 512 ++ B84ReplaceGenericResearch.segment original (971+512) 512 := segment_split original 971 512 512
  _ = (((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) ++ ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7))) := by rw [join2,join5]

theorem join7 : B84ReplaceGenericResearch.segment original 1995 256 = (windowChunk8 ++ windowChunk9) := by
 calc
  B84ReplaceGenericResearch.segment original 1995 256 = B84ReplaceGenericResearch.segment original 1995 128 ++ B84ReplaceGenericResearch.segment original (1995+128) 128 := segment_split original 1995 128 128
  _ = (windowChunk8 ++ windowChunk9) := by rw [piece8,piece9]

theorem join8 : B84ReplaceGenericResearch.segment original 2251 256 = (windowChunk10 ++ windowChunk11) := by
 calc
  B84ReplaceGenericResearch.segment original 2251 256 = B84ReplaceGenericResearch.segment original 2251 128 ++ B84ReplaceGenericResearch.segment original (2251+128) 128 := segment_split original 2251 128 128
  _ = (windowChunk10 ++ windowChunk11) := by rw [piece10,piece11]

theorem join9 : B84ReplaceGenericResearch.segment original 1995 512 = ((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) := by
 calc
  B84ReplaceGenericResearch.segment original 1995 512 = B84ReplaceGenericResearch.segment original 1995 256 ++ B84ReplaceGenericResearch.segment original (1995+256) 256 := segment_split original 1995 256 256
  _ = ((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) := by rw [join7,join8]

theorem join10 : B84ReplaceGenericResearch.segment original 2507 256 = (windowChunk12 ++ windowChunk13) := by
 calc
  B84ReplaceGenericResearch.segment original 2507 256 = B84ReplaceGenericResearch.segment original 2507 128 ++ B84ReplaceGenericResearch.segment original (2507+128) 128 := segment_split original 2507 128 128
  _ = (windowChunk12 ++ windowChunk13) := by rw [piece12,piece13]

theorem join11 : B84ReplaceGenericResearch.segment original 2763 256 = (windowChunk14 ++ windowChunk15) := by
 calc
  B84ReplaceGenericResearch.segment original 2763 256 = B84ReplaceGenericResearch.segment original 2763 128 ++ B84ReplaceGenericResearch.segment original (2763+128) 128 := segment_split original 2763 128 128
  _ = (windowChunk14 ++ windowChunk15) := by rw [piece14,piece15]

theorem join12 : B84ReplaceGenericResearch.segment original 2507 512 = ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15)) := by
 calc
  B84ReplaceGenericResearch.segment original 2507 512 = B84ReplaceGenericResearch.segment original 2507 256 ++ B84ReplaceGenericResearch.segment original (2507+256) 256 := segment_split original 2507 256 256
  _ = ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15)) := by rw [join10,join11]

theorem join13 : B84ReplaceGenericResearch.segment original 1995 1024 = (((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) ++ ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15))) := by
 calc
  B84ReplaceGenericResearch.segment original 1995 1024 = B84ReplaceGenericResearch.segment original 1995 512 ++ B84ReplaceGenericResearch.segment original (1995+512) 512 := segment_split original 1995 512 512
  _ = (((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) ++ ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15))) := by rw [join9,join12]

theorem join14 : B84ReplaceGenericResearch.segment original 971 2048 = ((((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) ++ ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7))) ++ (((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) ++ ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15)))) := by
 calc
  B84ReplaceGenericResearch.segment original 971 2048 = B84ReplaceGenericResearch.segment original 971 1024 ++ B84ReplaceGenericResearch.segment original (971+1024) 1024 := segment_split original 971 1024 1024
  _ = ((((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) ++ ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7))) ++ (((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) ++ ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15)))) := by rw [join6,join13]

theorem join15 : B84ReplaceGenericResearch.segment original 3019 256 = (windowChunk16 ++ windowChunk17) := by
 calc
  B84ReplaceGenericResearch.segment original 3019 256 = B84ReplaceGenericResearch.segment original 3019 128 ++ B84ReplaceGenericResearch.segment original (3019+128) 128 := segment_split original 3019 128 128
  _ = (windowChunk16 ++ windowChunk17) := by rw [piece16,piece17]

theorem join16 : B84ReplaceGenericResearch.segment original 3275 256 = (windowChunk18 ++ windowChunk19) := by
 calc
  B84ReplaceGenericResearch.segment original 3275 256 = B84ReplaceGenericResearch.segment original 3275 128 ++ B84ReplaceGenericResearch.segment original (3275+128) 128 := segment_split original 3275 128 128
  _ = (windowChunk18 ++ windowChunk19) := by rw [piece18,piece19]

theorem join17 : B84ReplaceGenericResearch.segment original 3019 512 = ((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) := by
 calc
  B84ReplaceGenericResearch.segment original 3019 512 = B84ReplaceGenericResearch.segment original 3019 256 ++ B84ReplaceGenericResearch.segment original (3019+256) 256 := segment_split original 3019 256 256
  _ = ((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) := by rw [join15,join16]

theorem join18 : B84ReplaceGenericResearch.segment original 3531 256 = (windowChunk20 ++ windowChunk21) := by
 calc
  B84ReplaceGenericResearch.segment original 3531 256 = B84ReplaceGenericResearch.segment original 3531 128 ++ B84ReplaceGenericResearch.segment original (3531+128) 128 := segment_split original 3531 128 128
  _ = (windowChunk20 ++ windowChunk21) := by rw [piece20,piece21]

theorem join19 : B84ReplaceGenericResearch.segment original 3787 256 = (windowChunk22 ++ windowChunk23) := by
 calc
  B84ReplaceGenericResearch.segment original 3787 256 = B84ReplaceGenericResearch.segment original 3787 128 ++ B84ReplaceGenericResearch.segment original (3787+128) 128 := segment_split original 3787 128 128
  _ = (windowChunk22 ++ windowChunk23) := by rw [piece22,piece23]

theorem join20 : B84ReplaceGenericResearch.segment original 3531 512 = ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23)) := by
 calc
  B84ReplaceGenericResearch.segment original 3531 512 = B84ReplaceGenericResearch.segment original 3531 256 ++ B84ReplaceGenericResearch.segment original (3531+256) 256 := segment_split original 3531 256 256
  _ = ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23)) := by rw [join18,join19]

theorem join21 : B84ReplaceGenericResearch.segment original 3019 1024 = (((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) ++ ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23))) := by
 calc
  B84ReplaceGenericResearch.segment original 3019 1024 = B84ReplaceGenericResearch.segment original 3019 512 ++ B84ReplaceGenericResearch.segment original (3019+512) 512 := segment_split original 3019 512 512
  _ = (((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) ++ ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23))) := by rw [join17,join20]

theorem join22 : B84ReplaceGenericResearch.segment original 4043 256 = (windowChunk24 ++ windowChunk25) := by
 calc
  B84ReplaceGenericResearch.segment original 4043 256 = B84ReplaceGenericResearch.segment original 4043 128 ++ B84ReplaceGenericResearch.segment original (4043+128) 128 := segment_split original 4043 128 128
  _ = (windowChunk24 ++ windowChunk25) := by rw [piece24,piece25]

theorem join23 : B84ReplaceGenericResearch.segment original 4299 256 = (windowChunk26 ++ windowChunk27) := by
 calc
  B84ReplaceGenericResearch.segment original 4299 256 = B84ReplaceGenericResearch.segment original 4299 128 ++ B84ReplaceGenericResearch.segment original (4299+128) 128 := segment_split original 4299 128 128
  _ = (windowChunk26 ++ windowChunk27) := by rw [piece26,piece27]

theorem join24 : B84ReplaceGenericResearch.segment original 4043 512 = ((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) := by
 calc
  B84ReplaceGenericResearch.segment original 4043 512 = B84ReplaceGenericResearch.segment original 4043 256 ++ B84ReplaceGenericResearch.segment original (4043+256) 256 := segment_split original 4043 256 256
  _ = ((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) := by rw [join22,join23]

theorem join25 : B84ReplaceGenericResearch.segment original 4555 256 = (windowChunk28 ++ windowChunk29) := by
 calc
  B84ReplaceGenericResearch.segment original 4555 256 = B84ReplaceGenericResearch.segment original 4555 128 ++ B84ReplaceGenericResearch.segment original (4555+128) 128 := segment_split original 4555 128 128
  _ = (windowChunk28 ++ windowChunk29) := by rw [piece28,piece29]

theorem join26 : B84ReplaceGenericResearch.segment original 4811 256 = (windowChunk30 ++ windowChunk31) := by
 calc
  B84ReplaceGenericResearch.segment original 4811 256 = B84ReplaceGenericResearch.segment original 4811 128 ++ B84ReplaceGenericResearch.segment original (4811+128) 128 := segment_split original 4811 128 128
  _ = (windowChunk30 ++ windowChunk31) := by rw [piece30,piece31]

theorem join27 : B84ReplaceGenericResearch.segment original 4555 512 = ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31)) := by
 calc
  B84ReplaceGenericResearch.segment original 4555 512 = B84ReplaceGenericResearch.segment original 4555 256 ++ B84ReplaceGenericResearch.segment original (4555+256) 256 := segment_split original 4555 256 256
  _ = ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31)) := by rw [join25,join26]

theorem join28 : B84ReplaceGenericResearch.segment original 4043 1024 = (((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) ++ ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31))) := by
 calc
  B84ReplaceGenericResearch.segment original 4043 1024 = B84ReplaceGenericResearch.segment original 4043 512 ++ B84ReplaceGenericResearch.segment original (4043+512) 512 := segment_split original 4043 512 512
  _ = (((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) ++ ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31))) := by rw [join24,join27]

theorem join29 : B84ReplaceGenericResearch.segment original 3019 2048 = ((((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) ++ ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23))) ++ (((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) ++ ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31)))) := by
 calc
  B84ReplaceGenericResearch.segment original 3019 2048 = B84ReplaceGenericResearch.segment original 3019 1024 ++ B84ReplaceGenericResearch.segment original (3019+1024) 1024 := segment_split original 3019 1024 1024
  _ = ((((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) ++ ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23))) ++ (((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) ++ ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31)))) := by rw [join21,join28]

theorem join30 : B84ReplaceGenericResearch.segment original 971 4096 = (((((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) ++ ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7))) ++ (((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) ++ ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15)))) ++ ((((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) ++ ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23))) ++ (((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) ++ ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31))))) := by
 calc
  B84ReplaceGenericResearch.segment original 971 4096 = B84ReplaceGenericResearch.segment original 971 2048 ++ B84ReplaceGenericResearch.segment original (971+2048) 2048 := segment_split original 971 2048 2048
  _ = (((((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) ++ ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7))) ++ (((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) ++ ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15)))) ++ ((((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) ++ ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23))) ++ (((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) ++ ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31))))) := by rw [join14,join29]

theorem join31 : B84ReplaceGenericResearch.segment original 5067 256 = (windowChunk32 ++ windowChunk33) := by
 calc
  B84ReplaceGenericResearch.segment original 5067 256 = B84ReplaceGenericResearch.segment original 5067 128 ++ B84ReplaceGenericResearch.segment original (5067+128) 128 := segment_split original 5067 128 128
  _ = (windowChunk32 ++ windowChunk33) := by rw [piece32,piece33]

theorem join32 : B84ReplaceGenericResearch.segment original 5323 256 = (windowChunk34 ++ windowChunk35) := by
 calc
  B84ReplaceGenericResearch.segment original 5323 256 = B84ReplaceGenericResearch.segment original 5323 128 ++ B84ReplaceGenericResearch.segment original (5323+128) 128 := segment_split original 5323 128 128
  _ = (windowChunk34 ++ windowChunk35) := by rw [piece34,piece35]

theorem join33 : B84ReplaceGenericResearch.segment original 5067 512 = ((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) := by
 calc
  B84ReplaceGenericResearch.segment original 5067 512 = B84ReplaceGenericResearch.segment original 5067 256 ++ B84ReplaceGenericResearch.segment original (5067+256) 256 := segment_split original 5067 256 256
  _ = ((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) := by rw [join31,join32]

theorem join34 : B84ReplaceGenericResearch.segment original 5579 256 = (windowChunk36 ++ windowChunk37) := by
 calc
  B84ReplaceGenericResearch.segment original 5579 256 = B84ReplaceGenericResearch.segment original 5579 128 ++ B84ReplaceGenericResearch.segment original (5579+128) 128 := segment_split original 5579 128 128
  _ = (windowChunk36 ++ windowChunk37) := by rw [piece36,piece37]

theorem join35 : B84ReplaceGenericResearch.segment original 5835 256 = (windowChunk38 ++ windowChunk39) := by
 calc
  B84ReplaceGenericResearch.segment original 5835 256 = B84ReplaceGenericResearch.segment original 5835 128 ++ B84ReplaceGenericResearch.segment original (5835+128) 128 := segment_split original 5835 128 128
  _ = (windowChunk38 ++ windowChunk39) := by rw [piece38,piece39]

theorem join36 : B84ReplaceGenericResearch.segment original 5579 512 = ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39)) := by
 calc
  B84ReplaceGenericResearch.segment original 5579 512 = B84ReplaceGenericResearch.segment original 5579 256 ++ B84ReplaceGenericResearch.segment original (5579+256) 256 := segment_split original 5579 256 256
  _ = ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39)) := by rw [join34,join35]

theorem join37 : B84ReplaceGenericResearch.segment original 5067 1024 = (((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) ++ ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39))) := by
 calc
  B84ReplaceGenericResearch.segment original 5067 1024 = B84ReplaceGenericResearch.segment original 5067 512 ++ B84ReplaceGenericResearch.segment original (5067+512) 512 := segment_split original 5067 512 512
  _ = (((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) ++ ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39))) := by rw [join33,join36]

theorem join38 : B84ReplaceGenericResearch.segment original 6091 256 = (windowChunk40 ++ windowChunk41) := by
 calc
  B84ReplaceGenericResearch.segment original 6091 256 = B84ReplaceGenericResearch.segment original 6091 128 ++ B84ReplaceGenericResearch.segment original (6091+128) 128 := segment_split original 6091 128 128
  _ = (windowChunk40 ++ windowChunk41) := by rw [piece40,piece41]

theorem join39 : B84ReplaceGenericResearch.segment original 6347 256 = (windowChunk42 ++ windowChunk43) := by
 calc
  B84ReplaceGenericResearch.segment original 6347 256 = B84ReplaceGenericResearch.segment original 6347 128 ++ B84ReplaceGenericResearch.segment original (6347+128) 128 := segment_split original 6347 128 128
  _ = (windowChunk42 ++ windowChunk43) := by rw [piece42,piece43]

theorem join40 : B84ReplaceGenericResearch.segment original 6091 512 = ((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) := by
 calc
  B84ReplaceGenericResearch.segment original 6091 512 = B84ReplaceGenericResearch.segment original 6091 256 ++ B84ReplaceGenericResearch.segment original (6091+256) 256 := segment_split original 6091 256 256
  _ = ((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) := by rw [join38,join39]

theorem join41 : B84ReplaceGenericResearch.segment original 6603 256 = (windowChunk44 ++ windowChunk45) := by
 calc
  B84ReplaceGenericResearch.segment original 6603 256 = B84ReplaceGenericResearch.segment original 6603 128 ++ B84ReplaceGenericResearch.segment original (6603+128) 128 := segment_split original 6603 128 128
  _ = (windowChunk44 ++ windowChunk45) := by rw [piece44,piece45]

theorem join42 : B84ReplaceGenericResearch.segment original 6859 256 = (windowChunk46 ++ windowChunk47) := by
 calc
  B84ReplaceGenericResearch.segment original 6859 256 = B84ReplaceGenericResearch.segment original 6859 128 ++ B84ReplaceGenericResearch.segment original (6859+128) 128 := segment_split original 6859 128 128
  _ = (windowChunk46 ++ windowChunk47) := by rw [piece46,piece47]

theorem join43 : B84ReplaceGenericResearch.segment original 6603 512 = ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47)) := by
 calc
  B84ReplaceGenericResearch.segment original 6603 512 = B84ReplaceGenericResearch.segment original 6603 256 ++ B84ReplaceGenericResearch.segment original (6603+256) 256 := segment_split original 6603 256 256
  _ = ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47)) := by rw [join41,join42]

theorem join44 : B84ReplaceGenericResearch.segment original 6091 1024 = (((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) ++ ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47))) := by
 calc
  B84ReplaceGenericResearch.segment original 6091 1024 = B84ReplaceGenericResearch.segment original 6091 512 ++ B84ReplaceGenericResearch.segment original (6091+512) 512 := segment_split original 6091 512 512
  _ = (((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) ++ ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47))) := by rw [join40,join43]

theorem join45 : B84ReplaceGenericResearch.segment original 5067 2048 = ((((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) ++ ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39))) ++ (((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) ++ ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47)))) := by
 calc
  B84ReplaceGenericResearch.segment original 5067 2048 = B84ReplaceGenericResearch.segment original 5067 1024 ++ B84ReplaceGenericResearch.segment original (5067+1024) 1024 := segment_split original 5067 1024 1024
  _ = ((((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) ++ ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39))) ++ (((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) ++ ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47)))) := by rw [join37,join44]

theorem join46 : B84ReplaceGenericResearch.segment original 7115 256 = (windowChunk48 ++ windowChunk49) := by
 calc
  B84ReplaceGenericResearch.segment original 7115 256 = B84ReplaceGenericResearch.segment original 7115 128 ++ B84ReplaceGenericResearch.segment original (7115+128) 128 := segment_split original 7115 128 128
  _ = (windowChunk48 ++ windowChunk49) := by rw [piece48,piece49]

theorem join47 : B84ReplaceGenericResearch.segment original 7371 256 = (windowChunk50 ++ windowChunk51) := by
 calc
  B84ReplaceGenericResearch.segment original 7371 256 = B84ReplaceGenericResearch.segment original 7371 128 ++ B84ReplaceGenericResearch.segment original (7371+128) 128 := segment_split original 7371 128 128
  _ = (windowChunk50 ++ windowChunk51) := by rw [piece50,piece51]

theorem join48 : B84ReplaceGenericResearch.segment original 7115 512 = ((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) := by
 calc
  B84ReplaceGenericResearch.segment original 7115 512 = B84ReplaceGenericResearch.segment original 7115 256 ++ B84ReplaceGenericResearch.segment original (7115+256) 256 := segment_split original 7115 256 256
  _ = ((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) := by rw [join46,join47]

theorem join49 : B84ReplaceGenericResearch.segment original 7627 256 = (windowChunk52 ++ windowChunk53) := by
 calc
  B84ReplaceGenericResearch.segment original 7627 256 = B84ReplaceGenericResearch.segment original 7627 128 ++ B84ReplaceGenericResearch.segment original (7627+128) 128 := segment_split original 7627 128 128
  _ = (windowChunk52 ++ windowChunk53) := by rw [piece52,piece53]

theorem join50 : B84ReplaceGenericResearch.segment original 7883 256 = (windowChunk54 ++ windowChunk55) := by
 calc
  B84ReplaceGenericResearch.segment original 7883 256 = B84ReplaceGenericResearch.segment original 7883 128 ++ B84ReplaceGenericResearch.segment original (7883+128) 128 := segment_split original 7883 128 128
  _ = (windowChunk54 ++ windowChunk55) := by rw [piece54,piece55]

theorem join51 : B84ReplaceGenericResearch.segment original 7627 512 = ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55)) := by
 calc
  B84ReplaceGenericResearch.segment original 7627 512 = B84ReplaceGenericResearch.segment original 7627 256 ++ B84ReplaceGenericResearch.segment original (7627+256) 256 := segment_split original 7627 256 256
  _ = ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55)) := by rw [join49,join50]

theorem join52 : B84ReplaceGenericResearch.segment original 7115 1024 = (((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) ++ ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55))) := by
 calc
  B84ReplaceGenericResearch.segment original 7115 1024 = B84ReplaceGenericResearch.segment original 7115 512 ++ B84ReplaceGenericResearch.segment original (7115+512) 512 := segment_split original 7115 512 512
  _ = (((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) ++ ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55))) := by rw [join48,join51]

theorem join53 : B84ReplaceGenericResearch.segment original 8139 256 = (windowChunk56 ++ windowChunk57) := by
 calc
  B84ReplaceGenericResearch.segment original 8139 256 = B84ReplaceGenericResearch.segment original 8139 128 ++ B84ReplaceGenericResearch.segment original (8139+128) 128 := segment_split original 8139 128 128
  _ = (windowChunk56 ++ windowChunk57) := by rw [piece56,piece57]

theorem join54 : B84ReplaceGenericResearch.segment original 8395 256 = (windowChunk58 ++ windowChunk59) := by
 calc
  B84ReplaceGenericResearch.segment original 8395 256 = B84ReplaceGenericResearch.segment original 8395 128 ++ B84ReplaceGenericResearch.segment original (8395+128) 128 := segment_split original 8395 128 128
  _ = (windowChunk58 ++ windowChunk59) := by rw [piece58,piece59]

theorem join55 : B84ReplaceGenericResearch.segment original 8139 512 = ((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) := by
 calc
  B84ReplaceGenericResearch.segment original 8139 512 = B84ReplaceGenericResearch.segment original 8139 256 ++ B84ReplaceGenericResearch.segment original (8139+256) 256 := segment_split original 8139 256 256
  _ = ((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) := by rw [join53,join54]

theorem join56 : B84ReplaceGenericResearch.segment original 8651 256 = (windowChunk60 ++ windowChunk61) := by
 calc
  B84ReplaceGenericResearch.segment original 8651 256 = B84ReplaceGenericResearch.segment original 8651 128 ++ B84ReplaceGenericResearch.segment original (8651+128) 128 := segment_split original 8651 128 128
  _ = (windowChunk60 ++ windowChunk61) := by rw [piece60,piece61]

theorem join57 : B84ReplaceGenericResearch.segment original 8907 217 = (windowChunk62 ++ windowChunk63) := by
 calc
  B84ReplaceGenericResearch.segment original 8907 217 = B84ReplaceGenericResearch.segment original 8907 128 ++ B84ReplaceGenericResearch.segment original (8907+128) 89 := segment_split original 8907 128 89
  _ = (windowChunk62 ++ windowChunk63) := by rw [piece62,piece63]

theorem join58 : B84ReplaceGenericResearch.segment original 8651 473 = ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63)) := by
 calc
  B84ReplaceGenericResearch.segment original 8651 473 = B84ReplaceGenericResearch.segment original 8651 256 ++ B84ReplaceGenericResearch.segment original (8651+256) 217 := segment_split original 8651 256 217
  _ = ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63)) := by rw [join56,join57]

theorem join59 : B84ReplaceGenericResearch.segment original 8139 985 = (((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) ++ ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63))) := by
 calc
  B84ReplaceGenericResearch.segment original 8139 985 = B84ReplaceGenericResearch.segment original 8139 512 ++ B84ReplaceGenericResearch.segment original (8139+512) 473 := segment_split original 8139 512 473
  _ = (((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) ++ ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63))) := by rw [join55,join58]

theorem join60 : B84ReplaceGenericResearch.segment original 7115 2009 = ((((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) ++ ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55))) ++ (((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) ++ ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63)))) := by
 calc
  B84ReplaceGenericResearch.segment original 7115 2009 = B84ReplaceGenericResearch.segment original 7115 1024 ++ B84ReplaceGenericResearch.segment original (7115+1024) 985 := segment_split original 7115 1024 985
  _ = ((((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) ++ ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55))) ++ (((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) ++ ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63)))) := by rw [join52,join59]

theorem join61 : B84ReplaceGenericResearch.segment original 5067 4057 = (((((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) ++ ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39))) ++ (((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) ++ ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47)))) ++ ((((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) ++ ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55))) ++ (((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) ++ ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63))))) := by
 calc
  B84ReplaceGenericResearch.segment original 5067 4057 = B84ReplaceGenericResearch.segment original 5067 2048 ++ B84ReplaceGenericResearch.segment original (5067+2048) 2009 := segment_split original 5067 2048 2009
  _ = (((((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) ++ ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39))) ++ (((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) ++ ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47)))) ++ ((((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) ++ ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55))) ++ (((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) ++ ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63))))) := by rw [join45,join60]

theorem join62 : B84ReplaceGenericResearch.segment original 971 8153 = ((((((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) ++ ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7))) ++ (((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) ++ ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15)))) ++ ((((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) ++ ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23))) ++ (((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) ++ ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31))))) ++ (((((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) ++ ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39))) ++ (((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) ++ ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47)))) ++ ((((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) ++ ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55))) ++ (((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) ++ ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63)))))) := by
 calc
  B84ReplaceGenericResearch.segment original 971 8153 = B84ReplaceGenericResearch.segment original 971 4096 ++ B84ReplaceGenericResearch.segment original (971+4096) 4057 := segment_split original 971 4096 4057
  _ = ((((((windowChunk0 ++ windowChunk1) ++ (windowChunk2 ++ windowChunk3)) ++ ((windowChunk4 ++ windowChunk5) ++ (windowChunk6 ++ windowChunk7))) ++ (((windowChunk8 ++ windowChunk9) ++ (windowChunk10 ++ windowChunk11)) ++ ((windowChunk12 ++ windowChunk13) ++ (windowChunk14 ++ windowChunk15)))) ++ ((((windowChunk16 ++ windowChunk17) ++ (windowChunk18 ++ windowChunk19)) ++ ((windowChunk20 ++ windowChunk21) ++ (windowChunk22 ++ windowChunk23))) ++ (((windowChunk24 ++ windowChunk25) ++ (windowChunk26 ++ windowChunk27)) ++ ((windowChunk28 ++ windowChunk29) ++ (windowChunk30 ++ windowChunk31))))) ++ (((((windowChunk32 ++ windowChunk33) ++ (windowChunk34 ++ windowChunk35)) ++ ((windowChunk36 ++ windowChunk37) ++ (windowChunk38 ++ windowChunk39))) ++ (((windowChunk40 ++ windowChunk41) ++ (windowChunk42 ++ windowChunk43)) ++ ((windowChunk44 ++ windowChunk45) ++ (windowChunk46 ++ windowChunk47)))) ++ ((((windowChunk48 ++ windowChunk49) ++ (windowChunk50 ++ windowChunk51)) ++ ((windowChunk52 ++ windowChunk53) ++ (windowChunk54 ++ windowChunk55))) ++ (((windowChunk56 ++ windowChunk57) ++ (windowChunk58 ++ windowChunk59)) ++ ((windowChunk60 ++ windowChunk61) ++ (windowChunk62 ++ windowChunk63)))))) := by rw [join30,join61]

theorem segment_eq_window : B84ReplaceGenericResearch.segment original 971 8153 = window := join62


#print axioms segment_eq_window
end B84CachedBlockResearch

end


-- Verified gate replacement helper: B84CachedBlockReplacement
section
namespace B84CachedBlockResearch
open ECDSAAdd B84WindowResearch B84ReplacementResearch B84ReplaceGenericResearch B84PostLiteralResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false


theorem headPart_eq : headPart = original.take 9124 := rfl
attribute [local irreducible] B84CachedBlockResearch.original B84CachedBlockResearch.headPart

theorem prefix_stripped : headPart.map stripPhase =
 (original.take 971).map stripPhase ++ window := by
 have h0 : headPart.map stripPhase = (original.take (971+8153)).map stripPhase :=
  congrArg (List.map stripPhase) headPart_eq
 have h1 := B84WindowCompositionResearch.take_map_segment original 971 8153
 have h2 := congrArg (fun p => (original.take 971).map stripPhase ++ p) segment_eq_window
 exact h0.trans (h1.trans h2)

theorem prefix_condition (s : State) (m : List Bool) : query (run headPart m s).basis = false :=
 B84WindowCompositionResearch.condition_of_stripped headPart
  ((original.take 971).map stripPhase) prefix_stripped s m

theorem run_eq (s : State) (m : List Bool) : run original m s = run optimized m s := by
 calc
  run original m s = run (headPart ++ ([.CCX 4660 4403 4404] ++ remainder)) m s :=
   congrArg (fun p => run p m s) original_shape
  _ = run (headPart ++ (repair ++ remainder)) m s := after_prefix headPart remainder prefix_condition s m
  _ = run optimized m s := rfl

#print axioms run_eq
end B84CachedBlockResearch

end


-- Verified gate replacement helper: B84RepairSupport
section
namespace B84RepairSupportResearch
open ECDSAAdd ECDSAAdd.Arithmetic B84PostLiteralResearch B84ReplacementResearch B84SupportResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

theorem contains_4339 : 4339 ∈ wires actualPost := by
 rw [post_eq]
 have h : postLiteral[576]? = some (.CX 4339 4629) := by decide +kernel
 exact instruction_wires_subset (List.mem_of_getElem? h) (by simp [Instr.wires])

theorem contains_4370 : 4370 ∈ wires actualPost := by
 rw [post_eq]
 have h : postLiteral[762]? = some (.CX 4370 4660) := by decide +kernel
 exact instruction_wires_subset (List.mem_of_getElem? h) (by simp [Instr.wires])

theorem contains_4629 : 4629 ∈ wires actualPost := by
 rw [post_eq]
 have h : postLiteral[576]? = some (.CX 4339 4629) := by decide +kernel
 exact instruction_wires_subset (List.mem_of_getElem? h) (by simp [Instr.wires])

theorem contains_4661 : 4661 ∈ wires actualPost := by
 rw [post_eq]
 have h : postLiteral[768]? = some (.CX 4796 4661) := by decide +kernel
 exact instruction_wires_subset (List.mem_of_getElem? h) (by simp [Instr.wires])

theorem contains_4760 : 4760 ∈ wires actualPost := by
 rw [post_eq]
 have h : postLiteral[1]? = some (.CX 4243 4760) := by decide +kernel
 exact instruction_wires_subset (List.mem_of_getElem? h) (by simp [Instr.wires])

theorem contains_4404 : 4404 ∈ wires actualPost := by
 rw [post_eq]
 have h : postLiteral[188]? = some (.CCX 4564 4403 4404) := by decide +kernel
 exact instruction_wires_subset (List.mem_of_getElem? h) (by simp [Instr.wires])

theorem repair_wires : wires repair = {4339,4370,4629,4661,4760,4404} := by decide +kernel

theorem repair_subset : wires repair ⊆ wires actualPost := by
 rw [repair_wires]
 intro w hw
 simp only [Finset.mem_insert,Finset.mem_singleton] at hw
 rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
 · exact contains_4339
 · exact contains_4370
 · exact contains_4629
 · exact contains_4661
 · exact contains_4760
 · exact contains_4404

theorem repair_physical : GatePhysical repair :=
 physicalGateCheck_correct repair (by decide +kernel)

#print axioms repair_subset
#print axioms repair_physical
end B84RepairSupportResearch

end


-- Verified gate replacement helper: B84CertifiedBlockResources
section
namespace B84CertifiedBlockResearch
open ECDSAAdd ECDSAAdd.Challenge B84CachedBlockResearch B84ContextResearch
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.Entrant.InverseCarryDevelop.buildPost

theorem original_post_eq : original = B84PostLiteralResearch.actualPost ++ FullPadBData.p5 := rfl
attribute [local irreducible] B84CachedBlockResearch.original B84CachedBlockResearch.headPart
 B84CachedBlockResearch.remainder B84PostLiteralResearch.actualPost

theorem block_toffoli : toffoliCount optimized + 1 = toffoliCount original := by
 change toffoliCount (headPart ++ (B84ReplacementResearch.repair ++ remainder)) + 1 = toffoliCount original
 exact (B84ResourceResearch.one_less_toffoli headPart remainder).trans
  (congrArg toffoliCount original_shape.symm)

theorem block_measurements : measurementCount original = measurementCount optimized := by
 calc
  measurementCount original = measurementCount (headPart ++ ([.CCX 4660 4403 4404] ++ remainder)) :=
   congrArg measurementCount original_shape
  _ = measurementCount optimized := (B84ResourceResearch.same_measurements headPart remainder).symm

theorem block_slots : gateSlots optimized = gateSlots original + 4 := by
 change gateSlots (headPart ++ (B84ReplacementResearch.repair ++ remainder)) = gateSlots original + 4
 exact (B84ResourceResearch.four_more_slots headPart remainder).trans
  (congrArg (fun p=>gateSlots p+4) original_shape.symm)


theorem block_support : wires optimized ⊆ wires original := by
 have hp : wires B84ReplacementResearch.repair ⊆
   wires B84PostLiteralResearch.actualPost ∪ wires FullPadBData.p5 :=
  B84RepairSupportResearch.repair_subset.trans Finset.subset_union_left
 have he : wires original = wires B84PostLiteralResearch.actualPost ∪ wires FullPadBData.p5 :=
  (congrArg wires original_post_eq).trans (wires_append _ _)
 have hr : wires B84ReplacementResearch.repair ⊆ wires original :=
  Eq.mp (congrArg (fun ws=>wires B84ReplacementResearch.repair ⊆ ws) he.symm) hp
 have hr' : wires B84ReplacementResearch.repair ⊆
   wires (headPart ++ ([.CCX 4660 4403 4404] ++ remainder)) :=
  Eq.mp (congrArg (fun p => wires B84ReplacementResearch.repair ⊆ wires p) original_shape) hr
 calc
  wires optimized ⊆ wires (headPart ++ ([.CCX 4660 4403 4404] ++ remainder)) :=
   B84SupportResearch.replacement_support headPart _ _ remainder hr'
  _ = wires original := congrArg wires original_shape.symm

theorem block_physical (hp : ECDSAAdd.Arithmetic.GatePhysical original) :
 ECDSAAdd.Arithmetic.GatePhysical optimized := by
 have h := Eq.mp (congrArg ECDSAAdd.Arithmetic.GatePhysical original_shape) hp
 exact B84SupportResearch.replacement_physical headPart _ _ remainder h
  B84RepairSupportResearch.repair_physical

#print axioms block_toffoli
#print axioms block_support
end B84CertifiedBlockResearch

end
