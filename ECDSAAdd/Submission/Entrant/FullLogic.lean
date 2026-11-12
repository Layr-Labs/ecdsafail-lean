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
