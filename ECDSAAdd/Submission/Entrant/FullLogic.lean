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

-- Narrow accumulator and carry protocols.
open ECDSAAdd

-- Component Numeric
section
namespace ECDSAAdd.Entrant.A161Facts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def K161 : Nat := 2^161-1

theorem accumulator_bound (H : Nat) (hH:H<2^128) :
 4294968272*H<2^161 := by
 norm_num at hH ⊢
 omega

theorem complement_delta : OwnDiagAll12Square.cFlipK-K161=3*2^161 := by
 norm_num [OwnDiagAll12Square.cFlipK,K161]

def acc161 (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 161

def aMiddle161 (L : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
 maskedConstant g (acc161 L) K161++
 (qprogTq L.measuredCore SquareReduction.p++maskedConstant g (acc161 L) K161)

def loans95 (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 FullASelectedDevelop.loans L++(L.core.work.drop 161).take 2

theorem high_work_zero (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths)
 (s : BasisState) (V : Nat) (hV:regValue L.core.work s=V) (hbound:V<2^161)
 (i : Nat) (hi : 161 ≤ i) (hlen : i < 256) : s (L.core.work.getD i 0)=false := by
 rw [RawClearCarryProbe.register_bit _ i s (by simpa [hw.core.work] using hlen),hV]
 have hb:V<2^i := lt_of_lt_of_le hbound (Nat.pow_le_pow_right (by decide) hi)
 simp [Nat.div_eq_of_lt hb]

theorem flip161_run (r : List Wire) (hlen:r.length=161) (hn:r.Nodup)
 (g : Wire) (hg:g∉r) (s : State) (m : List Bool) :
 (run (maskedConstant g r K161) m s).phase=s.phase ∧
 (∀q,q∉r → (run (maskedConstant g r K161) m s).basis q=s.basis q) ∧
 regValue r (run (maskedConstant g r K161) m s).basis=
 (if s.basis g then K161-regValue r s.basis else regValue r s.basis) := by
 rw [maskedConstant_run g r K161 hg]
 cases hs:s.basis g
 · simp
 · have e:K161=2^r.length-1 := by rw [hlen];rfl
   simp only [if_true]
   rw [e,OwnDiagAll12Square.xorConstant_ones,notRegister_correct r hn]
   refine ⟨rfl,?_,?_⟩
   · intro q hq;simp [hq]
   · change regValue r (fun w => if w∈r then !s.basis w else s.basis w)=_
     rw [regValue_congr r _ (fun w => !s.basis w) (by intro w hw;simp [hw]),regValue_complement]

theorem actual_loans95 : (loans95 FullPadSupport.L).length=95 ∧ (loans95 FullPadSupport.L).Nodup := by
 decide +kernel

def trimHighMasks (P : Program) : Program :=
 P.filter (fun i => decide (i≠.CX 4113 4662 ∧ i≠.CX 4113 4663))

def p161 : Program := trimHighMasks ParkAData.p0

set_option maxRecDepth 100000
set_option maxHeartbeats 500000000


#print axioms high_work_zero
#print axioms flip161_run
#print axioms actual_loans95
end ECDSAAdd.Entrant.A161Facts

end

-- Component NarrowAcc
section
-- Adapted from the retained NarrowAcc proof in QTop: outer accumulator width161.
-- This is scratch proof development, not an entrant replacement.
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.A161NarrowAcc
open Arithmetic

/-! Narrow H accumulator for a source of at most 128 bits.

`earlyHTerms src` accumulates `(2^32+976)*H` with `H < 2^128`. The generic early prefix runs its two
signed steps on 141 accumulator bits and the final `2^32` step on all 161 bits, which is sized for
130-bit sources. For a 128-bit source `1040*H < 2^139` and `(2^32+976)*H < 2^161`, so the same
operations run on 139 and 161 bits: the top two carries of each of the three adders are never produced
(two Toffolis and two measurements less per adder). -/

def pre8 (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)++
    Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src false 10)++
    CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)

def build8 (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  pre8 acc Z bank cin src++Acc.op (acc.take 161) Z bank cin 161 false (Acc.earlyTerm src false 32)

def unbuild8 (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  CodexNarrowSub.accSub (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)++
    Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)++
    CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)++
    Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)

theorem terms_mem (src : List Wire) :
    Acc.earlyTerm src false 4∈earlyHTerms src ∧ Acc.earlyTerm src false 10∈earlyHTerms src ∧
      Acc.earlyTerm src true 6∈earlyHTerms src ∧ Acc.earlyTerm src false 32∈earlyHTerms src := by
  simp [earlyHTerms]

theorem build8_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base 0) (build8 acc Z bank cin src)
      (SquareFrame acc base (4294968272*regValue src base)) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have hf10 := hf _ tm.2.1
  have hf6 := hf _ tm.2.2.1
  have hf32 := hf _ tm.2.2.2
  let H := regValue src base
  have hH : H<2^128 := lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
  have seed := Acc.seed_triple acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4 base hz
    0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
  have add : Triple (SquareFrame acc base (16*H))
      (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src false 10))
      (SquareFrame acc base (1040*H)) := by
    have h := Acc.op_prefix_triple acc Z bank cin 161 139 (Acc.earlyTerm src false 10) hacc
      (by norm_num [Acc.earlyTerm]) hf10 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (16*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : Acc.step base false (16*H) (Acc.earlyTerm src false 10)=1040*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have sub : Triple (SquareFrame acc base (1040*H))
      (CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6))
      (SquareFrame acc base (976*H)) := by
    have h := CodexNarrowSub.accSub_prefix_triple acc Z bank cin 161 139 (Acc.earlyTerm src true 6) hacc
      (by norm_num [Acc.earlyTerm]) hf6 (by simp only [Acc.earlyTerm]; omega) (by norm_num [Acc.earlyTerm]) base hz hb hi (1040*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (CodexNarrowSub.build_sub6_range H hH).2.2)
    have value : Acc.step base true (1040*H) (Acc.earlyTerm src true 6)=976*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have top : Triple (SquareFrame acc base (976*H))
      (Acc.op (acc.take 161) Z bank cin 161 false (Acc.earlyTerm src false 32))
      (SquareFrame acc base (4294968272*H)) := by
    have h := Acc.op_prefix_triple acc Z bank cin 161 161 (Acc.earlyTerm src false 32) hacc
      (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (976*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : Acc.step base false (976*H) (Acc.earlyTerm src false 32)=4294968272*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  exact ((seed.seq add).seq sub).seq top

                                                                               
                                                   
                                                           
                                                                            
                           
                                                                                              
                                    
                          
                       
                          
                           
                            
                            
                                                                                                      
                                                         
                                                                                        
                                          
                                                                                                          
                                                                              
                                                                
                                                                               
                                                                                       
                                                                                           
                                                                             
                                                
            
           
                   
           
                                                  
                                                                             
                                           
                                                                                         
                                                                                                         
                                                                                            
                                                                                    
                                       
               
           
                   
           
                                                   
                                                                                        
                                         
                                                                                                          
                                                                              
                                                          
                                                                               
                                                                                       
                                                                                    
                                       
               
           
                   
           
                                                                                              
                                                              
                                        

theorem narrowLen (Z bank : List Wire) (n : Nat) (f : MeasuredSquareFold)
    (hf : Acc.FitsLen Z bank 161 f) (hn : n≤161) (hl : f.src.length+f.shift<n) :
    Acc.FitsLen Z bank n f := by
  refine ⟨hl,?_,?_⟩
  · have h := hf.zpad; omega
  · have h := hf.bankLen; omega

theorem build8_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.FitsLen Z bank 161 f) :
    (toffoliCount (build8 acc Z bank cin src)=387 ∧ measurementCount (build8 acc Z bank cin src)=388) ∧
    (toffoliCount (unbuild8 acc Z bank cin src)=386 ∧
      measurementCount (unbuild8 acc Z bank cin src)=388) := by
  have tm := terms_mem src
  have l139 : (acc.take 139).length=139 := by simp [List.length_take,hacc]
  have l161 : (acc.take 161).length=161 := by simp [List.length_take,hacc]
  have seed := Acc.seed_counts acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc (hf _ tm.1)
  have f10 := narrowLen Z bank 139 _ (hf _ tm.2.1) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have f6 := narrowLen Z bank 139 _ (hf _ tm.2.2.1) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have f32 := narrowLen Z bank 161 _ (hf _ tm.2.2.2) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have a0 := Acc.op_counts (acc.take 139) Z bank cin 139 false _ l139 f10
  have a1 := Acc.op_counts (acc.take 139) Z bank cin 139 true _ l139 f10
  have b0 := Acc.op_counts (acc.take 139) Z bank cin 139 false _ l139 f6
  have b1 := Acc.op_counts (acc.take 139) Z bank cin 139 true _ l139 f6
  have c0 := Acc.op_counts (acc.take 161) Z bank cin 161 false _ l161 f32
  have c1 := Acc.op_counts (acc.take 161) Z bank cin 161 true _ l161 f32
  have bk := CodexNarrowSub.accSub_counts (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6) l139 f6 (by norm_num [Acc.earlyTerm])
  rw [b1.1,b1.2] at bk
  have ak := CodexNarrowSub.accSub_counts (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10) l139 f10 (by norm_num [Acc.earlyTerm])
  have ck := CodexNarrowSub.accSub_counts (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32) l161 f32 (by norm_num [Acc.earlyTerm])
  rw [a1.1,a1.2] at ak
  rw [c1.1,c1.2] at ck
  simp only [build8,unbuild8,pre8,toffoliCount_append,measurementCount_append,
    seed.1,seed.2,a0.1,a0.2,a1.1,a1.2,b0.1,b0.2,b1.1,b1.2,c0.1,c0.2,c1.1,c1.2]
  norm_num [Acc.earlyTerm] at bk ak ck ⊢
  omega

theorem build8_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f) :
    wires (build8 acc Z bank cin src)⊆(cin::(src++acc++Z++bank)).toFinset ∧
    wires (unbuild8 acc Z bank cin src)⊆(cin::(src++acc++Z++bank)).toFinset := by
  have tm := terms_mem src
  have seed := Acc.seed_support acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc (hf _ tm.1)
  have a0 := Acc.op_prefix_support acc Z bank cin 161 139 (Acc.earlyTerm src false 10) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have a1 := Acc.op_prefix_support acc Z bank cin 161 139 (Acc.earlyTerm src false 10) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have b0 := Acc.op_prefix_support acc Z bank cin 161 139 (Acc.earlyTerm src true 6) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have b1 := Acc.op_prefix_support acc Z bank cin 161 139 (Acc.earlyTerm src true 6) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have c0 := Acc.op_prefix_support acc Z bank cin 161 161 (Acc.earlyTerm src false 32) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) false
  have c1 := Acc.op_prefix_support acc Z bank cin 161 161 (Acc.earlyTerm src false 32) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) true
  have fit6 := Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src true 6) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega)
  have bk := CodexNarrowSub.accSub_support (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)
    (by simp [List.length_take,hacc]) fit6.toFitsLen (by norm_num [Acc.earlyTerm])
  have b1 := bk.trans b1
  have fit10 := Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src false 10) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega)
  have new10 := CodexNarrowSub.accSub_support (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)
    (by simp [List.length_take,hacc]) fit10.toFitsLen (by norm_num [Acc.earlyTerm])
  have a1 := new10.trans a1
  have fit32 := Acc.fits_prefix acc Z bank cin 161 161 (Acc.earlyTerm src false 32) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega)
  have new32 := CodexNarrowSub.accSub_support (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)
    (by simp [List.length_take,hacc]) fit32.toFitsLen (by norm_num [Acc.earlyTerm])
  have c1 := new32.trans c1
  simp only [Acc.earlyTerm] at seed a0 a1 b0 b1 c0 c1
  simp only [build8,unbuild8,pre8,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨seed,a0⟩,b1⟩,c0⟩,⟨⟨⟨c1,b0⟩,a1⟩,seed⟩⟩

theorem build8_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f) :
    GatePhysical (build8 acc Z bank cin src) ∧ GatePhysical (unbuild8 acc Z bank cin src) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have seed : GatePhysical (Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)) := by
    have len := Acc.fits_lengths acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4.toFitsLen
    have nd := Acc.fits_nodup acc Z bank cin 161 (Acc.earlyTerm src false 4) hf4
    exact copyRegister_physical none _ _
      ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
  have a0 := Acc.op_prefix_physical acc Z bank cin 161 139 (Acc.earlyTerm src false 10)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have a1 := Acc.op_prefix_physical acc Z bank cin 161 139 (Acc.earlyTerm src false 10)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have b0 := Acc.op_prefix_physical acc Z bank cin 161 139 (Acc.earlyTerm src true 6)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have b1 := Acc.op_prefix_physical acc Z bank cin 161 139 (Acc.earlyTerm src true 6)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have c0 := Acc.op_prefix_physical acc Z bank cin 161 161 (Acc.earlyTerm src false 32)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) false
  have c1 := Acc.op_prefix_physical acc Z bank cin 161 161 (Acc.earlyTerm src false 32)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) true
  have fit6 := Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src true 6) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega)
  have b1 := CodexNarrowSub.accSub_physical (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)
    (by simp [List.length_take,hacc]) fit6 (by norm_num [Acc.earlyTerm])
  have fit10 := Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src false 10) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega)
  have new10 := CodexNarrowSub.accSub_physical (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)
    (by simp [List.length_take,hacc]) fit10 (by norm_num [Acc.earlyTerm])
  have a1 := new10
  have fit32 := Acc.fits_prefix acc Z bank cin 161 161 (Acc.earlyTerm src false 32) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega)
  have new32 := CodexNarrowSub.accSub_physical (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)
    (by simp [List.length_take,hacc]) fit32 (by norm_num [Acc.earlyTerm])
  have c1 := new32
  simp only [build8,unbuild8,pre8,gatePhysical_append]
  exact ⟨⟨⟨⟨seed,a0⟩,b1⟩,c0⟩,⟨⟨⟨c1,b0⟩,a1⟩,seed⟩⟩

                                                                                
                                                   
                                                        
                                                                
                                                                      
                          
                       
                                                                                              
                                                                                      
                                                                                    
                                                               
                                                        
                       
                            
                                                                                          
                                                  
                                                                             
                                                                              
                                                              
                                                                                               
                       
                            
                                                                                                             
                                                                                                            
                                                                                                               
                                                                                                              
                                                                                                               
                                                                                                              
                                                                                                                         
                                                                                                 
                                                                        
                        
                                                                                                                        
                                                                                                      
                                                                         
                           
                                                                                                                          
                                                                                                      
                                                                         
                           
                                                             
       

end ECDSAAdd.Entrant.A161NarrowAcc
#print axioms ECDSAAdd.Entrant.A161NarrowAcc.build8_triple
#print axioms ECDSAAdd.Entrant.A161NarrowAcc.build8_physical

end

-- Component SourceUnbuild
section
-- Width161 specializations of the retained QTop SourceTail/SourceAddFour proofs.
-- Existing bit/arithmetic protocols are reused, not claimed as newly invented.
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.A161SourceTail
open SourceTailDevelop
open Arithmetic

def tail (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  program src Z ((acc.take 139).drop 10) (bank.take 128) cin

theorem tail_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 161 (Acc.earlyTerm src false 10))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (1040*regValue src base)) (tail acc Z bank cin src)
      (SquareFrame acc base (16*regValue src base)) := by
  let f:=Acc.earlyTerm src false 10
  let H:=regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have old:=Acc.op_prefix_triple acc Z bank cin 161 139 f hacc (by decide) hf
    (by simp [f,Acc.earlyTerm,hsrc]) base hz hb hi true (1040*H)
    (by omega) (by simp only [f,Acc.earlyTerm];dsimp [H];omega)
  have value : Acc.step base true (1040*H) f=16*H := by
    norm_num [Acc.step,f,Acc.earlyTerm]
    dsimp [H]
    omega
  rw [value] at old
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf (by simp [f,Acc.earlyTerm,hsrc])
  have len : (acc.take 139).length=139 := by simp [hacc]
  have rawEq : Acc.op (acc.take 139) Z bank cin 139 true f=
      subInPlace (src++Z.take 1) ((acc.take 139).drop 10) (bank.take 128) cin := by
    simp [Acc.op,Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc]
  intro s m hs
  have away (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h:=List.nodup_iff_count.mp hf.nd q
    have a:=List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b:=List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
      omega
  have same (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) s.basis (by omega) hs.1 (by omega)
  have sy : regValue ((acc.take 139).drop 10) s.basis=1040*H/1024 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
    rfl
  have sh : regValue src s.basis=H := regValue_congr src _ base (fun q hq=>same q (Or.inl (by simp [hq])))
  have sz (q : Wire) (hq : q∈Z) : s.basis q=false :=
    (same q (Or.inl (by simp [hq]))).trans (hz q hq)
  have sb (q : Wire) (hq : q∈bank.take 128) : s.basis q=false :=
    (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
  have si : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd' : (cin::((src++Z.take 1)++(acc.take 139).drop 10++bank.take 128)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd
  have zl : 1≤Z.length := by
    have h:=fit.zpad
    simpa [f,Acc.earlyTerm,hsrc] using h
  have bl : (bank.take 128).length=128 := by
    have h:=fit.bankLen
    simp only [f,Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have e:=run_eq_sub src Z ((acc.take 139).drop 10) (bank.take 128) cin hsrc zl
    (by simp [len]) bl nd' s m sz sb si H hH sh sy
  change run (tail acc Z bank cin src) m s=_ at e
  rw [e,←rawEq]
  exact old s m hs
#print axioms tail_triple
end ECDSAAdd.Entrant.A161SourceTail


namespace ECDSAAdd.Entrant.A161SourceAdd
open SourceAddFourDevelop
open Arithmetic

def add (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  program src Z ((acc.take 139).drop 6) (bank.take 132) cin

theorem add_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 161 (Acc.earlyTerm src true 6))
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (976*regValue src base)) (add acc Z bank cin src)
      (SquareFrame acc base (1040*regValue src base)) := by
  let f:=Acc.earlyTerm src true 6
  let H:=regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have old:=Acc.op_prefix_triple acc Z bank cin 161 139 f hacc (by decide) hf
    (by simp [f,Acc.earlyTerm,hsrc]) base hz hb hi false (976*H)
    (by omega) (by simp only [f,Acc.earlyTerm];dsimp [H];omega)
  have value : Acc.step base false (976*H) f=1040*H := by
    norm_num [Acc.step,f,Acc.earlyTerm]
    dsimp [H]
    omega
  rw [value] at old
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf (by simp [f,Acc.earlyTerm,hsrc])
  have len : (acc.take 139).length=139 := by simp [hacc]
  have rawEq : Acc.op (acc.take 139) Z bank cin 139 false f=
      addInPlace (src++Z.take 5) ((acc.take 139).drop 6) (bank.take 132) cin := by
    simp [Acc.op,Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc]
  intro s m hs
  have away (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : q∉acc := by
    intro bad
    have h:=List.nodup_iff_count.mp hf.nd q
    have a:=List.count_pos_iff.mpr bad
    rcases hq with hq|rfl
    · have b:=List.count_pos_iff.mpr hq
      simp only [List.count_cons,List.count_append,Acc.earlyTerm] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true,Acc.earlyTerm] at h
      omega
  have same (q : Wire) (hq : q∈src++Z++bank ∨ q=cin) : s.basis q=base q := hs.2 q (away q hq)
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) s.basis (by omega) hs.1 (by omega)
  have sy : regValue ((acc.take 139).drop 6) s.basis=976*H/64 := by
    rw [CuccaroStreamedSquareWideLayout.regValue_drop_div _ _ (by rw [len];decide),pref.1]
    rfl
  have sh : regValue src s.basis=H := regValue_congr src _ base (fun q hq=>same q (Or.inl (by simp [hq])))
  have sz (q : Wire) (hq : q∈Z) : s.basis q=false :=
    (same q (Or.inl (by simp [hq]))).trans (hz q hq)
  have sb (q : Wire) (hq : q∈bank.take 132) : s.basis q=false :=
    (same q (Or.inl (by simp [List.mem_of_mem_take hq]))).trans (hb q (List.mem_of_mem_take hq))
  have si : s.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd' : (cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd
  have zl : 5≤Z.length := by
    have h:=fit.zpad
    simpa [f,Acc.earlyTerm,hsrc] using h
  have bl : (bank.take 132).length=132 := by
    have h:=fit.bankLen
    simp only [f,Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have e:=run_eq_add src Z ((acc.take 139).drop 6) (bank.take 132) cin (by omega) zl
    (by simp [len,hsrc]) (by simp [bl,len]) nd' s m sz sb si H sh sy
  change run (add acc Z bank cin src) m s=_ at e
  rw [e,←rawEq]
  exact old s m hs
#print axioms add_triple
end ECDSAAdd.Entrant.A161SourceAdd


namespace ECDSAAdd.Entrant.A161SourceAdd
open SourceAddFourDevelop
open Arithmetic CodexNarrowTail SourceTailDevelop

def unbuild (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)++
    add acc Z bank cin src++
    A161SourceTail.tail acc Z bank cin src++Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)

theorem unbuild_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuild acc Z bank cin src)
      (SquareFrame acc base 0) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have hf10 := hf _ tm.2.1
  have hf6 := hf _ tm.2.2.1
  have hf32 := hf _ tm.2.2.2
  let H := regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have top : Triple (SquareFrame acc base (4294968272*H))
      (CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32))
      (SquareFrame acc base (976*H)) := by
    have h := CodexKnownOnesTail.accSub_prefix_triple acc Z bank cin 161 161 106 (Acc.earlyTerm src false 32) hacc
      (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega)
      (by norm_num [Acc.earlyTerm]) base hz hb hi (4294968272*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (clear_sub32_range H hH).2.2)
    have value : Acc.step base true (4294968272*H) (Acc.earlyTerm src false 32)=976*H := by
      have e : regValue src base*2^32=4294967296*H := by dsimp only [H]; ring
      simp only [Acc.step,Acc.earlyTerm,if_true]
      rw [e]
      omega
    rw [value] at h
    exact h
  have ad := add_triple acc Z bank cin src hacc hsrc hf6 base hz hb hi
  change Triple (SquareFrame acc base (976*H)) (add acc Z bank cin src)
    (SquareFrame acc base (1040*H)) at ad
  have sub : Triple (SquareFrame acc base (1040*H)) (A161SourceTail.tail acc Z bank cin src)
      (SquareFrame acc base (16*H)) := A161SourceTail.tail_triple acc Z bank cin src hacc hsrc hf10 base hz hb hi
  have seed := Acc.seed_triple acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4 base hz
    (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
  exact ((top.seq ad).seq sub).seq seed


                                                                              
                                                   
                                                           
                                                                                          
                                                                                          
                                                                                                    
                                                                                                     
                                                                                   
                                                                                                          
                                
                            
          
                     
                                                                                            
                                              
#print axioms unbuild_triple
                            
end ECDSAAdd.Entrant.A161SourceAdd

end

-- Component Carry
section
-- Retained generic carry protocols adapted to a161-bit accumulator interface.
-- The bit-level cached/consumed carry primitives are inherited unchanged.
namespace ECDSAAdd.Entrant.A161Carry
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop
 ThirdSavedCarryDevelop FourthASavedCarryDevelop ManyACarryDevelop ControlLoan1589BFFold ZeroReadDevelop CodexNarrowTail
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires
-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: buildPre
def buildPre (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)++
    Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src false 10)

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: buildPost
def buildPost (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  Acc.op (acc.take 161) Z bank cin 161 false (Acc.earlyTerm src false 32)

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: buildCached
def buildCached (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire) : Program :=
  buildPre acc Z bank cin src++
    cachedSub (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6))
      (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q++buildPost acc Z bank cin src

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: build_split
theorem build_split (acc Z bank : List Wire) (cin : Wire) (src : List Wire) :
    A161NarrowAcc.build8 acc Z bank cin src=buildPre acc Z bank cin src++
      CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)++buildPost acc Z bank cin src := rfl

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: buildPre_triple
theorem buildPre_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc:acc.length=161) (hsrc:src.length≤128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (base : BasisState) (hz:∀q∈Z,base q=false) (hb:∀q∈bank,base q=false) (hi:base cin=false) :
    Triple (SquareFrame acc base 0) (buildPre acc Z bank cin src)
      (SquareFrame acc base (1040*regValue src base)) := by
  have tm := A161NarrowAcc.terms_mem src
  have hf4 := hf _ tm.1
  have hf10 := hf _ tm.2.1
  let H := regValue src base
  have hH : H<2^128 := lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
  have seed := Acc.seed_triple acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4 base hz
    0 (16*H) (Or.inl (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
  have add : Triple (SquareFrame acc base (16*H))
      (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src false 10))
      (SquareFrame acc base (1040*H)) := by
    have h := Acc.op_prefix_triple acc Z bank cin 161 139 (Acc.earlyTerm src false 10) hacc
      (by norm_num [Acc.earlyTerm]) hf10 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (16*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : Acc.step base false (16*H) (Acc.earlyTerm src false 10)=1040*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  exact seed.seq add

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: buildCached_frame
theorem buildCached_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (A161NarrowAcc.build8 acc Z bank cin src)) :
    run (buildCached acc Z bank cin src q) m s=
      setWire (run (A161NarrowAcc.build8 acc Z bank cin src) m s) q (cacheBit (regValue src s.basis)) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (buildPre acc Z bank cin src) (m.take (measurementCount (buildPre acc Z bank cin src))) s
  have preFrame:=buildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
    (m.take (measurementCount (buildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (A161NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have len:(acc.take 139).length=139 := by simp [hacc]
  have lens:=Acc.fits_lengths (acc.take 139) Z bank cin 139 f len fit.toFitsLen
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have window:(Acc.ty (acc.take 139) f).length=133 := by simpa [f,Acc.earlyTerm] using lens.2.2
  have xv:regValue (Acc.tx Z 139 f) t.basis=H := by
    have zero:regValue (Z.take (139-f.shift-f.src.length)) t.basis=0 := (regValue_zero _ _).mpr (by
      intro w hw
      exact (same w (Or.inl (by simp [List.mem_of_mem_take hw]))).trans (hz w (List.mem_of_mem_take hw)))
    have srcv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
    change regValue (src++Z.take (139-6-src.length)) t.basis=H
    change regValue (Z.take (139-6-src.length)) t.basis=0 at zero
    rw [regValue_append,srcv,zero,Nat.mul_zero,Nat.add_zero]
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue (Acc.ty (acc.take 139) f) t.basis=1040*H/64 := by
    rw [Acc.ty,regValue_drop_div _ _ (by simp [f,Acc.earlyTerm,len]),pref.1]
    simp [f,Acc.earlyTerm]
  have clean:∀w∈Acc.tc bank 139 f,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=false := (preFrame.2.2 q qacc).trans hq
  have pieces:=off
  rw [build_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have count:=cachedSub_counts (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q lens.1 lens.2.1 (by omega)
  have changed:=cachedSub_known_frame (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q
    lens.1 lens.2.1 (by omega) nd t
    ((m.drop (measurementCount (buildPre acc Z bank cin src))).take (measurementCount (CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 f)))
    clean iv pieces.1.2 qt H xv yv
  have result:=modify_inside (buildPre acc Z bank cin src) (CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 f)
    (cachedSub (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q)
    (buildPost acc Z bank cin src) q (cacheBit H) count.2.1 pieces.2 s m changed
  simpa only [buildCached,build_split,f] using result

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: unbuildPre
def unbuildPre (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: unbuildPost
def unbuildPost (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  A161SourceTail.tail acc Z bank cin src++Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: unbuildConsumed
def unbuildConsumed (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire) : Program :=
  unbuildPre acc Z bank cin src++consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q++unbuildPost acc Z bank cin src

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: unbuild_split
theorem unbuild_split (acc Z bank : List Wire) (cin : Wire) (src : List Wire) :
    A161SourceAdd.unbuild acc Z bank cin src=
      unbuildPre acc Z bank cin src++A161SourceAdd.add acc Z bank cin src++unbuildPost acc Z bank cin src := by
  simp only [A161SourceAdd.unbuild,unbuildPre,unbuildPost,List.append_assoc]

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: unbuildPre_triple
theorem unbuildPre_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (base : BasisState) (hz:∀q∈Z,base q=false) (hb:∀q∈bank,base q=false) (hi:base cin=false) :
    Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuildPre acc Z bank cin src)
      (SquareFrame acc base (976*regValue src base)) := by
  have tm := A161NarrowAcc.terms_mem src
  have hf32 := hf _ tm.2.2.2
  let H := regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have top : Triple (SquareFrame acc base (4294968272*H))
      (CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32))
      (SquareFrame acc base (976*H)) := by
    have h := CodexKnownOnesTail.accSub_prefix_triple acc Z bank cin 161 161 106 (Acc.earlyTerm src false 32) hacc
      (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega)
      (by norm_num [Acc.earlyTerm]) base hz hb hi (4294968272*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (clear_sub32_range H hH).2.2)
    have value : Acc.step base true (4294968272*H) (Acc.earlyTerm src false 32)=976*H := by
      have e : regValue src base*2^32=4294967296*H := by dsimp only [H]; ring
      simp only [Acc.step,Acc.earlyTerm,if_true]
      rw [e]
      omega
    rw [value] at h
    exact h
  exact top

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: unbuildConsumed_frame
theorem unbuildConsumed_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (A161SourceAdd.unbuild acc Z bank cin src)) :
    run (unbuildConsumed acc Z bank cin src q) m s=
      setWire (run (A161SourceAdd.unbuild acc Z bank cin src) m s) q false := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (unbuildPre acc Z bank cin src) (m.take (measurementCount (unbuildPre acc Z bank cin src))) s
  have preFrame:=unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
    (m.take (measurementCount (unbuildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (A161NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have nd0:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd:(cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa only [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd0
  have bankLen:132≤bank.length := by
    have h:=hf6.bankLen
    norm_num [f,Acc.earlyTerm] at h
    omega
  have zlen:5≤Z.length := by
    have h:=hf6.zpad
    norm_num [f,Acc.earlyTerm,hsrc] at h
    omega
  have sv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue ((acc.take 139).drop 6) t.basis=976*H/64 := by
    rw [regValue_drop_div _ 6 (by simp [hacc]),pref.1]
    norm_num
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (same w (Or.inl (by simp [hw]))).trans (hz w hw)
  have clean:∀w∈bank.take 132,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=cacheBit H := (preFrame.2.2 q qacc).trans saved
  have qbank:q∉bank.take 132 := by intro bad;exact fresh (by simp [List.mem_of_mem_take bad])
  have pieces:=off
  rw [unbuild_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [hacc,hsrc]
  have hc:(bank.take 132).length+1=((acc.take 139).drop 6).length := by simp [hacc,Nat.min_eq_left bankLen]
  have count:=consumedAdd_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) hy (by simp [Nat.min_eq_left bankLen])
  have changed:=consumedAdd_frame src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) zlen hy hc nd t
    ((m.drop (measurementCount (unbuildPre acc Z bank cin src))).take (measurementCount (A161SourceAdd.add acc Z bank cin src)))
    zt clean iv H sv yv qbank pieces.1.2 qt
  have result:=modify_inside (unbuildPre acc Z bank cin src) (A161SourceAdd.add acc Z bank cin src)
    (consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q) (unbuildPost acc Z bank cin src)
    q false count.2.1 pieces.2 s m changed
  simpa only [unbuildConsumed,unbuild_split] using result

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: buildDual
def buildDual (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire) : Program :=
  buildPre acc Z bank cin src++
    cachedSubDual (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6))
      (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r++buildPost acc Z bank cin src

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: buildDual_frame
theorem buildDual_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false) (hr:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (A161NarrowAcc.build8 acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (rq:r≠q) :
    run (buildDual acc Z bank cin src q r) m s=
      setWire (run (buildCached acc Z bank cin src q) m s) r (cacheBit6 (regValue src s.basis)) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (buildPre acc Z bank cin src) (m.take (measurementCount (buildPre acc Z bank cin src))) s
  have preFrame:=buildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
    (m.take (measurementCount (buildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (A161NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have len:(acc.take 139).length=139 := by simp [hacc]
  have lens:=Acc.fits_lengths (acc.take 139) Z bank cin 139 f len fit.toFitsLen
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have window:(Acc.ty (acc.take 139) f).length=133 := by simpa [f,Acc.earlyTerm] using lens.2.2
  have xv:regValue (Acc.tx Z 139 f) t.basis=H := by
    have zero:regValue (Z.take (139-f.shift-f.src.length)) t.basis=0 := (regValue_zero _ _).mpr (by
      intro w hw
      exact (same w (Or.inl (by simp [List.mem_of_mem_take hw]))).trans (hz w (List.mem_of_mem_take hw)))
    have srcv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
    change regValue (src++Z.take (139-6-src.length)) t.basis=H
    change regValue (Z.take (139-6-src.length)) t.basis=0 at zero
    rw [regValue_append,srcv,zero,Nat.mul_zero,Nat.add_zero]
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue (Acc.ty (acc.take 139) f) t.basis=1040*H/64 := by
    rw [Acc.ty,regValue_drop_div _ _ (by simp [f,Acc.earlyTerm,len]),pref.1]
    simp [f,Acc.earlyTerm]
  have clean:∀w∈Acc.tc bank 139 f,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=false := (preFrame.2.2 q qacc).trans hq
  have pieces:=off
  rw [build_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=false := (preFrame.2.2 r racc).trans hr
  have piecesR:=offR
  rw [build_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have count:=cachedSubDual_counts (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r lens.1 lens.2.1 (by omega)
  have changed:=cachedSubDual_known_frame (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r
    lens.1 lens.2.1 (by omega) nd t
    ((m.drop (measurementCount (buildPre acc Z bank cin src))).take
      (measurementCount (cachedSub (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q)))
    clean iv pieces.1.2 piecesR.1.2 rq qt rt H xv yv
  have result:=modify_inside (buildPre acc Z bank cin src)
    (cachedSub (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q)
    (cachedSubDual (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r)
    (buildPost acc Z bank cin src) r (cacheBit6 H) count.2.1 piecesR.2 s m changed
  simpa only [buildDual,buildCached,f] using result

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: unbuildDual
def unbuildDual (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire) : Program :=
  unbuildPre acc Z bank cin src++
    consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r++unbuildPost acc Z bank cin src

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/MainPart04Base.lean :: unbuildDual_frame
theorem unbuildDual_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis)) (savedR:s.basis r=cacheBit6 (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src)) (rq:r≠q) :
    run (unbuildDual acc Z bank cin src q r) m s=
      setWire (run (unbuildConsumed acc Z bank cin src q) m s) r false := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (unbuildPre acc Z bank cin src) (m.take (measurementCount (unbuildPre acc Z bank cin src))) s
  have preFrame:=unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
    (m.take (measurementCount (unbuildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (A161NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have nd0:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd:(cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa only [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd0
  have bankLen:132≤bank.length := by
    have h:=hf6.bankLen
    norm_num [f,Acc.earlyTerm] at h
    omega
  have zlen:5≤Z.length := by
    have h:=hf6.zpad
    norm_num [f,Acc.earlyTerm,hsrc] at h
    omega
  have sv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue ((acc.take 139).drop 6) t.basis=976*H/64 := by
    rw [regValue_drop_div _ 6 (by simp [hacc]),pref.1]
    norm_num
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (same w (Or.inl (by simp [hw]))).trans (hz w hw)
  have clean:∀w∈bank.take 132,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=cacheBit H := (preFrame.2.2 q qacc).trans saved
  have qbank:q∉bank.take 132 := by intro bad;exact fresh (by simp [List.mem_of_mem_take bad])
  have pieces:=off
  rw [unbuild_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [hacc,hsrc]
  have hc:(bank.take 132).length+1=((acc.take 139).drop 6).length := by simp [hacc,Nat.min_eq_left bankLen]
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=cacheBit6 H := (preFrame.2.2 r racc).trans savedR
  have rbank:r∉bank.take 132 := by intro bad;exact freshR (by simp [List.mem_of_mem_take bad])
  have freshQ:q∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132 := by
    intro bad
    simp only [List.mem_append] at bad
    rcases bad with ((h|h)|h)|h
    · exact fresh (by simp [h])
    · exact fresh (by simp [List.mem_of_mem_take h])
    · exact fresh (by simp [List.mem_of_mem_take (List.mem_of_mem_drop h)])
    · exact fresh (by simp [List.mem_of_mem_take h])
  have piecesR:=offR
  rw [unbuild_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have count:=consumedAddDual_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r
    (by omega) hy (by simp [Nat.min_eq_left bankLen])
  have changed:=consumedAddDual_frame src Z ((acc.take 139).drop 6) (bank.take 132) cin q r
    (by omega) zlen hy hc nd t
    ((m.drop (measurementCount (unbuildPre acc Z bank cin src))).take
      (measurementCount (consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q)))
    zt clean iv H sv yv freshQ rbank rq piecesR.1.2 qt rt
  have result:=modify_inside (unbuildPre acc Z bank cin src)
    (consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q)
    (consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r) (unbuildPost acc Z bank cin src)
    r false count.2.1 piecesR.2 s m changed
  simpa only [unbuildDual,unbuildConsumed] using result

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/ParkAMany.lean :: buildTriple
def buildTriple (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire):Program:=
 buildPre acc Z bank cin src++cachedSubTriple (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p++buildPost acc Z bank cin src

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/ParkAMany.lean :: buildTriple_frame
theorem buildTriple_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false) (hr:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (A161NarrowAcc.build8 acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (rq:r≠q)
    (hp:s.basis p=false) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (buildDual acc Z bank cin src q r)) :
    run (buildTriple acc Z bank cin src q r p) m s=
      setWire (run (buildDual acc Z bank cin src q r) m s) p (cacheBit7 (regValue src s.basis)) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (buildPre acc Z bank cin src) (m.take (measurementCount (buildPre acc Z bank cin src))) s
  have preFrame:=buildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
    (m.take (measurementCount (buildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (A161NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have len:(acc.take 139).length=139 := by simp [hacc]
  have lens:=Acc.fits_lengths (acc.take 139) Z bank cin 139 f len fit.toFitsLen
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have window:(Acc.ty (acc.take 139) f).length=133 := by simpa [f,Acc.earlyTerm] using lens.2.2
  have xv:regValue (Acc.tx Z 139 f) t.basis=H := by
    have zero:regValue (Z.take (139-f.shift-f.src.length)) t.basis=0 := (regValue_zero _ _).mpr (by
      intro w hw
      exact (same w (Or.inl (by simp [List.mem_of_mem_take hw]))).trans (hz w (List.mem_of_mem_take hw)))
    have srcv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
    change regValue (src++Z.take (139-6-src.length)) t.basis=H
    change regValue (Z.take (139-6-src.length)) t.basis=0 at zero
    rw [regValue_append,srcv,zero,Nat.mul_zero,Nat.add_zero]
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue (Acc.ty (acc.take 139) f) t.basis=1040*H/64 := by
    rw [Acc.ty,regValue_drop_div _ _ (by simp [f,Acc.earlyTerm,len]),pref.1]
    simp [f,Acc.earlyTerm]
  have clean:∀w∈Acc.tc bank 139 f,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=false := (preFrame.2.2 q qacc).trans hq
  have pieces:=off
  rw [build_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=false := (preFrame.2.2 r racc).trans hr
  have piecesR:=offR
  rw [build_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=false:=(preFrame.2.2 p pacc).trans hp
  have piecesP:=offP
  rw[buildDual]at piecesP
  simp only[wires_append,Finset.mem_union,not_or]at piecesP
  have count:=cachedSubTriple_counts (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p lens.1 lens.2.1 (by omega)
  have changed:=cachedSubTriple_known_frame (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p
   lens.1 lens.2.1 (by omega) nd t
   ((m.drop (measurementCount (buildPre acc Z bank cin src))).take
    (measurementCount (cachedSubDual (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r)))
   clean iv pieces.1.2 piecesR.1.2 rq piecesP.1.2 qt rt pt H xv yv
  have result:=modify_inside (buildPre acc Z bank cin src)
   (cachedSubDual (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r)
   (cachedSubTriple (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p)
   (buildPost acc Z bank cin src) p (cacheBit7 H) count.2.1 piecesP.2 s m changed
  simpa only[buildTriple,buildDual,f]using result

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/ParkAMany.lean :: unbuildTriple
def unbuildTriple (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire):Program:=
 unbuildPre acc Z bank cin src++consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p++unbuildPost acc Z bank cin src

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/ParkAMany.lean :: unbuildTriple_frame
theorem unbuildTriple_frame (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis)) (savedR:s.basis r=cacheBit6 (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src)) (rq:r≠q)
    (savedP:s.basis p=cacheBit7 (regValue src s.basis)) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (unbuildDual acc Z bank cin src q r)) (pq:p≠q) (pr:p≠r) :
    run (unbuildTriple acc Z bank cin src q r p) m s=
      setWire (run (unbuildDual acc Z bank cin src q r) m s) p false := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (unbuildPre acc Z bank cin src) (m.take (measurementCount (unbuildPre acc Z bank cin src))) s
  have preFrame:=unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
    (m.take (measurementCount (unbuildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (A161NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have nd0:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd:(cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa only [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd0
  have bankLen:132≤bank.length := by
    have h:=hf6.bankLen
    norm_num [f,Acc.earlyTerm] at h
    omega
  have zlen:5≤Z.length := by
    have h:=hf6.zpad
    norm_num [f,Acc.earlyTerm,hsrc] at h
    omega
  have sv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue ((acc.take 139).drop 6) t.basis=976*H/64 := by
    rw [regValue_drop_div _ 6 (by simp [hacc]),pref.1]
    norm_num
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (same w (Or.inl (by simp [hw]))).trans (hz w hw)
  have clean:∀w∈bank.take 132,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=cacheBit H := (preFrame.2.2 q qacc).trans saved
  have qbank:q∉bank.take 132 := by intro bad;exact fresh (by simp [List.mem_of_mem_take bad])
  have pieces:=off
  rw [unbuild_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [hacc,hsrc]
  have hc:(bank.take 132).length+1=((acc.take 139).drop 6).length := by simp [hacc,Nat.min_eq_left bankLen]
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=cacheBit6 H := (preFrame.2.2 r racc).trans savedR
  have rbank:r∉bank.take 132 := by intro bad;exact freshR (by simp [List.mem_of_mem_take bad])
  have freshQ:q∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132 := by
    intro bad
    simp only [List.mem_append] at bad
    rcases bad with ((h|h)|h)|h
    · exact fresh (by simp [h])
    · exact fresh (by simp [List.mem_of_mem_take h])
    · exact fresh (by simp [List.mem_of_mem_take (List.mem_of_mem_drop h)])
    · exact fresh (by simp [List.mem_of_mem_take h])
  have piecesR:=offR
  rw [unbuild_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=cacheBit7 H:=(preFrame.2.2 p pacc).trans savedP
  have pbank:p∉bank.take 132:=by intro bad;exact freshP (by simp[List.mem_of_mem_take bad])
  have freshR':r∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132:=by
   intro bad
   simp only[List.mem_append]at bad
   rcases bad with ((h|h)|h)|h
   · exact freshR (by simp[h])
   · exact freshR (by simp[List.mem_of_mem_take h])
   · exact freshR (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
   · exact freshR (by simp[List.mem_of_mem_take h])
  have piecesP:=offP
  rw[unbuildDual]at piecesP
  simp only[wires_append,Finset.mem_union,not_or]at piecesP
  have count:=consumedAddTriple_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p
   (by omega) hy (by simp[Nat.min_eq_left bankLen])
  have changed:=consumedAddTriple_frame src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p
   (by omega) zlen hy hc nd t
   ((m.drop (measurementCount (unbuildPre acc Z bank cin src))).take
    (measurementCount (consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r)))
   zt clean iv H sv yv freshQ freshR' rq pbank pq pr piecesP.1.2 qt rt pt
  have result:=modify_inside (unbuildPre acc Z bank cin src)
   (consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r)
   (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) (unbuildPost acc Z bank cin src)
   p false count.2.1 piecesP.2 s m changed
  simpa only[unbuildTriple,unbuildDual]using result

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/ParkAMany.lean :: buildMany
def buildMany (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire):Program:=
 buildPre acc Z bank cin src++cachedSubMany k (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) hs cin q r p++buildPost acc Z bank cin src

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/ParkAMany.lean :: buildMany_frame
theorem buildMany_frame (k:Nat) (acc Z bank : List Wire) (cin : Wire) (src hs : List Wire) (q r p : Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (hq:s.basis q=false) (hr:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (A161NarrowAcc.build8 acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (rq:r≠q)
    (hp:s.basis p=false) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (buildDual acc Z bank cin src q r))
    (hk:k≤119) (ndhs:hs.Nodup)
    (hu:∀u∈hs,s.basis u=false) (freshU:∀u∈hs,u∉cin::(src++acc++Z++bank))
    (offU:∀u∈hs,u∉wires (buildTriple acc Z bank cin src q r p)) :
    run (buildMany k acc Z bank cin src hs q r p) m s=
      scatterState hs (bankValues 7 k (regValue src s.basis)) (run (buildTriple acc Z bank cin src q r p) m s) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (buildPre acc Z bank cin src) (m.take (measurementCount (buildPre acc Z bank cin src))) s
  have preFrame:=buildPre_triple acc Z bank cin src hacc (by omega) hf s.basis hz hb hi s
    (m.take (measurementCount (buildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (A161NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have len:(acc.take 139).length=139 := by simp [hacc]
  have lens:=Acc.fits_lengths (acc.take 139) Z bank cin 139 f len fit.toFitsLen
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have window:(Acc.ty (acc.take 139) f).length=133 := by simpa [f,Acc.earlyTerm] using lens.2.2
  have xv:regValue (Acc.tx Z 139 f) t.basis=H := by
    have zero:regValue (Z.take (139-f.shift-f.src.length)) t.basis=0 := (regValue_zero _ _).mpr (by
      intro w hw
      exact (same w (Or.inl (by simp [List.mem_of_mem_take hw]))).trans (hz w (List.mem_of_mem_take hw)))
    have srcv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
    change regValue (src++Z.take (139-6-src.length)) t.basis=H
    change regValue (Z.take (139-6-src.length)) t.basis=0 at zero
    rw [regValue_append,srcv,zero,Nat.mul_zero,Nat.add_zero]
  have pref:=regValue_take_drop_of_lt acc 139 (1040*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue (Acc.ty (acc.take 139) f) t.basis=1040*H/64 := by
    rw [Acc.ty,regValue_drop_div _ _ (by simp [f,Acc.earlyTerm,len]),pref.1]
    simp [f,Acc.earlyTerm]
  have clean:∀w∈Acc.tc bank 139 f,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=false := (preFrame.2.2 q qacc).trans hq
  have pieces:=off
  rw [build_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=false := (preFrame.2.2 r racc).trans hr
  have piecesR:=offR
  rw [build_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=false:=(preFrame.2.2 p pacc).trans hp
  have piecesP:=offP
  rw[buildDual]at piecesP
  simp only[wires_append,Finset.mem_union,not_or]at piecesP
  have ut (u:Wire) (h:u∈hs):t.basis u=false:=by
    have uacc:u∉acc:=by intro bad;exact freshU u h (by simp[bad])
    exact (preFrame.2.2 u uacc).trans (hu u h)
  have piecesU (u:Wire) (h:u∈hs):u∉wires (buildPre acc Z bank cin src) ∧
    u∉wires (cachedSubTriple (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p) ∧
    u∉wires (buildPost acc Z bank cin src):=by
    have free:=offU u h
    rw[buildTriple]at free
    simpa only[wires_append,Finset.mem_union,not_or,and_assoc,f]using free
  have freshcs (u:Wire) (h:u∈hs):u∉Acc.tc bank 139 f:=by
    intro bad
    exact freshU u h (by simp[List.mem_of_mem_take bad])
  have qc:q∉Acc.tc bank 139 f:=by intro bad;exact fresh (by simp[List.mem_of_mem_take bad])
  have rc:r∉Acc.tc bank 139 f:=by intro bad;exact freshR (by simp[List.mem_of_mem_take bad])
  have pc:p∉Acc.tc bank 139 f:=by intro bad;exact freshP (by simp[List.mem_of_mem_take bad])
  have count:=cachedSubMany_counts k (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) hs cin q r p lens.1 lens.2.1 (by omega)
  have changed:=cachedSubMany_known_frame k H (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) hs cin q r p
   lens.1 lens.2.1 (by omega) nd t (m.drop (measurementCount (buildPre acc Z bank cin src)))
   clean iv pieces.1.2 piecesR.1.2 rq piecesP.1.2 qc rc pc qt rt pt xv yv ndhs freshcs
   (fun u h=>(piecesU u h).2.1) ut
  have result:=modify_many_inside (buildPre acc Z bank cin src)
   (cachedSubTriple (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) cin q r p)
   (cachedSubMany k (Acc.tx Z 139 f) (Acc.ty (acc.take 139) f) (Acc.tc bank 139 f) hs cin q r p)
   (buildPost acc Z bank cin src) hs (bankValues 7 k H) count.2.1
   (fun u h=>(piecesU u h).2.2) s m (by simpa only[t,run_take]using changed)
  simpa only[buildMany,buildTriple,f,H]using result

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/ParkAMany.lean :: unbuildMany
def unbuildMany (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire):Program:=
 unbuildPre acc Z bank cin src++consumedAddMany k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p++unbuildPost acc Z bank cin src

-- Width161 adaptation from ECDSAAdd/Submission/Entrant/ParkAMany.lean :: unbuildMany_frame
theorem unbuildMany_frame (k:Nat) (acc Z bank : List Wire) (cin : Wire) (src hs : List Wire) (q r p : Wire)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=4294968272*regValue src s.basis)
    (saved:s.basis q=cacheBit (regValue src s.basis)) (savedR:s.basis r=cacheBit6 (regValue src s.basis))
    (fresh:q∉cin::(src++acc++Z++bank)) (off:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
    (freshR:r∉cin::(src++acc++Z++bank)) (offR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src)) (rq:r≠q)
    (savedP:s.basis p=cacheBit7 (regValue src s.basis)) (freshP:p∉cin::(src++acc++Z++bank))
    (offP:p∉wires (unbuildDual acc Z bank cin src q r)) (pq:p≠q) (pr:p≠r)
    (hk:k≤119) (ndhs:hs.Nodup) (hostlen:hs.length=k)
    (savedU:hs.map s.basis=bankValues 7 k (regValue src s.basis))
    (freshU:∀u∈hs,u∉cin::(src++acc++Z++bank))
    (offU:∀u∈hs,u∉wires (unbuildTriple acc Z bank cin src q r p)) :
    run (unbuildMany k acc Z bank cin src hs q r p) m s=
      scatterState hs (List.replicate hs.length false) (run (unbuildTriple acc Z bank cin src q r p) m s) := by
  let H:=regValue src s.basis
  let f:=Acc.earlyTerm src true 6
  let t:=run (unbuildPre acc Z bank cin src) (m.take (measurementCount (unbuildPre acc Z bank cin src))) s
  have preFrame:=unbuildPre_triple acc Z bank cin src hacc hsrc hf s.basis hz hb hi s
    (m.take (measurementCount (unbuildPre acc Z bank cin src))) ⟨ha,fun _ _=>rfl⟩
  have hH:H<2^128 := by simpa [H,hsrc] using regValue_lt src s.basis
  have hf6:=hf f (A161NarrowAcc.terms_mem src).2.2.1
  have ndall:(cin::(src++acc++Z++bank)).Nodup := by simpa [f,Acc.earlyTerm] using hf6.nd
  have hnd:=List.nodup_iff_count_le_one.mp ndall
  have away (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : w∉acc := by
    intro bad
    have h:=hnd w
    have a:=List.count_pos_iff.mpr bad
    rcases hw with hw|rfl
    · have b:=List.count_pos_iff.mpr hw
      simp only [List.count_cons,List.count_append] at h b
      split at h <;> omega
    · simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h
      omega
  have same (w : Wire) (hw:w∈src++Z++bank ∨ w=cin) : t.basis w=s.basis w := preFrame.2.2 w (away w hw)
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 f (by decide) hf6 (by simp [f,Acc.earlyTerm,hsrc])
  have nd0:=Acc.fits_nodup (acc.take 139) Z bank cin 139 f fit
  have nd:(cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa only [Acc.tx,Acc.ty,Acc.tc,f,Acc.earlyTerm,hsrc] using nd0
  have bankLen:132≤bank.length := by
    have h:=hf6.bankLen
    norm_num [f,Acc.earlyTerm] at h
    omega
  have zlen:5≤Z.length := by
    have h:=hf6.zpad
    norm_num [f,Acc.earlyTerm,hsrc] at h
    omega
  have sv:regValue src t.basis=H := regValue_congr _ _ _ (fun w hw=>same w (Or.inl (by simp [hw])))
  have pref:=regValue_take_drop_of_lt acc 139 (976*H) t.basis (by omega) preFrame.2.1 (by norm_num at hH ⊢;omega)
  have yv:regValue ((acc.take 139).drop 6) t.basis=976*H/64 := by
    rw [regValue_drop_div _ 6 (by simp [hacc]),pref.1]
    norm_num
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (same w (Or.inl (by simp [hw]))).trans (hz w hw)
  have clean:∀w∈bank.take 132,t.basis w=false := by
    intro w hw
    have member:w∈bank := List.mem_of_mem_take hw
    exact (same w (Or.inl (by simp [member]))).trans (hb w member)
  have iv:t.basis cin=false := (same cin (Or.inr rfl)).trans hi
  have qacc:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qt:t.basis q=cacheBit H := (preFrame.2.2 q qacc).trans saved
  have qbank:q∉bank.take 132 := by intro bad;exact fresh (by simp [List.mem_of_mem_take bad])
  have pieces:=off
  rw [unbuild_split] at pieces
  simp only [wires_append,Finset.mem_union,not_or] at pieces
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [hacc,hsrc]
  have hc:(bank.take 132).length+1=((acc.take 139).drop 6).length := by simp [hacc,Nat.min_eq_left bankLen]
  have racc:r∉acc := by intro bad;exact freshR (by simp [bad])
  have rt:t.basis r=cacheBit6 H := (preFrame.2.2 r racc).trans savedR
  have rbank:r∉bank.take 132 := by intro bad;exact freshR (by simp [List.mem_of_mem_take bad])
  have freshQ:q∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132 := by
    intro bad
    simp only [List.mem_append] at bad
    rcases bad with ((h|h)|h)|h
    · exact fresh (by simp [h])
    · exact fresh (by simp [List.mem_of_mem_take h])
    · exact fresh (by simp [List.mem_of_mem_take (List.mem_of_mem_drop h)])
    · exact fresh (by simp [List.mem_of_mem_take h])
  have piecesR:=offR
  rw [unbuild_split] at piecesR
  simp only [wires_append,Finset.mem_union,not_or] at piecesR
  have pacc:p∉acc:=by intro bad;exact freshP (by simp[bad])
  have pt:t.basis p=cacheBit7 H:=(preFrame.2.2 p pacc).trans savedP
  have freshP':p∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132:=by
   intro bad
   simp only[List.mem_append]at bad
   rcases bad with ((h|h)|h)|h
   · exact freshP (by simp[h])
   · exact freshP (by simp[List.mem_of_mem_take h])
   · exact freshP (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
   · exact freshP (by simp[List.mem_of_mem_take h])
  have freshR':r∉(src++Z.take 5)++(acc.take 139).drop 6++bank.take 132:=by
   intro bad
   simp only[List.mem_append]at bad
   rcases bad with ((h|h)|h)|h
   · exact freshR (by simp[h])
   · exact freshR (by simp[List.mem_of_mem_take h])
   · exact freshR (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
   · exact freshR (by simp[List.mem_of_mem_take h])
  have restrictFresh (w:Wire) (free:w∉cin::(src++acc++Z++bank)):
    w∉cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132):=by
    intro bad
    simp only[List.mem_cons,List.mem_append]at bad
    rcases bad with rfl|((h|h)|h)|h
    · exact free (by simp)
    · exact free (by simp[h])
    · exact free (by simp[List.mem_of_mem_take h])
    · exact free (by simp[List.mem_of_mem_take (List.mem_of_mem_drop h)])
    · exact free (by simp[List.mem_of_mem_take h])
  have preEq:run (consumePre3 src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) [] t=
    scatterState [q,r,p] [false,false,false]
      (run (carryPrefix 7 (src++Z.take 5) ((acc.take 139).drop 6) (bank.take 132) cin) [] t):=by
    exact source_prefix_consumed_eq7 src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p
     (by omega) zlen hy hc nd t zt clean iv H sv yv freshQ freshR' rq
     (by intro h;exact freshP' (by simp[h])) pq pr qt rt pt
  have svx:regValue (src++Z.take 5) t.basis=H:=by
    rw[regValue_append,sv,(regValue_zero _ _).mpr (fun w hw=>zt w (List.mem_of_mem_take hw))]
    simp
  have savedUt:hs.map t.basis=bankValues 7 k H:=by
    rw[show bankValues 7 k H=hs.map s.basis from savedU.symm]
    apply List.map_congr_left
    intro u hu
    exact preFrame.2.2 u (fun bad=>freshU u hu (by simp[bad]))
  have windowlen:((acc.take 139).drop 6).length=133:=by simp[hacc]
  have carrylen:(bank.take 132).length=132:=by simp[Nat.min_eq_left bankLen]
  have piecesU (u:Wire) (hu:u∈hs):u∉wires (unbuildPre acc Z bank cin src) ∧
    u∉wires (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) ∧
    u∉wires (unbuildPost acc Z bank cin src):=by
    have free:=offU u hu
    rw[unbuildTriple]at free
    simpa only[wires_append,Finset.mem_union,not_or,and_assoc]using free
  have freepieces (u:Wire) (hu:u∈hs):
    u∉wires (consumePre3 src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p) ∧
    u∉wires (prefixAfter 7 k (src++Z.take 5) ((acc.take 139).drop 6) (bank.take 132) cin) ∧
    u∉wires (inversePostN k src Z ((acc.take 139).drop 6) (bank.take 132) cin):=by
    have free:=(piecesU u hu).2.1
    rw[consumedAddTriple_splitN k src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p (by omega) (by omega) (by omega)]at free
    simpa only[wires_append,Finset.mem_union,not_or,and_assoc]using free
  have oldoff:∀w∈[q,r,p],w∉wires (prefixAfter 7 k (src++Z.take 5) ((acc.take 139).drop 6) (bank.take 132) cin):=by
    intro w hw
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hw
    rcases hw with rfl|rfl|rfl
    · exact prefixAfter_off _ _ _ _ _ _ _ (restrictFresh _ fresh)
    · exact prefixAfter_off _ _ _ _ _ _ _ (restrictFresh _ freshR)
    · exact prefixAfter_off _ _ _ _ _ _ _ (restrictFresh _ freshP)
  have oldfresh:∀w∈((bank.take 132).drop 7).take k,w∉[q,r,p]:=by
    intro w hw bad
    have mem:w∈bank:=List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_mem_take hw))
    simp only[List.mem_cons,List.not_mem_nil,or_false]at bad
    rcases bad with rfl|rfl|rfl
    · exact fresh (by simp[mem])
    · exact freshR (by simp[mem])
    · exact freshP (by simp[mem])
  have freebank:∀u∈hs,u∉((bank.take 132).drop 7).take k:=by
    intro u hu bad
    exact freshU u hu (by simp[List.mem_of_mem_take (List.mem_of_mem_drop (List.mem_of_mem_take bad))])
  have count:=consumedAddMany_counts k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
   (by omega) (by omega) (by omega) hostlen
  have changed:=consumedAddMany_known_frame k H src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
   (by omega) (by omega) (by omega) nd ndhs hostlen freebank
   (fun u hu=>(freepieces u hu).1) (fun u hu=>(freepieces u hu).2.2) oldoff oldfresh
   t (m.drop (measurementCount (unbuildPre acc Z bank cin src))) clean iv svx yv preEq savedUt
  have result:=modify_many_inside (unbuildPre acc Z bank cin src)
   (consumedAddTriple src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p)
   (consumedAddMany k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p) (unbuildPost acc Z bank cin src)
   hs (List.replicate hs.length false) count.2.1 (fun u hu=>(piecesU u hu).2.2) s m
   (by simpa only[t,run_take]using changed)
  simpa only[unbuildMany,unbuildTriple]using result
#print axioms buildMany_frame
#print axioms unbuildMany_frame
end ECDSAAdd.Entrant.A161Carry

end

-- Component Loops
section
namespace ECDSAAdd.Entrant.A161Carry
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop
 ThirdSavedCarryDevelop FourthASavedCarryDevelop ManyACarryDevelop ControlLoan1589BFFold ZeroReadDevelop CodexNarrowTail
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires
-- Width161 adaptation of MainPart04Base.lean :: sub6_lengths
theorem sub6_lengths (acc Z bank : List Wire) (src : List Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    (Acc.tx Z 139 (Acc.earlyTerm src true 6)).length=133 ∧
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)).length=133 ∧
    (Acc.tc bank 139 (Acc.earlyTerm src true 6)).length=132 := by
  simp [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,ha,hs,Nat.min_eq_left hz,Nat.min_eq_left hb]

-- Width161 adaptation of MainPart04Base.lean :: buildCached_counts
theorem buildCached_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    toffoliCount (buildCached acc Z bank cin src q)=toffoliCount (A161NarrowAcc.build8 acc Z bank cin src) ∧
    measurementCount (buildCached acc Z bank cin src q)=measurementCount (A161NarrowAcc.build8 acc Z bank cin src) ∧
    Challenge.gateSlots (buildCached acc Z bank cin src q)=Challenge.gateSlots (A161NarrowAcc.build8 acc Z bank cin src)+1 := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have count:=cachedSub_counts (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q
    (by omega) (by omega) (by omega)
  simp only [buildCached,build_split,CodexNarrowSub.accSub,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of MainPart04Base.lean :: unbuildConsumed_counts
theorem unbuildConsumed_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length) :
    toffoliCount (unbuildConsumed acc Z bank cin src q)+1=toffoliCount (A161SourceAdd.unbuild acc Z bank cin src) ∧
    measurementCount (unbuildConsumed acc Z bank cin src q)=measurementCount (A161SourceAdd.unbuild acc Z bank cin src) ∧
    Challenge.gateSlots (unbuildConsumed acc Z bank cin src q)+4=Challenge.gateSlots (A161SourceAdd.unbuild acc Z bank cin src) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:5≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have count:=consumedAdd_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) hy hc
  simp only [unbuildConsumed,unbuild_split,A161SourceAdd.add,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of MainPart04Base.lean :: cached_wloop_eq
theorem cached_wloop_eq (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire) (middle : Program)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false)
    (fresh:q∉cin::(src++acc++Z++bank))
    (offF:q∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
    (offI:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
    (good:let u:=middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m
      regValue acc u.basis=4294968272*regValue src s.basis ∧ regValue src u.basis=regValue src s.basis ∧
      (∀w∈Z,u.basis w=false) ∧ (∀w∈bank,u.basis w=false) ∧ u.basis cin=false) :
    run (buildCached acc Z bank cin src q++middle++unbuildConsumed acc Z bank cin src q) m s=
      run (A161NarrowAcc.build8 acc Z bank cin src++middle++A161SourceAdd.unbuild acc Z bank cin src) m s := by
  let H:=regValue src s.basis
  let u:=middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m
  let t:=setWire u q (cacheBit H)
  have qs:q∉src := by intro bad;exact fresh (by simp [bad])
  have qa:q∉acc := by intro bad;exact fresh (by simp [bad])
  have qz:q∉Z := by intro bad;exact fresh (by simp [bad])
  have qb:q∉bank := by intro bad;exact fresh (by simp [bad])
  have qi:cin≠q := by intro e;exact fresh (by simp [←e])
  have keep (w : Wire) (ne:w≠q) : t.basis w=u.basis w := by simp [t,setWire,writeBit,Function.update,ne]
  have sv:regValue src t.basis=H := (setWire_regValue src u q _ qs).trans good.2.1
  have av:regValue acc t.basis=4294968272*regValue src t.basis := by
    rw [show regValue acc t.basis=regValue acc u.basis from setWire_regValue acc u q _ qa,sv]
    exact good.1
  have zt:∀w∈Z,t.basis w=false := by
    intro w hw
    exact (keep w (by intro e;exact qz (e ▸ hw))).trans (good.2.2.1 w hw)
  have bt:∀w∈bank,t.basis w=false := by
    intro w hw
    exact (keep w (by intro e;exact qb (e ▸ hw))).trans (good.2.2.2.1 w hw)
  have it:t.basis cin=false := (keep cin qi).trans good.2.2.2.2
  have saved:t.basis q=cacheBit (regValue src t.basis) := by
    rw [sv]
    simp only [t,setWire,writeBit,Function.update_self]
  have fwd:=buildCached_frame acc Z bank cin src q hacc hsrc hf s
    (m.take (measurementCount (A161NarrowAcc.build8 acc Z bank cin src))) hz hb hi ha zero fresh offF
  have inv:=unbuildConsumed_frame acc Z bank cin src q hacc hsrc hf t
    (m.drop (measurementCount (A161NarrowAcc.build8 acc Z bank cin src)+measurementCount middle)) zt bt it av saved fresh offI
  have hf6:=hf _ (A161NarrowAcc.terms_mem src).2.2.1
  have zl:5≤Z.length := by have h:=hf6.zpad;norm_num [Acc.earlyTerm,hsrc] at h;omega
  have bl:132≤bank.length := by have h:=hf6.bankLen;norm_num [Acc.earlyTerm] at h;omega
  have count:=buildCached_counts acc Z bank cin src q hacc hsrc zl bl
  exact cached_pair_eq _ _ middle _ _ q (cacheBit H) count.2.1 offF offM offI s m zero fwd inv

-- Width161 adaptation of MainPart04Base.lean :: buildCached_support
theorem buildCached_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    wires (buildCached acc Z bank cin src q)⊆insert q (wires (A161NarrowAcc.build8 acc Z bank cin src)) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have sub:=cachedSub_support (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q
    (by omega) (by omega) (by omega)
  intro w hw
  by_cases eq:w=q
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [buildCached,wires_append,Finset.mem_union] at hw
  simp only [build_split,CodexNarrowSub.accSub,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

-- Width161 adaptation of MainPart04Base.lean :: unbuildConsumed_support
theorem unbuildConsumed_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length) :
    wires (unbuildConsumed acc Z bank cin src q)⊆insert q (wires (A161SourceAdd.unbuild acc Z bank cin src)) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:5≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have sub:=consumedAdd_support src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) hy hc
  intro w hw
  by_cases eq:w=q
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [unbuildConsumed,wires_append,Finset.mem_union] at hw
  simp only [unbuild_split,A161SourceAdd.add,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

-- Width161 adaptation of MainPart04Base.lean :: buildDual_counts
theorem buildDual_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    toffoliCount (buildDual acc Z bank cin src q r)=toffoliCount (buildCached acc Z bank cin src q) ∧
    measurementCount (buildDual acc Z bank cin src q r)=measurementCount (buildCached acc Z bank cin src q) ∧
    Challenge.gateSlots (buildDual acc Z bank cin src q r)=Challenge.gateSlots (buildCached acc Z bank cin src q)+1 := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have count:=cachedSubDual_counts (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r
    (by omega) (by omega) (by omega)
  simp only [buildDual,buildCached,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of MainPart04Base.lean :: unbuildDual_counts
theorem unbuildDual_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length) :
    toffoliCount (unbuildDual acc Z bank cin src q r)+1=toffoliCount (unbuildConsumed acc Z bank cin src q) ∧
    measurementCount (unbuildDual acc Z bank cin src q r)=measurementCount (unbuildConsumed acc Z bank cin src q) ∧
    Challenge.gateSlots (unbuildDual acc Z bank cin src q r)+4=Challenge.gateSlots (unbuildConsumed acc Z bank cin src q) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:6≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have count:=consumedAddDual_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r (by omega) hy hc
  simp only [unbuildDual,unbuildConsumed,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
  exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of MainPart04Base.lean :: cached_wloop_dual_eq
theorem cached_wloop_dual_eq (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire) (middle : Program)
    (hacc:acc.length=161) (hsrc:src.length=128)
    (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (s : State) (m : List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
    (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false)
    (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
    (offF:q∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
    (offI:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
    (offFR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
    (offIR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src))
    (good:WReady acc Z bank cin src (regValue src s.basis)
      (middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m)) :
    run (buildDual acc Z bank cin src q r++middle++unbuildDual acc Z bank cin src q r) m s=
      run (A161NarrowAcc.build8 acc Z bank cin src++middle++A161SourceAdd.unbuild acc Z bank cin src) m s := by
  let H:=regValue src s.basis
  have hf6:=hf _ (A161NarrowAcc.terms_mem src).2.2.1
  have zl:5≤Z.length := by have h:=hf6.zpad;norm_num [Acc.earlyTerm,hsrc] at h;omega
  have bl:132≤bank.length := by have h:=hf6.bankLen;norm_num [Acc.earlyTerm] at h;omega
  have bc:=buildCached_counts acc Z bank cin src q hacc hsrc zl bl
  have dc:=buildDual_counts acc Z bank cin src q r hacc hsrc zl bl
  have offF1:r∉wires (buildCached acc Z bank cin src q) := by
    intro h
    have h:=Finset.mem_insert.mp (buildCached_support acc Z bank cin src q hacc hsrc zl bl h)
    exact h.elim rq offFR
  have offI1:r∉wires (unbuildConsumed acc Z bank cin src q) := by
    intro h
    have h:=Finset.mem_insert.mp (unbuildConsumed_support acc Z bank cin src q hacc hsrc bl h)
    exact h.elim rq offIR
  let u:=middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m
  let t1:=middleState (buildCached acc Z bank cin src q) middle s m
  let t2:=setWire t1 r (cacheBit6 H)
  have eq1:t1=setWire u q (cacheBit H) :=
    middleState_frame_copy _ _ middle q (cacheBit H) bc.2.1 offM s m
      (fun tape=>buildCached_frame acc Z bank cin src q hacc hsrc hf s tape hz hb hi ha zero fresh offF)
  have ready1:WReady acc Z bank cin src H t1 := by
    rw [eq1]
    exact WReady.setWire acc Z bank cin src H u q (cacheBit H) fresh good
  have ready2:WReady acc Z bank cin src H t2 :=
    WReady.setWire acc Z bank cin src H t1 r (cacheBit6 H) freshR ready1
  have saved1:t2.basis q=cacheBit (regValue src t2.basis) := by
    rw [ready2.2.1]
    have atq:t1.basis q=cacheBit H := by
      rw [eq1]
      simp only [setWire,writeBit,Function.update_self]
    exact (setWire_basis_outside t1 r q (cacheBit6 H) (Ne.symm rq)).trans atq
  have saved2:t2.basis r=cacheBit6 (regValue src t2.basis) := by
    rw [ready2.2.1]
    simp only [t2,setWire,writeBit,Function.update_self]
  have av:regValue acc t2.basis=4294968272*regValue src t2.basis := by
    rw [ready2.2.1]
    exact ready2.1
  have forward:=buildDual_frame acc Z bank cin src q r hacc hsrc hf s
    (m.take (measurementCount (buildCached acc Z bank cin src q))) hz hb hi ha zero zeroR fresh offF freshR offFR rq
  have inverse:=unbuildDual_frame acc Z bank cin src q r hacc hsrc hf t2
    (m.drop (measurementCount (buildCached acc Z bank cin src q)+measurementCount middle))
    ready2.2.2.1 ready2.2.2.2.1 ready2.2.2.2.2 av saved1 saved2 fresh offI freshR offIR rq
  have paired:=cached_pair_eq (buildCached acc Z bank cin src q) (buildDual acc Z bank cin src q r) middle
    (unbuildConsumed acc Z bank cin src q) (unbuildDual acc Z bank cin src q r) r (cacheBit6 H)
    dc.2.1 offF1 offMR offI1 s m zeroR forward inverse
  exact paired.trans (cached_wloop_eq acc Z bank cin src q middle hacc hsrc hf s m hz hb hi ha zero fresh offF offM offI good)

-- Width161 adaptation of ParkAMany.lean :: buildTriple_counts
theorem buildTriple_counts (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length):
 toffoliCount (buildTriple acc Z bank cin src q r p)=toffoliCount (buildDual acc Z bank cin src q r) ∧
 measurementCount (buildTriple acc Z bank cin src q r p)=measurementCount (buildDual acc Z bank cin src q r) ∧
 Challenge.gateSlots (buildTriple acc Z bank cin src q r p)=Challenge.gateSlots (buildDual acc Z bank cin src q r)+1:=by
 have len:=sub6_lengths acc Z bank src ha hs hz hb
 have count:=cachedSubTriple_counts (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p
  (by omega) (by omega) (by omega)
 simp only[buildTriple,buildDual,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of ParkAMany.lean :: unbuildTriple_counts
theorem unbuildTriple_counts (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length):
 toffoliCount (unbuildTriple acc Z bank cin src q r p)+1=toffoliCount (unbuildDual acc Z bank cin src q r) ∧
 measurementCount (unbuildTriple acc Z bank cin src q r p)=measurementCount (unbuildDual acc Z bank cin src q r) ∧
 Challenge.gateSlots (unbuildTriple acc Z bank cin src q r p)+4=Challenge.gateSlots (unbuildDual acc Z bank cin src q r):=by
 have hy:((acc.take 139).drop 6).length=src.length+5:=by simp[ha,hs]
 have hc:7≤(bank.take 132).length:=by simp[Nat.min_eq_left hb]
 have count:=consumedAddTriple_counts src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p (by omega) hy hc
 simp only[unbuildTriple,unbuildDual,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of ParkAMany.lean :: cached_wloop_triple_eq
theorem cached_wloop_triple_eq (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire) (middle:Program)
 (hacc:acc.length=161) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m)):
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s=
 run (buildDual acc Z bank cin src q r++middle++unbuildDual acc Z bank cin src q r) m s:=by
 let H:=regValue src s.basis
 have hf6:=hf _ (A161NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hsrc]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have bc:=buildCached_counts acc Z bank cin src q hacc hsrc zl bl
 have dc:=buildDual_counts acc Z bank cin src q r hacc hsrc zl bl
 have tc:=buildTriple_counts acc Z bank cin src q r p hacc hsrc zl bl
 let u:=middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m
 let t1:=middleState (buildCached acc Z bank cin src q) middle s m
 let t2:=middleState (buildDual acc Z bank cin src q r) middle s m
 let t3:=setWire t2 p (cacheBit7 H)
 have eq1:t1=setWire u q (cacheBit H):=
  middleState_frame_copy _ _ middle q (cacheBit H) bc.2.1 offM s m
   (fun tape=>buildCached_frame acc Z bank cin src q hacc hsrc hf s tape hz hb hi ha zero fresh offF)
 have eq2:t2=setWire t1 r (cacheBit6 H):=
  middleState_frame_copy _ _ middle r (cacheBit6 H) dc.2.1 offMR s m
   (fun tape=>buildDual_frame acc Z bank cin src q r hacc hsrc hf s tape hz hb hi ha zero zeroR fresh offF freshR offFR rq)
 have ready1:WReady acc Z bank cin src H t1:=by
  rw[eq1]
  exact WReady.setWire acc Z bank cin src H u q (cacheBit H) fresh good
 have ready2:WReady acc Z bank cin src H t2:=by
  rw[eq2]
  exact WReady.setWire acc Z bank cin src H t1 r (cacheBit6 H) freshR ready1
 have ready3:WReady acc Z bank cin src H t3:=
  WReady.setWire acc Z bank cin src H t2 p (cacheBit7 H) freshP ready2
 have atq:t2.basis q=cacheBit H:=by
  rw[eq2]
  rw[setWire_basis_outside t1 r q (cacheBit6 H) (Ne.symm rq)]
  rw[eq1]
  simp only[setWire,writeBit,Function.update_self]
 have atr:t2.basis r=cacheBit6 H:=by
  rw[eq2]
  simp only[setWire,writeBit,Function.update_self]
 have saved1:t3.basis q=cacheBit (regValue src t3.basis):=by
  rw[ready3.2.1]
  exact (setWire_basis_outside t2 p q (cacheBit7 H) (Ne.symm pq)).trans atq
 have saved2:t3.basis r=cacheBit6 (regValue src t3.basis):=by
  rw[ready3.2.1]
  exact (setWire_basis_outside t2 p r (cacheBit7 H) (Ne.symm pr)).trans atr
 have saved3:t3.basis p=cacheBit7 (regValue src t3.basis):=by
  rw[ready3.2.1]
  simp only[t3,setWire,writeBit,Function.update_self]
 have av:regValue acc t3.basis=4294968272*regValue src t3.basis:=by rw[ready3.2.1];exact ready3.1
 have forward:=buildTriple_frame acc Z bank cin src q r p hacc hsrc hf s
  (m.take (measurementCount (buildDual acc Z bank cin src q r))) hz hb hi ha zero zeroR fresh offF freshR offFR rq zeroP freshP offFP
 have inverse:=unbuildTriple_frame acc Z bank cin src q r p hacc hsrc hf t3
  (m.drop (measurementCount (buildDual acc Z bank cin src q r)+measurementCount middle))
  ready3.2.2.1 ready3.2.2.2.1 ready3.2.2.2.2 av saved1 saved2 fresh offI freshR offIR rq saved3 freshP offIP pq pr
 exact cached_pair_eq (buildDual acc Z bank cin src q r) (buildTriple acc Z bank cin src q r p) middle
  (unbuildDual acc Z bank cin src q r) (unbuildTriple acc Z bank cin src q r p) p (cacheBit7 H)
  tc.2.1 offFP offMP offIP s m zeroP forward inverse

-- Width161 adaptation of ParkAMany.lean :: triple_middle_ready
theorem triple_middle_ready (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire) (middle:Program)
 (hacc:acc.length=161) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m)):
 let t:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 WReady acc Z bank cin src (regValue src s.basis) t ∧
 t.basis q=cacheBit (regValue src s.basis) ∧ t.basis r=cacheBit6 (regValue src s.basis) ∧ t.basis p=cacheBit7 (regValue src s.basis):=by
 let H:=regValue src s.basis
 have hf6:=hf _ (A161NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hsrc]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have bc:=buildCached_counts acc Z bank cin src q hacc hsrc zl bl
 have dc:=buildDual_counts acc Z bank cin src q r hacc hsrc zl bl
 have tc:=buildTriple_counts acc Z bank cin src q r p hacc hsrc zl bl
 let u:=middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m
 let t1:=middleState (buildCached acc Z bank cin src q) middle s m
 let t2:=middleState (buildDual acc Z bank cin src q r) middle s m
 let t3:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 have eq1:t1=setWire u q (cacheBit H):=
  middleState_frame_copy _ _ middle q (cacheBit H) bc.2.1 offM s m
   (fun tape=>buildCached_frame acc Z bank cin src q hacc hsrc hf s tape hz hb hi ha zero fresh offF)
 have eq2:t2=setWire t1 r (cacheBit6 H):=
  middleState_frame_copy _ _ middle r (cacheBit6 H) dc.2.1 offMR s m
   (fun tape=>buildDual_frame acc Z bank cin src q r hacc hsrc hf s tape hz hb hi ha zero zeroR fresh offF freshR offFR rq)
 have eq3:t3=setWire t2 p (cacheBit7 H):=
  middleState_frame_copy _ _ middle p (cacheBit7 H) tc.2.1 offMP s m
   (fun tape=>buildTriple_frame acc Z bank cin src q r p hacc hsrc hf s tape hz hb hi ha zero zeroR fresh offF freshR offFR rq zeroP freshP offFP)
 have ready1:WReady acc Z bank cin src H t1:=by
  rw[eq1]
  exact WReady.setWire acc Z bank cin src H u q (cacheBit H) fresh good
 have ready2:WReady acc Z bank cin src H t2:=by
  rw[eq2]
  exact WReady.setWire acc Z bank cin src H t1 r (cacheBit6 H) freshR ready1
 have ready3:WReady acc Z bank cin src H t3:=by
  rw[eq3]
  exact WReady.setWire acc Z bank cin src H t2 p (cacheBit7 H) freshP ready2
 have atq:t2.basis q=cacheBit H:=by
  rw[eq2]
  rw[setWire_basis_outside t1 r q (cacheBit6 H) (Ne.symm rq)]
  rw[eq1]
  simp only[setWire,writeBit,Function.update_self]
 have atr:t2.basis r=cacheBit6 H:=by
  rw[eq2]
  simp only[setWire,writeBit,Function.update_self]
 have saved1:t3.basis q=cacheBit (regValue src t3.basis):=by
  rw[ready3.2.1]
  rw[eq3]
  exact (setWire_basis_outside t2 p q (cacheBit7 H) (Ne.symm pq)).trans atq
 have saved2:t3.basis r=cacheBit6 (regValue src t3.basis):=by
  rw[ready3.2.1]
  rw[eq3]
  exact (setWire_basis_outside t2 p r (cacheBit7 H) (Ne.symm pr)).trans atr
 have saved3:t3.basis p=cacheBit7 (regValue src t3.basis):=by
  rw[ready3.2.1]
  rw[eq3]
  simp only[setWire,writeBit,Function.update_self]
 exact ⟨ready3,by simpa only[ready3.2.1]using saved1,by simpa only[ready3.2.1]using saved2,by simpa only[ready3.2.1]using saved3⟩

-- Width161 adaptation of ParkAMany.lean :: buildMany_counts
theorem buildMany_counts (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤119) (hh:hs.length=k):
 toffoliCount (buildMany k acc Z bank cin src hs q r p)=toffoliCount (buildTriple acc Z bank cin src q r p) ∧
 measurementCount (buildMany k acc Z bank cin src hs q r p)=measurementCount (buildTriple acc Z bank cin src q r p) ∧
 Challenge.gateSlots (buildMany k acc Z bank cin src hs q r p)=Challenge.gateSlots (buildTriple acc Z bank cin src q r p)+k:=by
 have len:=sub6_lengths acc Z bank src ha hl hz hb
 have count:=cachedSubMany_counts k (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) hs cin q r p
  (by omega) (by omega) (by omega)
 have banklen:(((Acc.tc bank 139 (Acc.earlyTerm src true 6)).drop 7).take k).length=k:=by
  simp only[List.length_take,List.length_drop,len.2.2]
  omega
 rw[banklen,hh,Nat.min_self]at count
 simp only[buildMany,buildTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of ParkAMany.lean :: unbuildMany_counts
theorem unbuildMany_counts (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hl:src.length=128) (hb:132≤bank.length) (hk:k≤119) (hh:hs.length=k):
 toffoliCount (unbuildMany k acc Z bank cin src hs q r p)+k=toffoliCount (unbuildTriple acc Z bank cin src q r p) ∧
 measurementCount (unbuildMany k acc Z bank cin src hs q r p)=measurementCount (unbuildTriple acc Z bank cin src q r p) ∧
 Challenge.gateSlots (unbuildMany k acc Z bank cin src hs q r p)+4*k=Challenge.gateSlots (unbuildTriple acc Z bank cin src q r p):=by
 have count:=consumedAddMany_counts k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
  (by omega) (by simp only[List.length_drop,List.length_take];omega)
  (by simp only[List.length_take];omega) hh
 simp only[unbuildMany,unbuildTriple,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of ParkAMany.lean :: cached_wloop_many_eq
theorem cached_wloop_many_eq (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle:Program)
 (hacc:acc.length=161) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false) (zeroU:∀u∈hs,s.basis u=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (hk:k≤119) (ndhs:hs.Nodup) (hostlen:hs.length=k)
 (freshU:∀u∈hs,u∉cin::(src++acc++Z++bank))
 (oldNe:∀u∈hs,u≠q ∧ u≠r ∧ u≠p)
 (offF:q∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offI:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offIR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (offFU:∀u∈hs,u∉wires (buildTriple acc Z bank cin src q r p)) (offMU:∀u∈hs,u∉wires middle)
 (offIU:∀u∈hs,u∉wires (unbuildTriple acc Z bank cin src q r p))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (buildTriple acc Z bank cin src q r p) middle s m))
 (savedQ:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis q=cacheBit (regValue src s.basis))
 (savedR:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis r=cacheBit6 (regValue src s.basis))
 (savedP:(middleState (buildTriple acc Z bank cin src q r p) middle s m).basis p=cacheBit7 (regValue src s.basis)):
 run (buildMany k acc Z bank cin src hs q r p++middle++unbuildMany k acc Z bank cin src hs q r p) m s=
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s:=by
 let H:=regValue src s.basis
 have hf6:=hf _ (A161NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hsrc]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have tc:=buildMany_counts k acc Z bank cin src hs q r p hacc hsrc zl bl hk hostlen
 let t3:=middleState (buildTriple acc Z bank cin src q r p) middle s m
 let tm:=scatterState hs (bankValues 7 k H) t3
 have ready:WReady acc Z bank cin src H tm:=WReady_scatter acc Z bank cin src H hs (bankValues 7 k H) t3 freshU good
 have qoff:q∉hs:=by intro h;exact (oldNe q h).1 rfl
 have roff:r∉hs:=by intro h;exact (oldNe r h).2.1 rfl
 have poff:p∉hs:=by intro h;exact (oldNe p h).2.2 rfl
 have saved1:tm.basis q=cacheBit (regValue src tm.basis):=by
  rw[ready.2.1]
  exact (scatter_outside hs (bankValues 7 k H) t3 q qoff).trans savedQ
 have saved2:tm.basis r=cacheBit6 (regValue src tm.basis):=by
  rw[ready.2.1]
  exact (scatter_outside hs (bankValues 7 k H) t3 r roff).trans savedR
 have saved3:tm.basis p=cacheBit7 (regValue src tm.basis):=by
  rw[ready.2.1]
  exact (scatter_outside hs (bankValues 7 k H) t3 p poff).trans savedP
 have savedMany:hs.map tm.basis=bankValues 7 k (regValue src tm.basis):=by
  rw[ready.2.1]
  exact scatter_saved_map hs (bankValues 7 k H) t3 ndhs (by simp[bankValues,hostlen])
 have av:regValue acc tm.basis=4294968272*regValue src tm.basis:=by rw[ready.2.1];exact ready.1
 have forward:=buildMany_frame k acc Z bank cin src hs q r p hacc hsrc hf s
  (m.take (measurementCount (buildTriple acc Z bank cin src q r p))) hz hb hi ha zero zeroR fresh offF freshR offFR rq zeroP freshP offFP hk ndhs zeroU freshU offFU
 have inverse:=unbuildMany_frame k acc Z bank cin src hs q r p hacc hsrc hf tm
  (m.drop (measurementCount (buildTriple acc Z bank cin src q r p)+measurementCount middle))
  ready.2.2.1 ready.2.2.2.1 ready.2.2.2.2 av saved1 saved2 fresh offI freshR offIR rq saved3 freshP offIP pq pr hk ndhs hostlen savedMany freshU offIU
 exact cached_pair_many_eq (buildTriple acc Z bank cin src q r p) (buildMany k acc Z bank cin src hs q r p) middle
  (unbuildTriple acc Z bank cin src q r p) (unbuildMany k acc Z bank cin src hs q r p) hs (bankValues 7 k H)
  tc.2.1 offFU offMU offIU ndhs s m zeroU forward inverse

-- Width161 adaptation of ParkAMany.lean :: compiled_wloop_many_eq_set
theorem compiled_wloop_many_eq_set (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle newMiddle:Program)
 (hacc:acc.length=161) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (hk:k≤119) (ndhs:hs.Nodup) (hostlen:hs.length=k)
 (zeroU:∀u∈hs,s.basis u=false) (freshU:∀u∈hs,u∉cin::(src++acc++Z++bank))
 (oldNe:∀u∈hs,u≠q ∧ u≠r ∧ u≠p)
 (offFU:∀u∈hs,u∉wires (buildTriple acc Z bank cin src q r p))
 (offIU:∀u∈hs,u∉wires (unbuildTriple acc Z bank cin src q r p))
 (cert:ZeroSetDevelop.SRewrites hs middle newMiddle)
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m)):
 run (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p) m s=
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s:=by
 have ready:=triple_middle_ready acc Z bank cin src q r p middle hacc hsrc hf s m hz hb hi ha zero zeroR zeroP
  fresh freshR rq freshP pq pr offF offM offI offFR offMR offIR offFP offMP offIP good
 have middleEq:=cert.middle_eq hs middle newMiddle (buildTriple acc Z bank cin src q r p) s m zeroU offFU
 rw[←middleEq]at ready
 have newOff:∀u∈hs,u∉wires newMiddle:=cert.support hs middle newMiddle |>.2
 have eq:=cached_wloop_many_eq k acc Z bank cin src hs q r p newMiddle hacc hsrc hf s m hz hb hi ha zero zeroR zeroP zeroU
  fresh freshR rq freshP pq pr hk ndhs hostlen freshU oldNe offF offI offFR offIR offFP offIP offFU newOff offIU
  ready.1 ready.2.1 ready.2.2.1 ready.2.2.2
 have replaced:=cert.surround_eq hs middle newMiddle (buildTriple acc Z bank cin src q r p) (unbuildTriple acc Z bank cin src q r p) s m zeroU offFU
 exact eq.trans replaced

-- Width161 adaptation of ParkAMany.lean :: compiled_counts_set
theorem compiled_counts_set (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle newMiddle:Program)
 (ha:acc.length=161) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤119) (hostlen:hs.length=k)
 (cert:ZeroSetDevelop.SRewrites hs middle newMiddle):
 toffoliCount (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p)+k≤
 toffoliCount (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) ∧
 measurementCount (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p)=
 measurementCount (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) ∧
 Challenge.gateSlots (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p)+3*k≤
 Challenge.gateSlots (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p):=by
 have b:=buildMany_counts k acc Z bank cin src hs q r p ha hl hz hb hk hostlen
 have i:=unbuildMany_counts k acc Z bank cin src hs q r p ha hl hb hk hostlen
 have t:=cert.toffoli hs middle newMiddle
 have m:=cert.measurements hs middle newMiddle
 have slots:=cert.slots hs middle newMiddle
 simp only[toffoliCount_append,measurementCount_append,Challenge.gateSlots_append]
 exact ⟨by omega,by omega,by omega⟩

-- Width161 adaptation of FullLogic.lean :: triple_plain_eq
theorem triple_plain_eq (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire) (middle:Program)
 (hacc:acc.length=161) (hsrc:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hb:∀w∈bank,s.basis w=false)
 (hi:s.basis cin=false) (ha:regValue acc s.basis=0) (zero:s.basis q=false) (zeroR:s.basis r=false) (zeroP:s.basis p=false)
 (fresh:q∉cin::(src++acc++Z++bank)) (freshR:r∉cin::(src++acc++Z++bank)) (rq:r≠q)
 (freshP:p∉cin::(src++acc++Z++bank)) (pq:p≠q) (pr:p≠r)
 (offF:q∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offM:q∉wires middle)
 (offI:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src)) (offMR:r∉wires middle)
 (offIR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r)) (offMP:p∉wires middle)
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r))
 (good:WReady acc Z bank cin src (regValue src s.basis) (middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m)):
 run (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p) m s=
 run (A161NarrowAcc.build8 acc Z bank cin src++middle++A161SourceAdd.unbuild acc Z bank cin src) m s := by
 have a:=cached_wloop_triple_eq acc Z bank cin src q r p middle hacc hsrc hf s m hz hb hi ha zero zeroR zeroP fresh freshR rq freshP pq pr offF offM offI offFR offMR offIR offFP offMP offIP good
 have b:=cached_wloop_dual_eq acc Z bank cin src q r middle hacc hsrc hf s m hz hb hi ha zero zeroR fresh freshR rq offF offM offI offFR offMR offIR good
 exact a.trans b
#print axioms compiled_wloop_many_eq_set
#print axioms triple_plain_eq
end ECDSAAdd.Entrant.A161Carry

end

-- Component Fold
section
namespace ECDSAAdd.Entrant.A161Fold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop
 ControlLoan1589BFFold ThirdSavedCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

def accReg (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 161
abbrev cFlipK : Nat := A161Facts.K161

theorem acc_lengths (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 (accReg L).length=161 ∧ (accZ L).length=154 ∧ (accBank L).length=160 ∧ (wTemp L).length=33 :=
 ⟨by simp [accReg,hw.core.work],(ECDSAAdd.Entrant.acc_lengths L hw).2⟩

theorem accReg_work (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq:q∈accReg L) : q∈L.core.work :=
 List.mem_of_mem_take hq

theorem accReg_in (L : CuccaroStreamedSquareWideLayout) (q : Wire) (hq:q∈accReg L) : q∈L.wires := by
 have h := accReg_work L q hq
 simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]

theorem accReg_nodup (L : CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) : (accReg L).Nodup := by
 have h : ((ECDSAAdd.Entrant.accReg L).take 161).Nodup := (OwnDiagAll12Square.accReg_nodup L hn).take
 simpa [accReg,ECDSAAdd.Entrant.accReg,List.take_take] using h

theorem wTerms_fits (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 ∀f∈wTerms L,Acc.Fits (accReg L) (accZ L) (accBank L) L.core.cin 161 f := by
 intro f hf
 have old := ControlLoan1589BFFold.wTerms_fits L hw hn f hf
 have hl : f.src.length+f.shift<161 := by
  change f∈earlyHTerms (hiReg L) at hf
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> simp [Acc.earlyTerm,hiReg_length L hw]
 simpa [accReg,ECDSAAdd.Entrant.accReg,List.take_take] using
  (Acc.fits_prefix (ECDSAAdd.Entrant.accReg L) (accZ L) (accBank L) L.core.cin 163 161 f (by decide) old hl)

theorem flip_run (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉accReg L) (s:State) (m:List Bool) :
 (run (maskedConstant g (accReg L) cFlipK) m s).phase=s.phase ∧
 (∀q,q∉accReg L → (run (maskedConstant g (accReg L) cFlipK) m s).basis q=s.basis q) ∧
 regValue (accReg L) (run (maskedConstant g (accReg L) cFlipK) m s).basis=
 (if s.basis g then cFlipK-regValue (accReg L) s.basis else regValue (accReg L) s.basis) :=
 A161Facts.flip161_run _ (acc_lengths L hw).1 (accReg_nodup L hn) g hg s m

def wBuild (L : CuccaroStreamedSquareWideLayout) : Program :=
 A161NarrowAcc.build8 (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
def wUnbuild (L : CuccaroStreamedSquareWideLayout) : Program :=
 A161SourceAdd.unbuild (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
def aMiddle (L : CuccaroStreamedSquareWideLayout) (g:Wire) : Program :=
 maskedConstant g (accReg L) cFlipK++(qprogTq L.measuredCore SquareReduction.p++maskedConstant g (accReg L) cFlipK)
theorem workSplit (L : CuccaroStreamedSquareWideLayout) (q : Wire) :
    L.core.work.count q=(accReg L).count q+(L.core.work.drop 161).count q := by
  have a := congrArg (List.count q) (List.take_append_drop 161 L.core.work)
  simp only [List.count_append] at a
  simp only [accReg]
  omega

/-- Registers that the B body never changes outside its sub-steps. -/
theorem other_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (h : q∈hiReg L ∨ q∈L.core.work.drop 161 ∨ q∈L.foldPad ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) :
    q∉L.core.out ∧ q∉eReg L ∧ q∉accReg L := by
  have lc := layoutCount L hn q
  have ps := productSplit L q
  have ws := workSplit L q
  have ec := eReg_count L q
  have pos : 0<(hiReg L).count q ∨ 0<(L.core.work.drop 161).count q ∨ 0<L.foldPad.count q ∨
      0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
        L.core.modFlag,L.core.sumCarry].count q := by
    rcases h with h|h|h|h
    · exact Or.inl (List.count_pos_iff.mpr h)
    · exact Or.inr (Or.inl (List.count_pos_iff.mpr h))
    · exact Or.inr (Or.inr (Or.inl (List.count_pos_iff.mpr h)))
    · refine Or.inr (Or.inr (Or.inr (List.count_pos_iff.mpr ?_)))
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h ⊢
      tauto
  refine ⟨fun h1 => ?_,fun h1 => ?_,fun h1 => ?_⟩
  · have a := List.count_pos_iff.mpr h1; omega
  · have a := List.count_pos_iff.mpr h1; omega
  · have a := List.count_pos_iff.mpr h1; omega

theorem accReg_away (L : CuccaroStreamedSquareWideLayout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 161) :
    q∉accReg L := by
  intro bad
  have h := List.nodup_iff_count_le_one.mp hn q
  have a := List.count_pos_iff.mpr bad
  have b := List.count_pos_iff.mpr hq
  have e1 : (L.core.work.take 161).count q+(L.core.work.drop 161).count q=L.core.work.count q := by
    rw [←List.count_append,List.take_append_drop]
  simp only [accReg] at a
  simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
    List.count_append,List.count_cons,List.count_nil] at h b
  omega

theorem a_middle_good (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (O : Nat) (hO:O<SquareReduction.p)
    (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    let u:=middleState (wBuild L) (aMiddle L g) s m
    regValue (accReg L) u.basis=4294968272*regValue (hiReg L) s.basis ∧
    regValue (hiReg L) u.basis=regValue (hiReg L) s.basis ∧
    (∀w∈accZ L,u.basis w=false) ∧ (∀w∈accBank L,u.basis w=false) ∧ u.basis L.core.cin=false := by
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
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := 4294968272*regValue (hiReg L) base
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^161 := by
    show 4294968272*regValue (hiReg L) base<2^161
    norm_num at hH ⊢
    omega
  have hAK : A≤cFlipK := by unfold cFlipK A161Facts.K161; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^161 := by
    simp only [A']; split
    · unfold cFlipK A161Facts.K161; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hhi : regValue (hiReg L) b0=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => agree0 q (hiReg_product L q hq))
  have hbuild : Triple (SquareFrame (accReg L) b0 0) (wBuild L) (SquareFrame (accReg L) b0 A) := by
    have h := A161NarrowAcc.build8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) b0 hz hb clean.cin
    rw [hhi] at h
    exact h
  let mb := measurementCount (wBuild L)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (wBuild L) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis
      else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 161) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 161) (L.core.work.drop 161) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 161) u1.basis=0 :=
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
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis
      else regValue (accReg L) v.basis) at fl2
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
  have hhi2 : regValue (hiReg L) base2=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => (b2off q (prodNotOut q (hiReg_product L q hq))).trans
      (agree0 q (hiReg_product L q hq)))
  have offAcc (q : Wire) (hq:q∈hiReg L ∨ q∈L.foldPad ∨ q∈L.core.work.drop 161 ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉accReg L := by
    apply (other_away L hn q ?_).2.2
    tauto
  have source:regValue (hiReg L) v1.basis=regValue (hiReg L) base :=
    (regValue_congr _ _ _ (fun q hq=>frame2.2 q (offAcc q (Or.inl hq)))).trans hhi2
  have zv:∀q∈accZ L,v1.basis q=false := by
    intro q hq
    have na:q∉accReg L := by
      rcases accZ_mem L q hq with h|h
      · exact offAcc q (Or.inr (Or.inl h))
      · apply offAcc q
        have hd:(L.core.work.drop 161).drop 35=L.core.work.drop 196 := by simp [List.drop_drop]
        rw [←hd] at h
        exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
    exact (frame2.2 q na).trans (hz2 q hq)
  have bv:∀q∈accBank L,v1.basis q=false := by
    intro q hq
    exact (frame2.2 q (offAcc q (Or.inr (Or.inl (List.mem_of_mem_take hq))))).trans (hb2 q hq)
  have iv:v1.basis L.core.cin=false :=
    (frame2.2 _ (offAcc _ (by simp))).trans hi2
  have midEq:middleState (wBuild L) (aMiddle L g) s m=v1 := by
    simp only [middleState,aMiddle,run_append,measurementCount_append,
      (maskedConstant_counts _ _ _).2,Nat.zero_add,Nat.add_zero,List.take_zero,List.drop_zero,List.drop_drop]
    dsimp only [v1,v,u1,u,m3,m2,m1,mc,mb,mk]
    simp only [(maskedConstant_counts _ _ _).2,List.take_zero,List.drop_zero,Nat.add_zero,List.take_take,Nat.min_self,List.drop_take,Nat.sub_self]
  rw [midEq]
  exact ⟨frame2.1.trans (by rw [hhi]),source.trans hhi.symm,zv,bv,iv⟩
#print axioms a_middle_good
end ECDSAAdd.Entrant.A161Fold

end

-- Component InputEq
section
namespace ECDSAAdd.Entrant.A161Facts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
set_option linter.unusedSimpArgs false
theorem trimHighMasks_append (P Q : Program) :
 trimHighMasks (P++Q)=trimHighMasks P++trimHighMasks Q := List.filter_append P Q

theorem trimHighMasks_eq (P : Program) (hg : 4113∉wires P) : trimHighMasks P=P := by
 induction P with
 | nil => rfl
 | cons i P ih =>
   have hgi : 4113∉i.wires := fun h => hg (Finset.mem_union_left _ h)
   have hgp : 4113∉wires P := fun h => hg (Finset.mem_union_right _ h)
   have h1 : i≠.CX 4113 4662 := by intro e;subst i;exact hgi (by simp [Instr.wires])
   have h2 : i≠.CX 4113 4663 := by intro e;subst i;exact hgi (by simp [Instr.wires])
   have keep : decide (i≠.CX 4113 4662 ∧ i≠.CX 4113 4663)=true := by simp [h1,h2]
   simp only [trimHighMasks,List.filter_cons,keep,ite_true]
   exact congrArg (List.cons i) (ih hgp)

set_option maxRecDepth 100000
set_option maxHeartbeats 500000000

theorem trim_mask :
 trimHighMasks (maskedConstant FullPadSupport.c (accReg FullPadSupport.L)
   OwnDiagAll12Square.cFlipK)=maskedConstant FullPadSupport.c (acc161 FullPadSupport.L) K161 := by
 rfl

theorem trim_core_general (K : MeasuredCanonicalModLayout) (p : Nat)
 (free : 4113∉K.wires.toFinset) : trimHighMasks (qprogTq K p)=qprogTq K p :=
 trimHighMasks_eq (qprogTq K p) (fun h => free (QCore.qprog_supportTq K p h))

theorem trim_core : trimHighMasks (qprogTq FullPadSupport.L.measuredCore SquareReduction.p)=
 qprogTq FullPadSupport.L.measuredCore SquareReduction.p := by
 have freeList : 4113∉FullPadSupport.L.measuredCore.wires := by decide
 have freeSet : 4113∉FullPadSupport.L.measuredCore.wires.toFinset := by
  simpa only [List.mem_toFinset] using freeList
 exact trim_core_general FullPadSupport.L.measuredCore SquareReduction.p freeSet

theorem input_eq : p161=aMiddle161 FullPadSupport.L FullPadSupport.c := by
 let A := maskedConstant FullPadSupport.c (accReg FullPadSupport.L) OwnDiagAll12Square.cFlipK
 let Q := qprogTq FullPadSupport.L.measuredCore SquareReduction.p
 let N := maskedConstant FullPadSupport.c (acc161 FullPadSupport.L) K161
 calc
  p161=trimHighMasks (InverseCarryDevelop.aMiddle FullPadSupport.L FullPadSupport.c) :=
   congrArg trimHighMasks ParkAStagedProof.input_eq
  _ = trimHighMasks A++(trimHighMasks Q++trimHighMasks A) :=
   (trimHighMasks_append A (Q++A)).trans
    (congrArg (fun t => trimHighMasks A++t) (trimHighMasks_append Q A))
  _ = N++(Q++N) :=
   congrArg₂ (fun (P R : Program) => P++R) trim_mask
    (congrArg₂ (fun (P R : Program) => P++R) trim_core trim_mask)
  _ = aMiddle161 FullPadSupport.L FullPadSupport.c := rfl

#print axioms input_eq

end ECDSAAdd.Entrant.A161Facts

end

-- Component Compile95
section
namespace ECDSAAdd.Entrant.A161Facts
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
theorem compiled95 : (ZeroSetDevelop.compileS? (loans95 FullPadSupport.L) p161).isSome=true := by
 decide +kernel

attribute [local irreducible] ZeroSetDevelop.compileS?

theorem actual_compiled95 :
 (ZeroSetDevelop.compileS? (loans95 FullPadSupport.L) (aMiddle161 FullPadSupport.L FullPadSupport.c)).isSome=true :=
 (congrArg (fun P : Program => (ZeroSetDevelop.compileS? (loans95 FullPadSupport.L) P).isSome) input_eq).symm.trans compiled95

#print axioms actual_compiled95
#print axioms compiled95
end ECDSAAdd.Entrant.A161Facts

end

-- Component KnownTail
section
-- Width161 specialization of retained CodexNarrowTail resource proofs.
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.A161KnownTail
open Arithmetic


theorem clear_sub32_range (H : Nat) (hH : H<2^128) :
    H≤4294968272*H/4294967296 ∧
    4294968272*H/4294967296-H=976*H/4294967296 ∧
    4294968272*H/4294967296-H<2^106 := by
  norm_num at hH ⊢
  omega

theorem clear_sub10_range (H : Nat) (hH : H<2^128) :
    H≤1040*H/1024 ∧ 1040*H/1024-H=H/64 ∧ 1040*H/1024-H<2^122 := by
  norm_num at hH ⊢
  omega

/-! Narrow H accumulator for a source of at most 128 bits.

`earlyHTerms src` accumulates `(2^32+976)*H` with `H < 2^128`. The generic early prefix runs its two
signed steps on 141 accumulator bits and the final `2^32` step on all 161 bits, which is sized for
130-bit sources. For a 128-bit source `1040*H < 2^139` and `(2^32+976)*H < 2^161`, so the same
operations run on 139 and 161 bits: the top two carries of each of the three adders are never produced
(two Toffolis and two measurements less per adder). -/

def pre8 (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)++
    Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src false 10)++
    CodexNarrowSub.accSub (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)

def build8 (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  pre8 acc Z bank cin src++Acc.op (acc.take 161) Z bank cin 161 false (Acc.earlyTerm src false 32)

def unbuild8 (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)++
    Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)++
    CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)++
    Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)

theorem terms_mem (src : List Wire) :
    Acc.earlyTerm src false 4∈earlyHTerms src ∧ Acc.earlyTerm src false 10∈earlyHTerms src ∧
      Acc.earlyTerm src true 6∈earlyHTerms src ∧ Acc.earlyTerm src false 32∈earlyHTerms src := by
  simp [earlyHTerms]

                                                                             
                                                   
                                                           
                                                                            
                           
                                                               
                                                                 
                          
                       
                          
                           
                            
                            
                                                                                                      
                                                                                              
                                                              
                                                 
                                                                               
                                           
                                                                                           
                                                                                                         
                                                                                            
                                                                                     
                                       
               
           
                   
           
                                                   
                                                                                      
                                          
                                                                                                        
                                                                                                                                  
                                                                               
                                                                                      
                                                                                   
                                       
               
           
                   
           
                                                  
                                                                               
                                                 
                                                                                           
                                                                                                          
                                                                                            
                                                                                            
                                       
               
           
                   
           
                                        

theorem unbuild8_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuild8 acc Z bank cin src)
      (SquareFrame acc base 0) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have hf10 := hf _ tm.2.1
  have hf6 := hf _ tm.2.2.1
  have hf32 := hf _ tm.2.2.2
  let H := regValue src base
  have hH : H<2^128 := lt_of_lt_of_le (regValue_lt src base) (Nat.pow_le_pow_right (by norm_num) hsrc)
  have top : Triple (SquareFrame acc base (4294968272*H))
      (CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32))
      (SquareFrame acc base (976*H)) := by
    have h := CodexKnownOnesTail.accSub_prefix_triple acc Z bank cin 161 161 106 (Acc.earlyTerm src false 32) hacc
      (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega)
      (by norm_num [Acc.earlyTerm]) base hz hb hi (4294968272*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (clear_sub32_range H hH).2.2)
    have value : Acc.step base true (4294968272*H) (Acc.earlyTerm src false 32)=976*H := by
      have e : regValue src base*2^32=4294967296*H := by dsimp only [H]; ring
      simp only [Acc.step,Acc.earlyTerm,if_true]
      rw [e]
      omega
    rw [value] at h
    exact h
  have add : Triple (SquareFrame acc base (976*H))
      (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6))
      (SquareFrame acc base (1040*H)) := by
    have h := Acc.op_prefix_triple acc Z bank cin 161 139 (Acc.earlyTerm src true 6) hacc
      (by norm_num [Acc.earlyTerm]) hf6 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (976*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : Acc.step base false (976*H) (Acc.earlyTerm src true 6)=1040*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have sub : Triple (SquareFrame acc base (1040*H))
      (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10))
      (SquareFrame acc base (16*H)) := by
    have h := CodexKnownOnesTail.accSub_prefix_triple acc Z bank cin 161 139 122 (Acc.earlyTerm src false 10) hacc
      (by norm_num [Acc.earlyTerm]) hf10 (by simp only [Acc.earlyTerm]; omega)
      (by norm_num [Acc.earlyTerm]) base hz hb hi (1040*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (clear_sub10_range H hH).2.2)
    have value : Acc.step base true (1040*H) (Acc.earlyTerm src false 10)=16*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have seed := Acc.seed_triple acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4 base hz
    (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
  exact ((top.seq add).seq sub).seq seed

theorem narrowLen (Z bank : List Wire) (n : Nat) (f : MeasuredSquareFold)
    (hf : Acc.FitsLen Z bank 161 f) (hn : n≤161) (hl : f.src.length+f.shift<n) :
    Acc.FitsLen Z bank n f := by
  refine ⟨hl,?_,?_⟩
  · have h := hf.zpad; omega
  · have h := hf.bankLen; omega

theorem build8_counts (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.FitsLen Z bank 161 f) :
    (toffoliCount (build8 acc Z bank cin src)=387 ∧ measurementCount (build8 acc Z bank cin src)=388) ∧
    (toffoliCount (unbuild8 acc Z bank cin src)=358 ∧
      measurementCount (unbuild8 acc Z bank cin src)=388) := by
  have tm := terms_mem src
  have l139 : (acc.take 139).length=139 := by simp [List.length_take,hacc]
  have l161 : (acc.take 161).length=161 := by simp [List.length_take,hacc]
  have seed := Acc.seed_counts acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc (hf _ tm.1)
  have f10 := narrowLen Z bank 139 _ (hf _ tm.2.1) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have f6 := narrowLen Z bank 139 _ (hf _ tm.2.2.1) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have f32 := narrowLen Z bank 161 _ (hf _ tm.2.2.2) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have a0 := Acc.op_counts (acc.take 139) Z bank cin 139 false _ l139 f10
  have a1 := Acc.op_counts (acc.take 139) Z bank cin 139 true _ l139 f10
  have b0 := Acc.op_counts (acc.take 139) Z bank cin 139 false _ l139 f6
  have b1 := Acc.op_counts (acc.take 139) Z bank cin 139 true _ l139 f6
  have c0 := Acc.op_counts (acc.take 161) Z bank cin 161 false _ l161 f32
  have c1 := Acc.op_counts (acc.take 161) Z bank cin 161 true _ l161 f32
  have bk := CodexNarrowSub.accSub_counts (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6) l139 f6 (by norm_num [Acc.earlyTerm])
  rw [b1.1,b1.2] at bk
  have ak := CodexNarrowTailResource.accSub_counts 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10) l139 f10 (by norm_num [Acc.earlyTerm])
  have ck := CodexNarrowTailResource.accSub_counts 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32) l161 f32 (by norm_num [Acc.earlyTerm])
  simp only [build8,unbuild8,pre8,toffoliCount_append,measurementCount_append,
    seed.1,seed.2,a0.1,a0.2,a1.1,a1.2,b0.1,b0.2,b1.1,b1.2,c0.1,c0.2,c1.1,c1.2]
  norm_num [Acc.earlyTerm] at bk ak ck ⊢
  omega

theorem build8_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f) :
    wires (build8 acc Z bank cin src)⊆(cin::(src++acc++Z++bank)).toFinset ∧
    wires (unbuild8 acc Z bank cin src)⊆(cin::(src++acc++Z++bank)).toFinset := by
  have tm := terms_mem src
  have seed := Acc.seed_support acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc (hf _ tm.1)
  have a0 := Acc.op_prefix_support acc Z bank cin 161 139 (Acc.earlyTerm src false 10) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have a1 := Acc.op_prefix_support acc Z bank cin 161 139 (Acc.earlyTerm src false 10) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have b0 := Acc.op_prefix_support acc Z bank cin 161 139 (Acc.earlyTerm src true 6) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have b1 := Acc.op_prefix_support acc Z bank cin 161 139 (Acc.earlyTerm src true 6) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have c0 := Acc.op_prefix_support acc Z bank cin 161 161 (Acc.earlyTerm src false 32) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) false
  have c1 := Acc.op_prefix_support acc Z bank cin 161 161 (Acc.earlyTerm src false 32) hacc
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) true
  have fit6 := Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src true 6) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega)
  have bk := CodexNarrowSub.accSub_support (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)
    (by simp [List.length_take,hacc]) fit6.toFitsLen (by norm_num [Acc.earlyTerm])
  have b1 := bk.trans b1
  have fit10 := Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src false 10) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega)
  have new10 := CodexNarrowTailResource.accSub_support 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)
    (by simp [List.length_take,hacc]) fit10.toFitsLen (by norm_num [Acc.earlyTerm])
  have a1 := new10.trans a1
  have fit32 := Acc.fits_prefix acc Z bank cin 161 161 (Acc.earlyTerm src false 32) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega)
  have new32 := CodexNarrowTailResource.accSub_support 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)
    (by simp [List.length_take,hacc]) fit32.toFitsLen (by norm_num [Acc.earlyTerm])
  have c1 := new32.trans c1
  simp only [Acc.earlyTerm] at seed a0 a1 b0 b1 c0 c1
  simp only [build8,unbuild8,pre8,wires_append,Finset.union_subset_iff]
  exact ⟨⟨⟨⟨seed,a0⟩,b1⟩,c0⟩,⟨⟨⟨c1,b0⟩,a1⟩,seed⟩⟩

theorem build8_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f) :
    GatePhysical (build8 acc Z bank cin src) ∧ GatePhysical (unbuild8 acc Z bank cin src) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have seed : GatePhysical (Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)) := by
    have len := Acc.fits_lengths acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4.toFitsLen
    have nd := Acc.fits_nodup acc Z bank cin 161 (Acc.earlyTerm src false 4) hf4
    exact copyRegister_physical none _ _
      ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
  have a0 := Acc.op_prefix_physical acc Z bank cin 161 139 (Acc.earlyTerm src false 10)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have a1 := Acc.op_prefix_physical acc Z bank cin 161 139 (Acc.earlyTerm src false 10)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have b0 := Acc.op_prefix_physical acc Z bank cin 161 139 (Acc.earlyTerm src true 6)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have b1 := Acc.op_prefix_physical acc Z bank cin 161 139 (Acc.earlyTerm src true 6)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have c0 := Acc.op_prefix_physical acc Z bank cin 161 161 (Acc.earlyTerm src false 32)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) false
  have c1 := Acc.op_prefix_physical acc Z bank cin 161 161 (Acc.earlyTerm src false 32)
    (by norm_num [Acc.earlyTerm]) (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) true
  have fit6 := Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src true 6) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega)
  have b1 := CodexNarrowSub.accSub_physical (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)
    (by simp [List.length_take,hacc]) fit6 (by norm_num [Acc.earlyTerm])
  have fit10 := Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src false 10) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega)
  have new10 := CodexKnownOnesTail.accSub_physical 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)
    (by simp [List.length_take,hacc]) fit10 (by norm_num [Acc.earlyTerm])
  have a1 := new10
  have fit32 := Acc.fits_prefix acc Z bank cin 161 161 (Acc.earlyTerm src false 32) (by norm_num [Acc.earlyTerm])
    (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega)
  have new32 := CodexKnownOnesTail.accSub_physical 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)
    (by simp [List.length_take,hacc]) fit32 (by norm_num [Acc.earlyTerm])
  have c1 := new32
  simp only [build8,unbuild8,pre8,gatePhysical_append]
  exact ⟨⟨⟨⟨seed,a0⟩,b1⟩,c0⟩,⟨⟨⟨c1,b0⟩,a1⟩,seed⟩⟩

theorem build8_gateSlots (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length≤128)
    (hf : ∀f∈earlyHTerms src,Acc.FitsLen Z bank 161 f) :
    Challenge.gateSlots (build8 acc Z bank cin src)≤4*(14*161) ∧
    Challenge.gateSlots (unbuild8 acc Z bank cin src)≤4*(14*161) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have seed : Challenge.gateSlots (Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4))≤161 := by
    have l := Acc.fits_lengths acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4
    have h : Challenge.gateSlots (Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4))≤
        (Acc.tx Z 161 (Acc.earlyTerm src false 4)).length := by
      simp [Acc.seedOp,Baselines.copyRegister_gateSlots]
    rw [l.1,l.2.2] at h
    exact h.trans (by omega)
  have op (n : Nat) (hn : n≤161) (f : MeasuredSquareFold) (hff : Acc.FitsLen Z bank 161 f)
      (hl : f.src.length+f.shift<n) (neg : Bool) :
      Challenge.gateSlots (Acc.op (acc.take n) Z bank cin n neg f)≤14*n := by
    have len : (acc.take n).length=n := by simp [List.length_take,hacc]; omega
    have h := Acc.op_gateSlots (acc.take n) Z bank cin n neg f
    have l := Acc.fits_lengths (acc.take n) Z bank cin n f len (narrowLen Z bank n f hff hn hl)
    rw [l.1,l.2.2] at h
    exact h.trans (by omega)
  have a0 := op 139 (by norm_num [Acc.earlyTerm]) _ (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have a1 := op 139 (by norm_num [Acc.earlyTerm]) _ (hf _ tm.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have b0 := op 139 (by norm_num [Acc.earlyTerm]) _ (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) false
  have b1 := op 139 (by norm_num [Acc.earlyTerm]) _ (hf _ tm.2.2.1) (by simp only [Acc.earlyTerm]; omega) true
  have c0 := op 161 (by norm_num [Acc.earlyTerm]) _ (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) false
  have c1 := op 161 (by norm_num [Acc.earlyTerm]) _ (hf _ tm.2.2.2) (by simp only [Acc.earlyTerm]; omega) true
  have fit6 := narrowLen Z bank 139 _ (hf _ tm.2.2.1) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have bk := CodexNarrowSub.accSub_slots (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6)
    (by simp [List.length_take,hacc]) fit6 (by norm_num [Acc.earlyTerm])
  have b1 := bk.trans b1
  have fit10 := narrowLen Z bank 139 _ (hf _ tm.2.1) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have new10 := CodexNarrowTailResource.accSub_slots 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)
    (by simp [List.length_take,hacc]) fit10 (by norm_num [Acc.earlyTerm])
  have a1 := new10.trans a1
  have fit32 := narrowLen Z bank 161 _ (hf _ tm.2.2.2) (by norm_num [Acc.earlyTerm]) (by simp only [Acc.earlyTerm]; omega)
  have new32 := CodexNarrowTailResource.accSub_slots 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)
    (by simp [List.length_take,hacc]) fit32 (by norm_num [Acc.earlyTerm])
  have c1 := new32.trans c1
  simp only [build8,unbuild8,pre8,Challenge.gateSlots_append]
  omega

end ECDSAAdd.Entrant.A161KnownTail

#print axioms ECDSAAdd.Entrant.A161KnownTail.build8_counts

end

-- Component SourceResources
section
-- Width161 specializations of retained optimized inverse resource proofs.
set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.A161SourceTail
open SourceTailDevelop
open Arithmetic A161KnownTail

def unbuild (acc Z bank : List Wire) (cin : Wire) (src : List Wire) : Program :=
  CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32)++
    Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)++
    tail acc Z bank cin src++Acc.seedOp acc Z 161 (Acc.earlyTerm src false 4)

theorem unbuild_triple (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (base : BasisState) (hz : ∀q∈Z,base q=false) (hb : ∀q∈bank,base q=false)
    (hi : base cin=false) :
    Triple (SquareFrame acc base (4294968272*regValue src base)) (unbuild acc Z bank cin src)
      (SquareFrame acc base 0) := by
  have tm := terms_mem src
  have hf4 := hf _ tm.1
  have hf10 := hf _ tm.2.1
  have hf6 := hf _ tm.2.2.1
  have hf32 := hf _ tm.2.2.2
  let H := regValue src base
  have hH : H<2^128 := by have h:=regValue_lt src base;rw [hsrc] at h;exact h
  have top : Triple (SquareFrame acc base (4294968272*H))
      (CodexKnownOnesTail.accSub 106 (acc.take 161) Z bank cin 161 (Acc.earlyTerm src false 32))
      (SquareFrame acc base (976*H)) := by
    have h := CodexKnownOnesTail.accSub_prefix_triple acc Z bank cin 161 161 106 (Acc.earlyTerm src false 32) hacc
      (by norm_num [Acc.earlyTerm]) hf32 (by simp only [Acc.earlyTerm]; omega)
      (by norm_num [Acc.earlyTerm]) base hz hb hi (4294968272*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm];dsimp [H];omega)
      (by simpa only [Acc.earlyTerm] using (clear_sub32_range H hH).2.2)
    have value : Acc.step base true (4294968272*H) (Acc.earlyTerm src false 32)=976*H := by
      have e : regValue src base*2^32=4294967296*H := by dsimp only [H]; ring
      simp only [Acc.step,Acc.earlyTerm,if_true]
      rw [e]
      omega
    rw [value] at h
    exact h
  have add : Triple (SquareFrame acc base (976*H))
      (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6))
      (SquareFrame acc base (1040*H)) := by
    have h := Acc.op_prefix_triple acc Z bank cin 161 139 (Acc.earlyTerm src true 6) hacc
      (by norm_num [Acc.earlyTerm]) hf6 (by simp only [Acc.earlyTerm]; omega) base hz hb hi false (976*H)
      (by norm_num at hH ⊢;omega) (by norm_num [Acc.earlyTerm] at hH ⊢;dsimp [H] at *;omega)
    have value : Acc.step base false (976*H) (Acc.earlyTerm src true 6)=1040*H := by
      norm_num [Acc.step,Acc.earlyTerm]
      dsimp [H]
      omega
    rw [value] at h
    exact h
  have sub : Triple (SquareFrame acc base (1040*H)) (tail acc Z bank cin src)
      (SquareFrame acc base (16*H)) := tail_triple acc Z bank cin src hacc hsrc hf10 base hz hb hi
  have seed := Acc.seed_triple acc Z bank cin 161 (Acc.earlyTerm src false 4) hacc hf4 base hz
    (16*H) 0 (Or.inr (by simp [Acc.earlyTerm,H,Nat.mul_comm]))
  exact ((top.seq add).seq sub).seq seed


                                                                              
                                                   
                                                           
                                                                                          
                                                                                          
                                                                                                    
                                                                                                     
                                                                                   
                                                                                                          
                                
                            
          
                     
                                                                                            
                                              
#print axioms unbuild_triple
                            
end ECDSAAdd.Entrant.A161SourceTail


namespace ECDSAAdd.Entrant.A161SourceAdd
open SourceAddFourDevelop
open Arithmetic A161KnownTail
theorem add_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : Acc.FitsLen Z bank 161 (Acc.earlyTerm src true 6)) :
    toffoliCount (add acc Z bank cin src)+4=
      toffoliCount (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)) ∧
    measurementCount (add acc Z bank cin src)=
      measurementCount (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)) ∧
    wires (add acc Z bank cin src)⊆
      wires (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)) ∧
    Challenge.gateSlots (add acc Z bank cin src)≤
      Challenge.gateSlots (Acc.op (acc.take 139) Z bank cin 139 false (Acc.earlyTerm src true 6)) := by
  have fit:=A161KnownTail.narrowLen Z bank 139 (Acc.earlyTerm src true 6) hf (by decide)
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 5≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 132).length=132 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have h:=program_resources src Z ((acc.take 139).drop 6) (bank.take 132) cin (by omega) zl
    (by simp [hacc,hsrc]) (by simp [hacc,bl])
  simpa [add,Acc.op,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using h

theorem add_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 161 (Acc.earlyTerm src true 6)) :
    GatePhysical (add acc Z bank cin src) := by
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src true 6) (by decide) hf
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 5≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 132).length=132 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 (Acc.earlyTerm src true 6) fit
  have nd' : (cin::((src++Z.take 5)++(acc.take 139).drop 6++bank.take 132)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using nd
  exact program_physical src Z ((acc.take 139).drop 6) (bank.take 132) cin (by omega) zl (by simp [hacc,hsrc]) (by simp [hacc,bl]) nd'


#print axioms add_resources
#print axioms add_physical
end ECDSAAdd.Entrant.A161SourceAdd


namespace ECDSAAdd.Entrant.A161SourceTail
open SourceTailDevelop
open Arithmetic A161KnownTail

theorem tail_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : Acc.FitsLen Z bank 161 (Acc.earlyTerm src false 10)) :
    toffoliCount (tail acc Z bank cin src)+121=
      toffoliCount (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)) ∧
    measurementCount (tail acc Z bank cin src)=
      measurementCount (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)) ∧
    wires (tail acc Z bank cin src)⊆
      wires (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)) ∧
    Challenge.gateSlots (tail acc Z bank cin src)≤
      Challenge.gateSlots (CodexKnownOnesTail.accSub 122 (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10)) := by
  have fit:=A161KnownTail.narrowLen Z bank 139 (Acc.earlyTerm src false 10) hf (by decide)
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 1≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 128).length=128 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have h:=program_resources src Z ((acc.take 139).drop 10) (bank.take 128) cin hsrc zl
    (by simp [hacc]) bl
  simpa [tail,CodexKnownOnesTail.accSub,Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using h

theorem unbuild_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.FitsLen Z bank 161 f) :
    toffoliCount (unbuild acc Z bank cin src)=237 ∧ measurementCount (unbuild acc Z bank cin src)=388 ∧
    wires (unbuild acc Z bank cin src)⊆wires (A161KnownTail.unbuild8 acc Z bank cin src) ∧
    Challenge.gateSlots (unbuild acc Z bank cin src)≤Challenge.gateSlots (A161KnownTail.unbuild8 acc Z bank cin src) := by
  have t:=tail_resources acc Z bank cin src hacc hsrc (hf _ (A161KnownTail.terms_mem src).2.1)
  have old:=(A161KnownTail.build8_counts acc Z bank cin src hacc (by omega) hf).2
  have dt : toffoliCount (unbuild acc Z bank cin src)+121=toffoliCount (A161KnownTail.unbuild8 acc Z bank cin src) := by
    simp only [unbuild,A161KnownTail.unbuild8,toffoliCount_append]
    omega
  have dm : measurementCount (unbuild acc Z bank cin src)=measurementCount (A161KnownTail.unbuild8 acc Z bank cin src) := by
    simp only [unbuild,A161KnownTail.unbuild8,measurementCount_append]
    omega
  refine ⟨by omega,by omega,?_,?_⟩
  · simp only [unbuild,A161KnownTail.unbuild8,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) t.2.2.1) (Finset.Subset.refl _)
  · simp only [unbuild,A161KnownTail.unbuild8,Challenge.gateSlots_append]
    omega

theorem tail_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : Acc.Fits acc Z bank cin 161 (Acc.earlyTerm src false 10)) :
    GatePhysical (tail acc Z bank cin src) := by
  have fit:=Acc.fits_prefix acc Z bank cin 161 139 (Acc.earlyTerm src false 10) (by decide) hf
    (by simp [Acc.earlyTerm,hsrc])
  have zl : 1≤Z.length := by simpa [Acc.earlyTerm,hsrc] using fit.zpad
  have bl : (bank.take 128).length=128 := by
    have h:=fit.bankLen
    simp only [Acc.earlyTerm] at h
    simp only [List.length_take]
    omega
  have nd:=Acc.fits_nodup (acc.take 139) Z bank cin 139 (Acc.earlyTerm src false 10) fit
  have nd' : (cin::((src++Z.take 1)++(acc.take 139).drop 10++bank.take 128)).Nodup := by
    simpa [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,hsrc] using nd
  exact program_physical src Z ((acc.take 139).drop 10) (bank.take 128) cin hsrc zl (by simp [hacc]) bl nd'

theorem unbuild_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f) :
    GatePhysical (unbuild acc Z bank cin src) := by
  have old:=(A161KnownTail.build8_physical acc Z bank cin src hacc (by omega) hf).2
  have new:=tail_physical acc Z bank cin src hacc hsrc (hf _ (A161KnownTail.terms_mem src).2.1)
  simp only [unbuild,A161KnownTail.unbuild8,gatePhysical_append] at old ⊢
  exact ⟨⟨⟨old.1.1.1,old.1.1.2⟩,new⟩,old.2⟩
#print axioms tail_resources
#print axioms unbuild_resources
#print axioms unbuild_physical
end ECDSAAdd.Entrant.A161SourceTail


namespace ECDSAAdd.Entrant.A161SourceAdd
open SourceAddFourDevelop
open Arithmetic A161KnownTail

theorem unbuild_resources (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.FitsLen Z bank 161 f) :
    toffoliCount (unbuild acc Z bank cin src)=233 ∧ measurementCount (unbuild acc Z bank cin src)=388 ∧
    wires (unbuild acc Z bank cin src)⊆wires (A161KnownTail.unbuild8 acc Z bank cin src) ∧
    Challenge.gateSlots (unbuild acc Z bank cin src)≤Challenge.gateSlots (A161KnownTail.unbuild8 acc Z bank cin src) := by
  have a:=add_resources acc Z bank cin src hacc hsrc (hf _ (terms_mem src).2.2.1)
  have old:=A161SourceTail.unbuild_resources acc Z bank cin src hacc hsrc hf
  have dt : toffoliCount (unbuild acc Z bank cin src)+4=toffoliCount (A161SourceTail.unbuild acc Z bank cin src) := by
    simp only [unbuild,A161SourceTail.unbuild,toffoliCount_append]
    omega
  have dm : measurementCount (unbuild acc Z bank cin src)=measurementCount (A161SourceTail.unbuild acc Z bank cin src) := by
    simp only [unbuild,A161SourceTail.unbuild,measurementCount_append]
    omega
  refine ⟨by omega,by omega,?_,?_⟩
  · apply Finset.Subset.trans _ old.2.2.1
    simp only [unbuild,A161SourceTail.unbuild,wires_append]
    exact Finset.union_subset_union
      (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) a.2.2.1)
        (Finset.Subset.refl _)) (Finset.Subset.refl _)
  · have h : Challenge.gateSlots (unbuild acc Z bank cin src)≤Challenge.gateSlots (A161SourceTail.unbuild acc Z bank cin src) := by
      simp only [unbuild,A161SourceTail.unbuild,Challenge.gateSlots_append]
      omega
    exact h.trans old.2.2.2

theorem unbuild_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire)
    (hacc : acc.length=161) (hsrc : src.length=128)
    (hf : ∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f) :
    GatePhysical (unbuild acc Z bank cin src) := by
  have old:=A161SourceTail.unbuild_physical acc Z bank cin src hacc hsrc hf
  have a:=add_physical acc Z bank cin src hacc hsrc (hf _ (terms_mem src).2.2.1)
  simp only [unbuild,A161SourceTail.unbuild,gatePhysical_append] at old ⊢
  exact ⟨⟨⟨old.1.1.1,a⟩,old.1.2⟩,old.2⟩
#print axioms unbuild_resources
#print axioms unbuild_physical
end ECDSAAdd.Entrant.A161SourceAdd

end

-- Component Ambient
section
namespace ECDSAAdd.Entrant.A161KnownTail
open Arithmetic
theorem build8_eq (acc Z bank : List Wire) (cin : Wire) (src : List Wire) :
 build8 acc Z bank cin src=A161NarrowAcc.build8 acc Z bank cin src := rfl
end ECDSAAdd.Entrant.A161KnownTail

namespace ECDSAAdd.Entrant.A161Carry
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop
 ThirdSavedCarryDevelop FourthASavedCarryDevelop ManyACarryDevelop ControlLoan1589BFFold ZeroReadDevelop CodexNarrowTail
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires
-- Width161 specialization of MainPart04Base.lean :: buildCached_physical
theorem buildCached_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
    (off:q∉wires (A161NarrowAcc.build8 acc Z bank cin src))
    (physical:GatePhysical (A161NarrowAcc.build8 acc Z bank cin src)) :
    GatePhysical (buildCached acc Z bank cin src q) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have pp:=physical
  rw [build_split,gatePhysical_append,gatePhysical_append] at pp
  have qo:q∉wires (CodexNarrowSub.program (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin) := by
    intro h;apply off
    simp only [build_split,CodexNarrowSub.accSub,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=cachedSub_resources _ _ _ cin q (by omega) (by omega) (by omega) qo pp.1.2
  simp only [buildCached,gatePhysical_append]
  exact ⟨⟨pp.1.1,sub.2⟩,pp.2⟩

-- Width161 specialization of MainPart04Base.lean :: unbuildConsumed_physical
theorem unbuildConsumed_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length)
    (off:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
    (physical:GatePhysical (A161SourceAdd.unbuild acc Z bank cin src)) :
    GatePhysical (unbuildConsumed acc Z bank cin src q) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:5≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have pp:=physical
  rw [unbuild_split,gatePhysical_append,gatePhysical_append] at pp
  have qo:q∉wires (SourceAddFourDevelop.program src Z ((acc.take 139).drop 6) (bank.take 132) cin) := by
    intro h;apply off
    simp only [unbuild_split,A161SourceAdd.add,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=consumedAdd_resources src Z ((acc.take 139).drop 6) (bank.take 132) cin q (by omega) hy hc qo pp.1.2
  simp only [unbuildConsumed,gatePhysical_append]
  exact ⟨⟨pp.1.1,sub.2⟩,pp.2⟩

-- Width161 specialization of MainPart04Base.lean :: wloop_original_off
theorem wloop_original_off (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
    (fresh:q∉cin::(src++acc++Z++bank)) :
    q∉wires (A161NarrowAcc.build8 acc Z bank cin src) ∧
    q∉wires (A161SourceAdd.unbuild acc Z bank cin src) := by
  have support:=A161KnownTail.build8_support acc Z bank cin src ha (by omega) hf
  rw [A161KnownTail.build8_eq] at support
  have inv:=A161SourceAdd.unbuild_resources acc Z bank cin src ha hs
    (fun f h=>(hf f h).toFitsLen)
  exact ⟨fun h=>fresh (List.mem_toFinset.mp (support.1 h)),
    fun h=>fresh (List.mem_toFinset.mp (support.2 (inv.2.2.1 h)))⟩

-- Width161 specialization of MainPart04Base.lean :: buildDual_support
theorem buildDual_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    wires (buildDual acc Z bank cin src q r)⊆insert r (wires (buildCached acc Z bank cin src q)) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have sub:=cachedSubDual_support (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r
    (by omega) (by omega) (by omega)
  intro w hw
  by_cases eq:w=r
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [buildDual,wires_append,Finset.mem_union] at hw
  simp only [buildCached,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

-- Width161 specialization of MainPart04Base.lean :: unbuildDual_support
theorem unbuildDual_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length) :
    wires (unbuildDual acc Z bank cin src q r)⊆insert r (wires (unbuildConsumed acc Z bank cin src q)) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:6≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have sub:=consumedAddDual_support src Z ((acc.take 139).drop 6) (bank.take 132) cin q r (by omega) hy hc
  intro w hw
  by_cases eq:w=r
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [unbuildDual,wires_append,Finset.mem_union] at hw
  simp only [unbuildConsumed,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

-- Width161 specialization of MainPart04Base.lean :: buildDual_physical
theorem buildDual_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
    (off:r∉wires (buildCached acc Z bank cin src q)) (physical:GatePhysical (buildCached acc Z bank cin src q)) :
    GatePhysical (buildDual acc Z bank cin src q r) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  rw [buildCached,gatePhysical_append,gatePhysical_append] at physical
  have midOff:r∉wires (cachedSub (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q) := by
    intro h;apply off
    simp only [buildCached,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=cachedSubDual_physical _ _ _ cin q r (by omega) (by omega) (by omega) midOff physical.1.2
  simp only [buildDual,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

-- Width161 specialization of MainPart04Base.lean :: unbuildDual_physical
theorem unbuildDual_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length)
    (off:r∉wires (unbuildConsumed acc Z bank cin src q)) (physical:GatePhysical (unbuildConsumed acc Z bank cin src q)) :
    GatePhysical (unbuildDual acc Z bank cin src q r) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:6≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  rw [unbuildConsumed,gatePhysical_append,gatePhysical_append] at physical
  have midOff:r∉wires (consumedAdd src Z ((acc.take 139).drop 6) (bank.take 132) cin q) := by
    intro h;apply off
    simp only [unbuildConsumed,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=consumedAddDual_physical src Z ((acc.take 139).drop 6) (bank.take 132) cin q r (by omega) hy hc midOff physical.1.2
  simp only [unbuildDual,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

-- Width161 specialization of ParkAMany.lean :: buildTriple_support
theorem buildTriple_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) :
    wires (buildTriple acc Z bank cin src q r p)⊆insert p (wires (buildDual acc Z bank cin src q r)) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  have sub:=cachedSubTriple_support (Acc.tx Z 139 (Acc.earlyTerm src true 6))
    (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r p
    (by omega) (by omega) (by omega)
  intro w hw
  by_cases eq:w=p
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [buildTriple,wires_append,Finset.mem_union] at hw
  simp only [buildDual,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

-- Width161 specialization of ParkAMany.lean :: unbuildTriple_support
theorem unbuildTriple_support (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length) :
    wires (unbuildTriple acc Z bank cin src q r p)⊆insert p (wires (unbuildDual acc Z bank cin src q r)) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:7≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  have sub:=consumedAddTriple_support src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p (by omega) hy hc
  intro w hw
  by_cases eq:w=p
  · exact Finset.mem_insert.mpr (Or.inl eq)
  apply Finset.mem_insert_of_mem
  simp only [unbuildTriple,wires_append,Finset.mem_union] at hw
  simp only [unbuildDual,wires_append,Finset.mem_union]
  rcases hw with (hw|hw)|hw
  · exact Or.inl (Or.inl hw)
  · have h:=Finset.mem_insert.mp (sub hw)
    exact h.elim (fun e=>False.elim (eq e)) (fun h=>Or.inl (Or.inr h))
  · exact Or.inr hw

-- Width161 specialization of ParkAMany.lean :: buildTriple_physical
theorem buildTriple_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length)
    (off:p∉wires (buildDual acc Z bank cin src q r)) (physical:GatePhysical (buildDual acc Z bank cin src q r)) :
    GatePhysical (buildTriple acc Z bank cin src q r p) := by
  have len:=sub6_lengths acc Z bank src ha hs hz hb
  rw [buildDual,gatePhysical_append,gatePhysical_append] at physical
  have midOff:p∉wires (cachedSubDual (Acc.tx Z 139 (Acc.earlyTerm src true 6))
      (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) cin q r) := by
    intro h;apply off
    simp only [buildDual,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=cachedSubTriple_physical _ _ _ cin q r p (by omega) (by omega) (by omega) midOff physical.1.2
  simp only [buildTriple,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

-- Width161 specialization of ParkAMany.lean :: unbuildTriple_physical
theorem unbuildTriple_physical (acc Z bank : List Wire) (cin : Wire) (src : List Wire) (q r p : Wire)
    (ha:acc.length=161) (hs:src.length=128) (hb:132≤bank.length)
    (off:p∉wires (unbuildDual acc Z bank cin src q r)) (physical:GatePhysical (unbuildDual acc Z bank cin src q r)) :
    GatePhysical (unbuildTriple acc Z bank cin src q r p) := by
  have hy:((acc.take 139).drop 6).length=src.length+5 := by simp [ha,hs]
  have hc:7≤(bank.take 132).length := by simp [Nat.min_eq_left hb]
  rw [unbuildDual,gatePhysical_append,gatePhysical_append] at physical
  have midOff:p∉wires (consumedAddDual src Z ((acc.take 139).drop 6) (bank.take 132) cin q r) := by
    intro h;apply off
    simp only [unbuildDual,wires_append,Finset.mem_union]
    exact Or.inl (Or.inr h)
  have sub:=consumedAddTriple_physical src Z ((acc.take 139).drop 6) (bank.take 132) cin q r p (by omega) hy hc midOff physical.1.2
  simp only [unbuildTriple,gatePhysical_append]
  exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

-- Width161 specialization of ParkAMany.lean :: fresh_off_triple
theorem fresh_off_triple (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p u:Wire)
 (ha:acc.length=161) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (fresh:u∉cin::(src++acc++Z++bank)) (uq:u≠q) (ur:u≠r) (up:u≠p):
 u∉wires (buildTriple acc Z bank cin src q r p) ∧ u∉wires (unbuildTriple acc Z bank cin src q r p):=by
 have hf6:=hf _ (A161NarrowAcc.terms_mem src).2.2.1
 have zl:5≤Z.length:=by have h:=hf6.zpad;norm_num[Acc.earlyTerm,hs]at h;omega
 have bl:132≤bank.length:=by have h:=hf6.bankLen;norm_num[Acc.earlyTerm]at h;omega
 have off:=wloop_original_off acc Z bank cin src u ha hs hf fresh
 have bc:=buildCached_support acc Z bank cin src q ha hs zl bl
 have uc:=unbuildConsumed_support acc Z bank cin src q ha hs bl
 have bd:=buildDual_support acc Z bank cin src q r ha hs zl bl
 have ud:=unbuildDual_support acc Z bank cin src q r ha hs bl
 have bt:=buildTriple_support acc Z bank cin src q r p ha hs zl bl
 have ut:=unbuildTriple_support acc Z bank cin src q r p ha hs bl
 constructor
 · intro h
   rcases Finset.mem_insert.mp (bt h)with e|h
   · exact up e
   rcases Finset.mem_insert.mp (bd h)with e|h
   · exact ur e
   exact (Finset.mem_insert.mp (bc h)).elim uq off.1
 · intro h
   rcases Finset.mem_insert.mp (ut h)with e|h
   · exact up e
   rcases Finset.mem_insert.mp (ud h)with e|h
   · exact ur e
   exact (Finset.mem_insert.mp (uc h)).elim uq off.2

-- Width161 specialization of ParkAMany.lean :: buildMany_support
theorem buildMany_support (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤119):
 wires (buildMany k acc Z bank cin src hs q r p)⊆wires (buildTriple acc Z bank cin src q r p)∪hs.toFinset:=by
 have len:=sub6_lengths acc Z bank src ha hl hz hb
 exact support_surround _ _ _ _ hs (cachedSubMany_support k _ _ _ hs cin q r p (by omega) (by omega) (by omega))

-- Width161 specialization of ParkAMany.lean :: unbuildMany_support
theorem unbuildMany_support (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hl:src.length=128) (hb:132≤bank.length) (hk:k≤119):
 wires (unbuildMany k acc Z bank cin src hs q r p)⊆wires (unbuildTriple acc Z bank cin src q r p)∪hs.toFinset:=by
 exact support_surround _ _ _ _ hs (consumedAddMany_support k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
  (by omega) (by simp only[List.length_drop,List.length_take];omega) (by simp only[List.length_take];omega))

-- Width161 specialization of ParkAMany.lean :: buildMany_physical
theorem buildMany_physical (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤119)
 (fresh:∀u∈hs,u∉bank) (physical:GatePhysical (buildTriple acc Z bank cin src q r p)):
 GatePhysical (buildMany k acc Z bank cin src hs q r p):=by
 have len:=sub6_lengths acc Z bank src ha hl hz hb
 rw[buildTriple,gatePhysical_append,gatePhysical_append]at physical
 have sub:=cachedSubMany_gatePhysical k (Acc.tx Z 139 (Acc.earlyTerm src true 6))
  (Acc.ty (acc.take 139) (Acc.earlyTerm src true 6)) (Acc.tc bank 139 (Acc.earlyTerm src true 6)) hs cin q r p
  (by omega) (by omega) (by omega) (fun u hu bad=>fresh u hu (List.mem_of_mem_take bad)) physical.1.2
 rw[buildMany,gatePhysical_append,gatePhysical_append]
 exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

-- Width161 specialization of ParkAMany.lean :: unbuildMany_physical
theorem unbuildMany_physical (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hl:src.length=128) (hb:132≤bank.length) (hk:k≤119)
 (fresh:∀u∈hs,u∉bank) (physical:GatePhysical (unbuildTriple acc Z bank cin src q r p)):
 GatePhysical (unbuildMany k acc Z bank cin src hs q r p):=by
 rw[unbuildTriple,gatePhysical_append,gatePhysical_append]at physical
 have sub:=consumedAddMany_gatePhysical k src Z ((acc.take 139).drop 6) (bank.take 132) hs cin q r p
  (by omega) (by simp only[List.length_drop,List.length_take];omega) (by simp only[List.length_take];omega)
  (fun u hu bad=>fresh u hu (List.mem_of_mem_take bad)) physical.1.2
 rw[unbuildMany,gatePhysical_append,gatePhysical_append]
 exact ⟨⟨physical.1.1,sub⟩,physical.2⟩

-- Width161 specialization of ParkAMany.lean :: compiled_support_set
theorem compiled_support_set (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle newMiddle:Program)
 (ha:acc.length=161) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤119)
 (cert:ZeroSetDevelop.SRewrites hs middle newMiddle):
 wires (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p)⊆
 wires (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p)∪hs.toFinset:=by
 have b:=buildMany_support k acc Z bank cin src hs q r p ha hl hz hb hk
 have i:=unbuildMany_support k acc Z bank cin src hs q r p ha hl hb hk
 have mid:=(cert.support hs middle newMiddle).1
 intro w hw
 simp only[wires_append,Finset.mem_union]at hw ⊢
 rcases hw with (hw|hw)|hw
 · rcases Finset.mem_union.mp (b hw) with hw|hw
   · exact Or.inl (Or.inl (Or.inl hw))
   · exact Or.inr hw
 · exact Or.inl (Or.inl (Or.inr (mid hw)))
 · rcases Finset.mem_union.mp (i hw) with hw|hw
   · exact Or.inl (Or.inr hw)
   · exact Or.inr hw

-- Width161 specialization of ParkAMany.lean :: compiled_physical_set
theorem compiled_physical_set (k:Nat) (acc Z bank:List Wire) (cin:Wire) (src hs:List Wire) (q r p:Wire) (middle newMiddle:Program)
 (ha:acc.length=161) (hl:src.length=128) (hz:5≤Z.length) (hb:132≤bank.length) (hk:k≤119)
 (fresh:∀u∈hs,u∉bank) (cert:ZeroSetDevelop.SRewrites hs middle newMiddle)
 (physical:GatePhysical (buildTriple acc Z bank cin src q r p++middle++unbuildTriple acc Z bank cin src q r p)):
 GatePhysical (buildMany k acc Z bank cin src hs q r p++newMiddle++unbuildMany k acc Z bank cin src hs q r p):=by
 rw[gatePhysical_append,gatePhysical_append]at physical ⊢
 exact ⟨⟨buildMany_physical k acc Z bank cin src hs q r p ha hl hz hb hk fresh physical.1.1,
 cert.physical hs middle newMiddle physical.1.2⟩,
 unbuildMany_physical k acc Z bank cin src hs q r p ha hl hb hk fresh physical.2⟩
#print axioms compiled_physical_set
end ECDSAAdd.Entrant.A161Carry

end

-- Component Repad
section
namespace ECDSAAdd.Entrant.A161Repad
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop ZeroReadDevelop WholePadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires
-- Width161 specialization of FullLogic.lean :: build_repad
theorem build_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire)
 (ha:acc.length=161) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (hf':∀f∈earlyHTerms src,Acc.Fits acc Z' bank cin 161 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hz':∀w∈Z',s.basis w=false)
 (hb:∀w∈bank,s.basis w=false) (hi:s.basis cin=false) (zero:regValue acc s.basis=0):
 run (A161NarrowAcc.build8 acc Z bank cin src) m s=run (A161NarrowAcc.build8 acc Z' bank cin src) m s := by
 have a:=A161NarrowAcc.build8_triple acc Z bank cin src ha (by omega) hf s.basis hz hb hi s m ⟨zero,fun _ _=>rfl⟩
 have b:=A161NarrowAcc.build8_triple acc Z' bank cin src ha (by omega) hf' s.basis hz' hb hi s m ⟨zero,fun _ _=>rfl⟩
 exact state_eq_of_frame acc s.basis _ _ _ (a.1.trans b.1.symm) a.2 b.2

-- Width161 specialization of FullLogic.lean :: unbuild_repad
theorem unbuild_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire)
 (ha:acc.length=161) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (hf':∀f∈earlyHTerms src,Acc.Fits acc Z' bank cin 161 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hz':∀w∈Z',s.basis w=false)
 (hb:∀w∈bank,s.basis w=false) (hi:s.basis cin=false)
 (value:regValue acc s.basis=4294968272*regValue src s.basis):
 run (A161SourceAdd.unbuild acc Z bank cin src) m s=run (A161SourceAdd.unbuild acc Z' bank cin src) m s := by
 have a:=A161SourceAdd.unbuild_triple acc Z bank cin src ha hs hf s.basis hz hb hi s m ⟨value,fun _ _=>rfl⟩
 have b:=A161SourceAdd.unbuild_triple acc Z' bank cin src ha hs hf' s.basis hz' hb hi s m ⟨value,fun _ _=>rfl⟩
 exact state_eq_of_frame acc s.basis 0 _ _ (a.1.trans b.1.symm) a.2 b.2

-- Width161 specialization of FullLogic.lean :: build_measurements_repad
theorem build_measurements_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire)
 (ha:acc.length=161) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.FitsLen Z bank 161 f)
 (hf':∀f∈earlyHTerms src,Acc.FitsLen Z' bank 161 f):
 measurementCount (A161NarrowAcc.build8 acc Z bank cin src)=measurementCount (A161NarrowAcc.build8 acc Z' bank cin src) :=
 (A161NarrowAcc.build8_counts acc Z bank cin src ha (by omega) hf).1.2.trans
  (A161NarrowAcc.build8_counts acc Z' bank cin src ha (by omega) hf').1.2.symm

-- Width161 specialization of FullLogic.lean :: plain_loop_repad
theorem plain_loop_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire) (middle:Program)
 (ha:acc.length=161) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (hf':∀f∈earlyHTerms src,Acc.Fits acc Z' bank cin 161 f)
 (sub:Z'⊆Z) (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false)
 (hb:∀w∈bank,s.basis w=false) (hi:s.basis cin=false) (zero:regValue acc s.basis=0)
 (H:Nat) (post:WReady acc Z bank cin src H
  (run middle (m.drop (measurementCount (A161NarrowAcc.build8 acc Z bank cin src)))
   (run (A161NarrowAcc.build8 acc Z bank cin src) m s))):
 run (A161NarrowAcc.build8 acc Z bank cin src++middle++A161SourceAdd.unbuild acc Z bank cin src) m s=
 run (A161NarrowAcc.build8 acc Z' bank cin src++middle++A161SourceAdd.unbuild acc Z' bank cin src) m s := by
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

-- Width161 specialization of FullLogic.lean :: middle_repad
theorem middle_repad (acc Z Z' bank:List Wire) (cin:Wire) (src:List Wire) (middle:Program)
 (ha:acc.length=161) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f)
 (hf':∀f∈earlyHTerms src,Acc.Fits acc Z' bank cin 161 f)
 (s:State) (m:List Bool) (hz:∀w∈Z,s.basis w=false) (hz':∀w∈Z',s.basis w=false)
 (hb:∀w∈bank,s.basis w=false) (hi:s.basis cin=false) (zero:regValue acc s.basis=0):
 middleState (A161NarrowAcc.build8 acc Z bank cin src) middle s m=
 middleState (A161NarrowAcc.build8 acc Z' bank cin src) middle s m := by
 have ct:=build_measurements_repad acc Z Z' bank cin src ha hs (fun f h=>(hf f h).toFitsLen) (fun f h=>(hf' f h).toFitsLen)
 simp only [middleState,ct]
 rw [build_repad acc Z Z' bank cin src ha hs hf hf' s _ hz hz' hb hi zero]
#print axioms plain_loop_repad
end ECDSAAdd.Entrant.A161Repad

end

-- Component Plain
section
namespace ECDSAAdd.Entrant.A161Fold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop
 ControlLoan1589BFFold ThirdSavedCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires

theorem plain_frame (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (O:Nat) (hO:O<SquareReduction.p) :
 Triple (SquareFrame L.core.out base O) ((wBuild L++aMiddle L g)++wUnbuild L)
  (SquareFrame L.core.out base
   (((if base g then cFlipK-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
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
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := 4294968272*regValue (hiReg L) base
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^161 := by
    show 4294968272*regValue (hiReg L) base<2^161
    norm_num at hH ⊢
    omega
  have hAK : A≤cFlipK := by unfold cFlipK A161Facts.K161; omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^161 := by
    simp only [A']; split
    · unfold cFlipK A161Facts.K161; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hhi : regValue (hiReg L) b0=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => agree0 q (hiReg_product L q hq))
  have hbuild : Triple (SquareFrame (accReg L) b0 0) (wBuild L) (SquareFrame (accReg L) b0 A) := by
    have h := A161NarrowAcc.build8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) b0 hz hb clean.cin
    rw [hhi] at h
    exact h
  let mb := measurementCount (wBuild L)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (wBuild L) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis
      else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 161) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 161) (L.core.work.drop 161) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 161) u1.basis=0 :=
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
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc)
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis
      else regValue (accReg L) v.basis) at fl2
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
  have hhi2 : regValue (hiReg L) base2=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => (b2off q (prodNotOut q (hiReg_product L q hq))).trans
      (agree0 q (hiReg_product L q hq)))
  have offAcc (q : Wire) (hq:q∈hiReg L ∨ q∈L.foldPad ∨ q∈L.core.work.drop 161 ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉accReg L := by
    apply (other_away L hn q ?_).2.2
    tauto
  have source:regValue (hiReg L) v1.basis=regValue (hiReg L) base :=
    (regValue_congr _ _ _ (fun q hq=>frame2.2 q (offAcc q (Or.inl hq)))).trans hhi2
  have zv:∀q∈accZ L,v1.basis q=false := by
    intro q hq
    have na:q∉accReg L := by
      rcases accZ_mem L q hq with h|h
      · exact offAcc q (Or.inr (Or.inl h))
      · apply offAcc q
        have hd:(L.core.work.drop 161).drop 35=L.core.work.drop 196 := by simp [List.drop_drop]
        rw [←hd] at h
        exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
    exact (frame2.2 q na).trans (hz2 q hq)
  have bv:∀q∈accBank L,v1.basis q=false := by
    intro q hq
    exact (frame2.2 q (offAcc q (Or.inr (Or.inl (List.mem_of_mem_take hq))))).trans (hb2 q hq)
  have iv:v1.basis L.core.cin=false :=
    (frame2.2 _ (offAcc _ (by simp))).trans hi2
  have midEq:middleState (wBuild L) (aMiddle L g) s m=v1 := by
    simp only [middleState,aMiddle,run_append,measurementCount_append,
      (maskedConstant_counts _ _ _).2,Nat.zero_add,Nat.add_zero,List.take_zero,List.drop_zero,List.drop_drop]
    dsimp only [v1,v,u1,u,m3,m2,m1,mc,mb,mk]
    simp only [(maskedConstant_counts _ _ _).2,List.take_zero,List.drop_zero,Nat.add_zero,List.take_take,Nat.min_self,List.drop_take,Nat.sub_self]
  let post := m.drop (measurementCount (wBuild L)+measurementCount (aMiddle L g))
  have pre2 : SquareFrame (accReg L) base2 (4294968272*regValue (hiReg L) base2) v1.basis := by
    simpa only [hhi2] using frame2
  have inv := A161SourceAdd.unbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) base2 hz2 hb2 hi2 v1 post pre2
  have valuev1 : regValue L.core.out v1.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p :=
    (regValue_congr _ _ _ (fun q hq => fl2.2.1 q (fun ha => accOut q ha hq))).trans ek.2.1
  have firstTwo : run (wBuild L++aMiddle L g) m s=middleState (wBuild L) (aMiddle L g) s m := by
    simp only [middleState,run_take]
    exact run_cat _ _ _ _
  have loop : run ((wBuild L++aMiddle L g)++wUnbuild L) m s=
    run (wUnbuild L) post (middleState (wBuild L) (aMiddle L g) s m) := by
    rw [run_cat (wBuild L++aMiddle L g) (wUnbuild L) m s,measurementCount_append,firstTwo]
  rw [loop,midEq]
  refine ⟨inv.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have agreeOut : ∀q∈L.core.out,(run (wUnbuild L) post v1).basis q=v1.basis q := by
      intro q hq
      exact (inv.2.2 q (fun ha => accOut q ha hq)).trans (by simp [base2,hq])
    exact (regValue_congr _ _ _ agreeOut).trans valuev1
  · intro q hq
    by_cases ha:q∈accReg L
    · have outZero := (regValue_zero _ _).mp inv.2.1 q ha
      have oldZero := (regValue_zero _ _).mp hc.work q (accReg_work L q ha)
      exact outZero.trans oldZero.symm
    · exact (inv.2.2 q ha).trans ((b2off q hq).trans (hf.2 q hq))

#print axioms plain_frame
end ECDSAAdd.Entrant.A161Fold

end

-- Component GenericFold
section
namespace ECDSAAdd.Entrant.A161GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ECDSAAdd.measurementCount ECDSAAdd.toffoliCount

def domain (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 L.core.cin::(hiReg L++A161Fold.accReg L++FullPadDevelop.pad L++accBank L)

def Ready (L : CuccaroStreamedSquareWideLayout) (g : Wire) (hs : List Wire) : Prop :=
 g∉L.wires ∧ hs.length=96 ∧ hs.Nodup ∧
 (∀u∈hs,u∉domain L) ∧ (∀u∈hs,u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L) ∧
 L.core.sumCarry∉domain L ∧ eV L∉domain L ∧ spare L∉domain L ∧
 eV L≠L.core.sumCarry ∧ spare L≠L.core.sumCarry ∧ spare L≠eV L ∧
 (∀u∈([L.core.sumCarry,eV L,spare L] : List Wire),
   u∉g::A161Fold.accReg L ∧ u∉L.measuredCore.wires ∧ u∉L.core.out)

def loop (L : CuccaroStreamedSquareWideLayout) (hs : List Wire) (middle : Program) : Program :=
 A161Carry.buildMany 96 (A161Fold.accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L)++middle++
 A161Carry.unbuildMany 96 (A161Fold.accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L)

theorem smallFit (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (A161Fold.accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin 161 f := by
 intro f hf
 have old := FullPadDevelop.terms_fits L hw hn f hf
 have hl : f.src.length+f.shift<161 := by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> simp [Acc.earlyTerm,hiReg_length L hw]
 simpa [A161Fold.accReg,ECDSAAdd.Entrant.accReg,List.take_take] using
  (Acc.fits_prefix (ECDSAAdd.Entrant.accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin 163 161 f (by decide) old hl)

theorem free_middle (L : CuccaroStreamedSquareWideLayout) (g u : Wire)
 (ha:u∉g::A161Fold.accReg L) (hc:u∉L.measuredCore.wires) : u∉wires (A161Fold.aMiddle L g) := by
 have hm : u∉wires (maskedConstant g (A161Fold.accReg L) A161Fold.cFlipK) := by
  intro h
  exact ha (List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h))
 have hk : u∉wires (qprogTq L.measuredCore SquareReduction.p) := by
  have hc' : u∉L.measuredCore.wires.toFinset := by simpa only [List.mem_toFinset] using hc
  exact fun h => hc' (QCore.qprog_supportTq L.measuredCore SquareReduction.p h)
 intro h
 simp only [A161Fold.aMiddle,wires_append,Finset.mem_union] at h
 exact h.elim hm (fun h => h.elim hk hm)

theorem eq_plain (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (ready:Ready L g hs)
 (cert:ZeroSetDevelop.SRewrites hs (A161Fold.aMiddle L g) newMiddle)
 (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false)
 (O:Nat) (hO:O<SquareReduction.p) (s:State) (m:List Bool)
 (hf:SquareFrame L.core.out base O s.basis) (zeroU:∀u∈hs,s.basis u=false) :
 run (loop L hs newMiddle) m s=
 run ((A161Fold.wBuild L++A161Fold.aMiddle L g)++A161Fold.wUnbuild L) m s := by
  let acc := A161Fold.accReg L
  let pad := FullPadDevelop.pad L
  let bank := accBank L
  let src := hiReg L
  let q := L.core.sumCarry
  let r := eV L
  let p := spare L
  let middleProgram := A161Fold.aMiddle L g
  have smallFit := smallFit L hw hn
  rcases ready with ⟨hg,hlen,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,fmid⟩
  have lens := A161Fold.acc_lengths L hw
  have hsrc := hiReg_length L hw
  have fullfit := A161Fold.wTerms_fits L hw hn
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  have hzFull : ∀u∈accZ L,s.basis u=false := by
   intro u hu
   rcases accZ_mem L u hu with hu|hu
   · exact (regValue_zero _ _).mp clean.pad u hu
   · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
  have hz : ∀u∈pad,s.basis u=false := fun u hu => hzFull u ((FullPadDevelop.pad_sublist L).subset hu)
  have hb : ∀u∈bank,s.basis u=false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
  have ha : regValue acc s.basis=0 := (regValue_zero _ _).mpr (fun u hu =>
   (regValue_zero _ _).mp clean.work u (A161Fold.accReg_work L u hu))
  have zq := (hf.2 q (fmid q (by simp [q,r,p])).2.2).trans hsum
  have zr := (hf.2 r (fmid r (by simp [q,r,p])).2.2).trans hV
  have zp := (hf.2 p (fmid p (by simp [q,r,p])).2.2).trans hP
  have offq := A161Carry.wloop_original_off acc pad bank L.core.cin src q lens.1 hsrc smallFit fq
  have offr := A161Carry.wloop_original_off acc pad bank L.core.cin src r lens.1 hsrc smallFit fr
  have offp := A161Carry.wloop_original_off acc pad bank L.core.cin src p lens.1 hsrc smallFit fp
  have plen := FullPadDevelop.pad_length L hw
  have blen := lens.2.2.1
  have bd := A161Carry.buildDual_support acc pad bank L.core.cin src q r lens.1 hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have ud := A161Carry.unbuildDual_support acc pad bank L.core.cin src q r lens.1 hsrc (by change 132≤(accBank L).length; omega)
  have b0 := A161Carry.buildCached_support acc pad bank L.core.cin src q lens.1 hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have u0 := A161Carry.unbuildConsumed_support acc pad bank L.core.cin src q lens.1 hsrc (by change 132≤(accBank L).length; omega)
  have offpd : p∉wires (A161Carry.buildDual acc pad bank L.core.cin src q r) ∧
   p∉wires (A161Carry.unbuildDual acc pad bank L.core.cin src q r) := by
   constructor
   · intro h
     exact (Finset.mem_insert.mp (bd h)).elim pr (fun h => (Finset.mem_insert.mp (b0 h)).elim pq offp.1)
   · intro h
     exact (Finset.mem_insert.mp (ud h)).elim pr (fun h => (Finset.mem_insert.mp (u0 h)).elim pq offp.2)
  have offU (u:Wire) (hu:u∈hs) := A161Carry.fresh_off_triple acc pad bank L.core.cin src q r p u
   lens.1 hsrc smallFit (hfresh u hu) (hne u hu).1 (hne u hu).2.1 (hne u hu).2.2
  have mq := free_middle L g q (fmid q (by simp [q,r,p])).1 (fmid q (by simp [q,r,p])).2.1
  have mr := free_middle L g r (fmid r (by simp [q,r,p])).1 (fmid r (by simp [q,r,p])).2.1
  have mp := free_middle L g p (fmid p (by simp [q,r,p])).1 (fmid p (by simp [q,r,p])).2.1
  have oldGood := A161Fold.a_middle_good L hw hn g hg base hc O hO s m hf
  have middleEq := A161Repad.middle_repad acc (accZ L) pad bank L.core.cin src middleProgram lens.1 hsrc fullfit smallFit
   s m hzFull hz hb clean.cin ha
  have good : WReady acc pad bank L.core.cin src (regValue src s.basis)
   (middleState (A161NarrowAcc.build8 acc pad bank L.core.cin src) middleProgram s m) := by
   rw [←middleEq]
   exact ⟨oldGood.1,oldGood.2.1,(fun u hu => oldGood.2.2.1 u ((FullPadDevelop.pad_sublist L).subset hu)),oldGood.2.2.2⟩
  have eq := A161Carry.compiled_wloop_many_eq_set 96 acc pad bank L.core.cin src hs q r p middleProgram newMiddle
   lens.1 hsrc smallFit s m hz hb clean.cin ha zq zr zp fq fr rq fp pq pr
   offq.1 mq offq.2 offr.1 mr offr.2 offpd.1 mp offpd.2
   (by decide) hnd hlen zeroU hfresh hne (fun u hu => (offU u hu).1) (fun u hu => (offU u hu).2) cert good
  have plain := A161Carry.triple_plain_eq acc pad bank L.core.cin src q r p middleProgram lens.1 hsrc smallFit
   s m hz hb clean.cin ha zq zr zp fq fr rq fp pq pr offq.1 mq offq.2 offr.1 mr offr.2 offpd.1 mp offpd.2 good
  have repad := A161Repad.plain_loop_repad acc (accZ L) pad bank L.core.cin src middleProgram lens.1 hsrc fullfit smallFit
   (FullPadDevelop.pad_sublist L).subset s m hzFull hb clean.cin ha (regValue src s.basis)
   (by simpa only [middleState,run_take] using oldGood)
  have combine := eq.trans (plain.trans repad.symm)
  have assoc : ((A161Fold.wBuild L++middleProgram)++A161Fold.wUnbuild L)=
   (A161NarrowAcc.build8 acc (accZ L) bank L.core.cin src++middleProgram++A161SourceAdd.unbuild acc (accZ L) bank L.core.cin src) :=
   rfl
  exact combine.trans (congrArg (fun P : Program => run P m s) assoc.symm)


#print axioms eq_plain
end ECDSAAdd.Entrant.A161GenericFold

end

-- Component EXTEND
section
namespace ECDSAAdd.Entrant.A161Extend
open ZeroSetDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
theorem eraseS_extend (Q:List Wire) (d:Wire) (i:Instr) (h:d∉i.wires) :
    eraseS (Q++[d]) i=eraseS Q i := by
  have mem : ∀ x, x∈i.wires → (x∈Q++[d] ↔ x∈Q) := by
    intro x hx
    simp only [List.mem_append,List.mem_singleton]
    constructor
    · rintro (h1|h1)
      · exact h1
      · exact absurd (h1 ▸ hx) h
    · intro h1
      exact Or.inl h1
  have prune : ∀ cs : List Correction, (∀ x∈correctionWires cs, (x∈Q++[d] ↔ x∈Q)) →
      pruneS (Q++[d]) cs=pruneS Q cs := by
    intro cs
    induction cs with
    | nil => intro _; rfl
    | cons c cs ih =>
      intro hcs
      cases c with
      | Z t =>
        have ht := hcs t (by simp [correctionWires])
        have rest : ∀ x∈correctionWires cs, (x∈Q++[d] ↔ x∈Q) := fun x hx => hcs x (by simp [correctionWires,hx])
        have e := ih rest
        simp only [pruneS,List.filter_cons,keepS] at e ⊢
        simp only [decide_eq_decide.mpr ht,e]
      | CZ a b =>
        have ha := hcs a (by simp [correctionWires])
        have hb := hcs b (by simp [correctionWires])
        have rest : ∀ x∈correctionWires cs, (x∈Q++[d] ↔ x∈Q) := fun x hx => hcs x (by simp [correctionWires,hx])
        have e := ih rest
        simp only [pruneS,List.filter_cons,keepS] at e ⊢
        simp only [decide_eq_decide.mpr ha,decide_eq_decide.mpr hb,e]
  cases i with
  | X t => rfl
  | CX a t =>
    have ha := mem a (by simp [Instr.wires])
    simp only [eraseS]
    rw [if_congr ha rfl rfl]
  | CCX a b t =>
    have ha := mem a (by simp [Instr.wires])
    have hb := mem b (by simp [Instr.wires])
    simp only [eraseS]
    rw [if_congr (or_congr ha hb) rfl rfl]
  | measureX t c0 c1 =>
    simp only [eraseS]
    rw [prune c0 (fun x hx => mem x (by simp [Instr.wires,hx])),
      prune c1 (fun x hx => mem x (by simp [Instr.wires,hx]))]

/-- A zero-set rewrite stays valid when an unused zero wire joins the zero set. -/
theorem SRewrites_extend (Q:List Wire) (d:Wire) (p r:Program) (h:SRewrites Q p r) :
    d∉wires p → SRewrites (Q++[d]) p r := by
  induction h with
  | nil => intro _; exact SRewrites.nil
  | normal i p r ht tail ih =>
    intro hd
    have hi : d∉i.wires := fun h' => hd (by simp only [wires,Finset.mem_union]; exact Or.inl h')
    have hp : d∉wires p := fun h' => hd (by simp only [wires,Finset.mem_union]; exact Or.inr h')
    rw [← eraseS_extend Q d i hi]
    refine SRewrites.normal i p r ?_ (ih hp)
    intro hm
    rcases List.mem_append.mp hm with h1|h1
    · exact ht h1
    · rw [List.mem_singleton] at h1
      apply hi
      rw [← h1]
      cases i <;> simp [ZeroReadDevelop.targetOf,Instr.wires]
  | zeroMajority a q c e p r hq he hn tail ih =>
    intro hd
    have hm : d∉wires (Arithmetic.majority a q c e) := fun h' => hd (by rw [wires_append]; exact Finset.mem_union_left _ h')
    have hp : d∉wires p := fun h' => hd (by rw [wires_append]; exact Finset.mem_union_right _ h')
    have hne : d≠a ∧ d≠c ∧ d≠e := by
      refine ⟨fun h' => hm ?_,fun h' => hm ?_,fun h' => hm ?_⟩ <;>
        subst h' <;> simp [Arithmetic.majority,wires,Instr.wires]
    rw [← eraseS_extend Q d (Instr.CCX a c e) (by simp [Instr.wires]; tauto)]
    refine SRewrites.zeroMajority a q c e p r (List.mem_append_left _ hq) ?_ hn (ih hp)
    intro h1
    rcases List.mem_append.mp h1 with h1|h1
    · exact he h1
    · rw [List.mem_singleton] at h1
      exact hne.2.2 h1.symm
end ECDSAAdd.Entrant.A161Extend

end

-- Component FixedData
section
namespace ECDSAAdd.Entrant.A161FixedFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ECDSAAdd.measurementCount ECDSAAdd.toffoliCount ZeroSetDevelop.compileS?

abbrev L := FullPadSupport.L
abbrev g := FullPadSupport.c
abbrev d := Baselines.layout.core.poolWire 1540
abbrev acc := A161Fold.accReg L
abbrev pad := FullPadDevelop.pad L
abbrev bank := accBank L
abbrev src := hiReg L
abbrev q := L.core.sumCarry
abbrev r := eV L
abbrev p := spare L
abbrev hs95 := A161Facts.loans95 L
abbrev hs96 := hs95++[d]
abbrev middleProgram := A161Fold.aMiddle L g
abbrev domain := L.core.cin::(src++acc++pad++bank)

theorem hw : L.Widths := Baselines.layout.dialogStreamedSquareWide_widths Baselines.layout_widths
theorem hn : L.wires.Nodup := Baselines.layout.dialogStreamedSquareWide_nodup Baselines.layout_widths Baselines.layout_nodup

theorem geometry : g∉L.wires ∧ hs96.length=96 ∧ hs96.Nodup ∧
 (∀u∈hs96,u∉domain) ∧ (∀u∈hs96,u≠q ∧ u≠r ∧ u≠p) ∧
 q∉domain ∧ r∉domain ∧ p∉domain ∧ r≠q ∧ p≠q ∧ p≠r ∧
 (∀u∈([q,r,p,d] : List Wire),u∉g::acc ∧ u∉L.measuredCore.wires ∧ u∉L.core.out) ∧
 (∀u∈hs95,u∈L.core.work) := by
 decide

theorem smallFit : ∀f∈earlyHTerms src,Acc.Fits acc pad bank L.core.cin 161 f := by
 intro f hf
 have old := FullPadDevelop.terms_fits L hw hn f hf
 have hl : f.src.length+f.shift<161 := by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> simp [Acc.earlyTerm,hiReg_length L hw]
 simpa [acc,A161Fold.accReg,ECDSAAdd.Entrant.accReg,List.take_take] using
  (Acc.fits_prefix (ECDSAAdd.Entrant.accReg L) pad bank L.core.cin 163 161 f (by decide) old hl)

theorem middle_free (u : Wire) (ha:u∉g::acc) (hc:u∉L.measuredCore.wires) : u∉wires middleProgram := by
 have hm : u∉wires (maskedConstant g acc A161Fold.cFlipK) := by
  intro h
  exact ha (List.mem_toFinset.mp (maskedConstant_wires_subset g acc A161Fold.cFlipK h))
 have hk : u∉wires (qprogTq L.measuredCore SquareReduction.p) := by
  have hc' : u∉L.measuredCore.wires.toFinset := by simpa only [List.mem_toFinset] using hc
  exact fun h => hc' (QCore.qprog_supportTq L.measuredCore SquareReduction.p h)
 intro h
 simp only [middleProgram,A161Fold.aMiddle,wires_append,Finset.mem_union] at h
 exact h.elim hm (fun h => h.elim hk hm)

def checked : ZeroSetDevelop.CheckedS hs95 A161Facts.p161 :=
 (ZeroSetDevelop.compileS? hs95 A161Facts.p161).get A161Facts.compiled95
attribute [local irreducible] checked

theorem cert95 : ZeroSetDevelop.SRewrites hs95 middleProgram checked.out := by
 have h := Eq.mp (congrArg (fun P : Program => ZeroSetDevelop.SRewrites hs95 P checked.out) A161Facts.input_eq) checked.proof
 simpa only [middleProgram,A161Fold.aMiddle,A161Fold.accReg,A161Fold.cFlipK,A161Facts.aMiddle161,A161Facts.acc161] using h

theorem cert96 : ZeroSetDevelop.SRewrites hs96 middleProgram checked.out := by
 rcases geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,hm,_⟩
 have hf := hm d (by simp)
 exact A161Extend.SRewrites_extend hs95 d middleProgram checked.out cert95 (middle_free d hf.1 hf.2.1)

def fold96 : Program := A161GenericFold.loop L hs96 checked.out

end ECDSAAdd.Entrant.A161FixedFold

end

-- Component FixedFold
section
namespace ECDSAAdd.Entrant.A161FixedFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires checked

theorem ready : A161GenericFold.Ready L g hs96 := by
 rcases geometry with ⟨hg,hl,hn,hf,he,hq,hr,hp,hrq,hpq,hpr,hm,hw⟩
 refine ⟨hg,hl,hn,hf,he,hq,hr,hp,hrq,hpq,hpr,?_⟩
 intro u hu
 exact hm u (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hu ⊢; tauto)
 theorem fold96_eq_plain (base : BasisState) (hc:L.PairClean base)
 (hsum:base q=false) (hV:base r=false) (hP:base p=false)
 (O:Nat) (hO:O<SquareReduction.p) (s:State) (m:List Bool)
 (hf:SquareFrame L.core.out base O s.basis) (zeroU:∀u∈hs96,s.basis u=false) :
 run fold96 m s=run ((A161Fold.wBuild L++middleProgram)++A161Fold.wUnbuild L) m s := by
 exact A161GenericFold.eq_plain L hw hn g hs96 checked.out ready cert96 base hc hsum hV hP O hO s m hf zeroU

#print axioms fold96_eq_plain
end ECDSAAdd.Entrant.A161FixedFold

end

-- Component Frame
section
namespace ECDSAAdd.Entrant.A161GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ThirdSavedCarryDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem frame (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (ready:Ready L g hs)
 (cert:ZeroSetDevelop.SRewrites hs (A161Fold.aMiddle L g) newMiddle)
 (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false)
 (hostClean:∀u∈hs,u∉L.core.out ∧ base u=false) (O:Nat) (hO:O<SquareReduction.p) :
 Triple (SquareFrame L.core.out base O) (loop L hs newMiddle)
  (SquareFrame L.core.out base
   (((if base g then A161Fold.cFlipK-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
     (SquareReduction.p-1-O))%SquareReduction.p)) := by
 intro s m hf
 have hz : ∀u∈hs,s.basis u=false := by
  intro u hu
  exact (hf.2 u (hostClean u hu).1).trans (hostClean u hu).2
 have e := eq_plain L hw hn g hs newMiddle ready cert base hc hsum hV hP O hO s m hf hz
 rw [e]
 exact A161Fold.plain_frame L hw hn g ready.1 base hc O hO s m hf
#print axioms frame
end ECDSAAdd.Entrant.A161GenericFold

namespace ECDSAAdd.Entrant.A161FixedFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ThirdSavedCarryDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires checked
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem hostClean (base:BasisState) (hc:L.PairClean base) (hd:base d=false) :
 ∀u∈hs96,u∉L.core.out ∧ base u=false := by
 rcases geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,hm,hw⟩
 intro u hu
 rcases List.mem_append.mp hu with hu|hu
 · have hu := hw u hu
   exact ⟨(L.pairAuxAway hn u (by simp [hu])).2,(regValue_zero _ _).mp hc.work u hu⟩
 · have he : u=d := by simpa only [List.mem_singleton] using hu
   subst u
   exact ⟨(hm d (by simp)).2.2,hd⟩

theorem frame (base:BasisState) (hc:L.PairClean base) (hsum:base q=false)
 (hV:base r=false) (hP:base p=false) (hd:base d=false) (O:Nat) (hO:O<SquareReduction.p) :
 Triple (SquareFrame L.core.out base O) fold96
  (SquareFrame L.core.out base
   (((if base g then A161Fold.cFlipK-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
     (SquareReduction.p-1-O))%SquareReduction.p)) := by
 exact A161GenericFold.frame L hw hn g hs96 checked.out ready cert96 base hc hsum hV hP (hostClean base hc hd) O hO
#print axioms frame
end ECDSAAdd.Entrant.A161FixedFold

end

-- Component Offsets
section
namespace ECDSAAdd.Entrant.A161Offsets
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

def delta : Nat := 3*2^161

theorem flip_decomposition : OwnDiagAll12Square.cFlipK=A161Facts.K161+delta := by
 norm_num [OwnDiagAll12Square.cFlipK,A161Facts.K161,delta]

-- The A body is reflected: reducing its complement decreases the reflected output,
-- and therefore increases the unreflected square offset.
def squareK : Nat := ControlLoan1589BFFold.K+delta

theorem squareK_lt : squareK<SquareReduction.p := by
 norm_num [squareK,delta,ControlLoan1589BFFold.K,SquareReduction.p,SquareReduction.B,SquareReduction.c]

theorem squareK_cast : (squareK : ZMod SquareReduction.p)=
 (ControlLoan1589BFFold.K : ZMod SquareReduction.p)+(delta : ZMod SquareReduction.p) := by
 rw [squareK,Nat.cast_add]

def resAF161 (P O : Nat) (g : Bool) : Nat :=
 ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-P-
   (if g then (A161Facts.K161 : ZMod SquareReduction.p) else 0)))

theorem resAF_delta (P O : Nat) (g : Bool) : (resAF161 P O g : ZMod SquareReduction.p)=
 (resAF P O g : ZMod SquareReduction.p)-(if g then (delta : ZMod SquareReduction.p) else 0) := by
 haveI : NeZero SquareReduction.p := ⟨by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]⟩
 simp only [resAF161,resAF,ofCast,if_true,ZMod.natCast_zmod_val]
 cases g
 · simp
 · simp only [if_true]
   rw [flip_decomposition,Nat.cast_add]
   ring

theorem absorb {F : Type*} [CommRing F] (X S K c d : F) (g : Bool) :
 (X-(if g then S else 0)+(if g then K+d else 0))+(if g then c-d else 0)=
 (X-(if g then S else 0)+(if g then K else 0))+(if g then c else 0) := by
 cases g <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring

#print axioms resAF_delta
#print axioms squareK_cast
#print axioms absorb
end ECDSAAdd.Entrant.A161Offsets

end

-- Component Body
section
namespace ECDSAAdd.Entrant.A161Body
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop FullASelectedDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem body_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) (fold : Program)
    (foldFrame : ∀ O, O<SquareReduction.p → base (eV L)=false → base (spare L)=false →
      Triple (SquareFrame L.core.out base O) fold
       (SquareFrame L.core.out base
        (((if base c then A161Facts.K161-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
         (SquareReduction.p-1-O))%SquareReduction.p))) :
    Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)) (SquareFrame L.core.out base (A161Offsets.resAF161 (M^2) O (base c))) := by
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
  have t3 := foldFrame O2 hO2 vZero (spare_zero L hw base M hP)
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
    exact A161Facts.accumulator_bound _ hH
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
  have bound : ((if base c then A161Facts.K161-A else A)+(SquareReduction.p-1-O2))%SquareReduction.p<SquareReduction.p :=
    Nat.mod_lt _ pmod
  apply measuredOrientationCast_injective true _ _ bound (ofCast_lt true _)
  refine Eq.trans ?_ (cast_ofCast true (measuredOrientationCast false O+(((M^2 : Nat) : ZMod SquareReduction.p)*2^128-
    ((M^2 : Nat) : ZMod SquareReduction.p)-(if base c then (A161Facts.K161 : ZMod SquareReduction.p) else 0)))).symm
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
    have hAle : A≤A161Facts.K161 := by simp only [A161Facts.K161]; omega
    have hoff : ((A161Facts.K161-A : Nat) : ZMod SquareReduction.p)=(A161Facts.K161 : ZMod SquareReduction.p)-
        (A : ZMod SquareReduction.p) := by
      rw [Nat.cast_sub hAle]
    rw [hoff]
    linear_combination hsum
#print axioms body_frame
end ECDSAAdd.Entrant.A161Body

end

-- Component TripleResources
section
namespace ECDSAAdd.Entrant.A161Carry
open Arithmetic InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires
 theorem physical (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f) (rq:r≠q)
 (offF:q∉wires (A161NarrowAcc.build8 acc Z bank cin src))
 (offI:q∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFR:r∉wires (A161NarrowAcc.build8 acc Z bank cin src))
 (offIR:r∉wires (A161SourceAdd.unbuild acc Z bank cin src))
 (offFP:p∉wires (buildDual acc Z bank cin src q r))
 (offIP:p∉wires (unbuildDual acc Z bank cin src q r)):
 GatePhysical (buildTriple acc Z bank cin src q r p) ∧ GatePhysical (unbuildTriple acc Z bank cin src q r p) := by
 have fit:=hf _ (A161NarrowAcc.terms_mem src).2.2.1
 have hz:5≤Z.length:=by have h:=fit.zpad;norm_num [Acc.earlyTerm,hs] at h;omega
 have hb:132≤bank.length:=by have h:=fit.bankLen;norm_num [Acc.earlyTerm] at h;omega
 have plainF:=(A161KnownTail.build8_physical acc Z bank cin src ha (by omega) hf).1
 rw [A161KnownTail.build8_eq] at plainF
 have plainI:=A161SourceAdd.unbuild_physical acc Z bank cin src ha hs hf
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

 theorem support (acc Z bank:List Wire) (cin:Wire) (src:List Wire) (q r p:Wire)
 (ha:acc.length=161) (hs:src.length=128)
 (hf:∀f∈earlyHTerms src,Acc.Fits acc Z bank cin 161 f):
 wires (buildTriple acc Z bank cin src q r p) ⊆ (p::r::q::cin::(src++acc++Z++bank)).toFinset ∧
 wires (unbuildTriple acc Z bank cin src q r p) ⊆ (p::r::q::cin::(src++acc++Z++bank)).toFinset := by
 have fit:=hf _ (A161NarrowAcc.terms_mem src).2.2.1
 have hz:5≤Z.length:=by have h:=fit.zpad;norm_num [Acc.earlyTerm,hs] at h;omega
 have hb:132≤bank.length:=by have h:=fit.bankLen;norm_num [Acc.earlyTerm] at h;omega
 have plain:=A161KnownTail.build8_support acc Z bank cin src ha (by omega) hf
 rw [A161KnownTail.build8_eq] at plain
 have unbuild:=A161SourceAdd.unbuild_resources acc Z bank cin src ha hs (fun f h=>(hf f h).toFitsLen)
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
   have oldI := (A161KnownTail.build8_support acc Z bank cin src ha (by omega) hf).2
   have h:=List.mem_toFinset.mp (oldI (unbuild.2.2.1 hw))
   simp only [List.mem_toFinset,List.mem_cons]
   exact Or.inr (Or.inr (Or.inr (by simpa only [List.mem_cons] using h)))
#print axioms physical
#print axioms support
end ECDSAAdd.Entrant.A161Carry

end

-- Component LoopResources
section
namespace ECDSAAdd.Entrant.A161GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run

theorem physical (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (ready:Ready L g hs)
 (cert:ZeroSetDevelop.SRewrites hs (A161Fold.aMiddle L g) newMiddle) :
 GatePhysical (loop L hs newMiddle) := by
  let acc := A161Fold.accReg L
  let pad := FullPadDevelop.pad L
  let bank := accBank L
  let src := hiReg L
  let q := L.core.sumCarry
  let r := eV L
  let p := spare L
  let middleProgram := A161Fold.aMiddle L g
  have smallFit := smallFit L hw hn
  rcases ready with ⟨hg,hlen,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,fmid⟩
  have lens := A161Fold.acc_lengths L hw
  have hsrc := hiReg_length L hw
  have offq := A161Carry.wloop_original_off acc pad bank L.core.cin src q lens.1 hsrc smallFit fq
  have offr := A161Carry.wloop_original_off acc pad bank L.core.cin src r lens.1 hsrc smallFit fr
  have offp := A161Carry.wloop_original_off acc pad bank L.core.cin src p lens.1 hsrc smallFit fp
  have plen := FullPadDevelop.pad_length L hw
  have blen := lens.2.2.1
  have bd := A161Carry.buildDual_support acc pad bank L.core.cin src q r lens.1 hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have ud := A161Carry.unbuildDual_support acc pad bank L.core.cin src q r lens.1 hsrc (by change 132≤(accBank L).length; omega)
  have b0 := A161Carry.buildCached_support acc pad bank L.core.cin src q lens.1 hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have u0 := A161Carry.unbuildConsumed_support acc pad bank L.core.cin src q lens.1 hsrc (by change 132≤(accBank L).length; omega)
  have offpd : p∉wires (A161Carry.buildDual acc pad bank L.core.cin src q r) ∧
   p∉wires (A161Carry.unbuildDual acc pad bank L.core.cin src q r) := by
   constructor
   · intro h
     exact (Finset.mem_insert.mp (bd h)).elim pr (fun h => (Finset.mem_insert.mp (b0 h)).elim pq offp.1)
   · intro h
     exact (Finset.mem_insert.mp (ud h)).elim pr (fun h => (Finset.mem_insert.mp (u0 h)).elim pq offp.2)
  have pp := A161Carry.physical acc pad bank L.core.cin src q r p lens.1 hsrc smallFit rq
   offq.1 offq.2 offr.1 offr.2 offpd.1 offpd.2
  have coreNd : L.measuredCore.wires.Nodup :=
   (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have mc := maskedConstant_physical g acc A161Fold.cFlipK (fun h => hg (A161Fold.accReg_in L g h))
  have mid : GatePhysical middleProgram := by
   simp only [middleProgram,A161Fold.aMiddle,gatePhysical_append]
   exact ⟨mc,QCore.qprog_physicalTq L.measuredCore SquareReduction.p coreNd,mc⟩
  have fresh : ∀u∈hs,u∉bank := by
   intro u hu hb
   exact hfresh u hu (by simp [domain,bank,hb])
  have physical : GatePhysical (A161Carry.buildTriple acc pad bank L.core.cin src q r p++middleProgram++A161Carry.unbuildTriple acc pad bank L.core.cin src q r p) := by
   simp only [gatePhysical_append]
   exact ⟨⟨pp.1,mid⟩,pp.2⟩
  exact A161Carry.compiled_physical_set 96 acc pad bank L.core.cin src hs q r p middleProgram newMiddle
   lens.1 hsrc (by change 5≤(FullPadDevelop.pad L).length; omega)
   (by change 132≤(accBank L).length; omega) (by decide) fresh cert physical

def ambient (L : CuccaroStreamedSquareWideLayout) (g : Wire) (hs : List Wire) : List Wire :=
 g::spare L::eV L::L.core.sumCarry::(domain L++L.measuredCore.wires++hs)

theorem support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program)
 (cert:ZeroSetDevelop.SRewrites hs (A161Fold.aMiddle L g) newMiddle) :
 wires (loop L hs newMiddle)⊆(ambient L g hs).toFinset := by
 let acc := A161Fold.accReg L
 let pad := FullPadDevelop.pad L
 let bank := accBank L
 let src := hiReg L
 have lens := A161Fold.acc_lengths L hw
 have hsrc := hiReg_length L hw
 have plen := FullPadDevelop.pad_length L hw
 have hfit := smallFit L hw hn
 have tri := A161Carry.support acc pad bank L.core.cin src L.core.sumCarry (eV L) (spare L) lens.1 hsrc hfit
 have cmp := A161Carry.compiled_support_set 96 acc pad bank L.core.cin src hs L.core.sumCarry (eV L) (spare L)
  (A161Fold.aMiddle L g) newMiddle lens.1 hsrc (by change 5≤(FullPadDevelop.pad L).length; omega)
  (by change 132≤(accBank L).length; omega) (by decide) cert
 have sub (u:Wire) (h:u∈(spare L::eV L::L.core.sumCarry::L.core.cin::(src++acc++pad++bank)).toFinset) :
  u∈(ambient L g hs).toFinset := by
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  simp only [ambient,domain,List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto
 intro u hu
 rcases Finset.mem_union.mp (cmp hu) with h|h
 · simp only [wires_append,Finset.mem_union] at h
   rcases h with (h|h)|h
   · exact sub u (tri.1 h)
   · simp only [A161Fold.aMiddle,wires_append,Finset.mem_union] at h
     rcases h with h|(h|h)
     · have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
       simp only [List.mem_cons] at h
       simp only [ambient,domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       tauto
     · have h := List.mem_toFinset.mp (QCore.qprog_supportTq L.measuredCore SquareReduction.p h)
       simp only [ambient,domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       tauto
     · have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
       simp only [List.mem_cons] at h
       simp only [ambient,domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       tauto
   · exact sub u (tri.2 h)
 · have h := List.mem_toFinset.mp h
   simp only [ambient,List.mem_toFinset,List.mem_cons,List.mem_append]
   tauto

#print axioms physical
#print axioms support
end ECDSAAdd.Entrant.A161GenericFold

end

-- Component AmbientSites
section
namespace ECDSAAdd.Entrant.A161GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

theorem work_in (L:CuccaroStreamedSquareWideLayout) (u:Wire) (h:u∈L.core.work) : u∈L.wires := by
 simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]

theorem append_hosts (L:CuccaroStreamedSquareWideLayout) (hs:List Wire) (d:Wire)
 (hwork:∀u∈hs,u∈L.core.work) : ∀u∈hs++[d],u=d ∨ u∈L.wires := by
 intro u hu
 rcases List.mem_append.mp hu with hu|hu
 · exact Or.inr (work_in L u (hwork u hu))
 · exact Or.inl (List.mem_singleton.mp hu)

theorem domain_in (L:CuccaroStreamedSquareWideLayout) (u:Wire) (hu:u∈domain L) : u∈L.wires := by
 simp only [domain,List.mem_cons,List.mem_append] at hu
 rcases hu with hu|((hu|hu)|hu)|hu
 · simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hu]
 · have h := List.mem_of_mem_take (List.mem_of_mem_drop hu)
   simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
 · exact A161Fold.accReg_in L u hu
 · have h := List.mem_of_mem_drop (List.mem_of_mem_take hu)
   simp only [foldPad,List.mem_append] at h
   rcases h with h|h <;> simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]
 · have h := List.mem_of_mem_take hu
   simp only [foldPad,List.mem_append] at h
   rcases h with h|h <;> simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,h]

theorem ambient_sites_general (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g d:Wire) (hs:List Wire)
 (host:∀u∈hs,u=d ∨ u∈L.wires) :
 (ambient L g hs).toFinset⊆(d::g::L.wires).toFinset := by
 have sp : spare L∈L.core.product := DiagSq.getD_in _ 1 (by simp [hw.core.product])
 have ev : eV L∈L.core.product := List.mem_of_mem_drop (DiagSq.getD_in _ 1 (by simp [hw.core.product]))
 intro u hu
 simp only [ambient,List.mem_toFinset,List.mem_cons,List.mem_append] at hu
 simp only [List.mem_toFinset,List.mem_cons]
 rcases hu with hu|hu|hu|hu|((hu|hu)|hu)
 · tauto
 · right;right
   subst u
   simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,sp]
 · right;right
   subst u
   simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,ev]
 · right;right
   simp [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,hu]
 · exact Or.inr (Or.inr (domain_in L u hu))
 · have h := List.mem_toFinset.mp (measuredCore_in L g (List.mem_toFinset.mpr hu))
   simp only [List.mem_cons] at h
   tauto
 · rcases host u hu with h|h <;> tauto
#print axioms domain_in
#print axioms ambient_sites_general
end ECDSAAdd.Entrant.A161GenericFold

end

-- Component FixedBody
section
namespace ECDSAAdd.Entrant.A161FixedFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires checked List.toFinset

def body : Program := measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold96)

theorem ambient_sites : (A161GenericFold.ambient L g hs96).toFinset⊆(d::g::L.wires).toFinset := by
 rcases geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hwork⟩
 exact A161GenericFold.ambient_sites_general L hw g d hs96 (A161GenericFold.append_hosts L hs95 d hwork)

theorem ambient_eU : eU L∉(A161GenericFold.ambient L g hs96).toFinset := by
 simpa only [List.mem_toFinset] using (show eU L∉A161GenericFold.ambient L g hs96 from by decide)

theorem fold_support : wires fold96⊆(d::g::L.wires).toFinset :=
 (A161GenericFold.support L hw hn g hs96 checked.out cert96).trans ambient_sites

theorem fold_physical : GatePhysical fold96 :=
 A161GenericFold.physical L hw hn g hs96 checked.out ready cert96

theorem body_frame (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base g=false → M=0) (hd:base d=false) :
 Triple (SquareFrame L.core.out base O) body
  (SquareFrame L.core.out base (A161Offsets.resAF161 (M^2) O (base g))) := by
 have ff : ∀ O, O<SquareReduction.p → base (eV L)=false → base (spare L)=false →
  Triple (SquareFrame L.core.out base O) fold96
   (SquareFrame L.core.out base (((if base g then A161Facts.K161-4294968272*regValue (hiReg L) base
    else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) :=
  fun O hO hV hP => frame base hc hzero hV hP hd O hO
 exact A161Body.body_frame L hw hn g geometry.1 base M hM hP hc hzero O hO hg fold96 ff

theorem body_support : wires body⊆(d::g::L.wires).toFinset := by
 have p1 := measuredFoldQ_supportTq L g (negP L) (by
  intro u hu
  exact List.mem_of_mem_take hu)
 have p2 := measuredFoldQ_supportTq L g (rot128F L) (by
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hu)
  · exact List.mem_of_mem_take hu)
 intro u hu
 simp only [body,wires_append,Finset.mem_union] at hu
 rcases hu with hu|(hu|hu)
 · exact List.mem_toFinset.mpr (List.mem_cons_of_mem d (List.mem_toFinset.mp (p1 hu)))
 · exact List.mem_toFinset.mpr (List.mem_cons_of_mem d (List.mem_toFinset.mp (p2 hu)))
 · exact fold_support hu

theorem body_eU_free : eU L∉wires body := by
 have old : eU L∉wires (aBodyTriple L g) := fun h =>
  InverseCarryDevelop.eU_off_aBodyDual L hw hn g geometry.1 (aBodyTriple_subset L hw g h)
 simp only [aBodyTriple,wires_append,Finset.mem_union,not_or] at old
 simp only [body,wires_append,Finset.mem_union,not_or]
 refine ⟨old.1,old.2.1,?_⟩
 exact fun h => ambient_eU (A161GenericFold.support L hw hn g hs96 checked.out cert96 h)

#print axioms body_frame
#print axioms fold_physical
#print axioms body_support
#print axioms body_eU_free
end ECDSAAdd.Entrant.A161FixedFold

end

-- Component FormalCounts
section
namespace ECDSAAdd.Entrant.A161GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount

theorem counts (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (hl:hs.length=96)
 (cert:ZeroSetDevelop.SRewrites hs (A161Fold.aMiddle L g) newMiddle) :
 toffoliCount (loop L hs newMiddle)≤1287 ∧ measurementCount (loop L hs newMiddle)=1543 := by
 let acc := A161Fold.accReg L
 let pad := FullPadDevelop.pad L
 let bank := accBank L
 let src := hiReg L
 let q := L.core.sumCarry
 let r := eV L
 let p := spare L
 have ha := (A161Fold.acc_lengths L hw).1
 have hb := (A161Fold.acc_lengths L hw).2.2.1
 have hsrc : src.length=128 := hiReg_length L hw
 have hz := FullPadDevelop.pad_length L hw
 have zp : 5≤pad.length := by change 5≤(FullPadDevelop.pad L).length; omega
 have bp : 132≤bank.length := by change 132≤(accBank L).length; omega
 have fit := smallFit L hw hn
 have b := A161KnownTail.build8_counts acc pad bank L.core.cin src ha (by omega) (fun f h => (fit f h).toFitsLen)
 rw [A161KnownTail.build8_eq] at b
 have u := A161SourceAdd.unbuild_resources acc pad bank L.core.cin src ha hsrc (fun f h => (fit f h).toFitsLen)
 have bc := A161Carry.buildCached_counts acc pad bank L.core.cin src q ha hsrc zp bp
 have uc := A161Carry.unbuildConsumed_counts acc pad bank L.core.cin src q ha hsrc bp
 have bd := A161Carry.buildDual_counts acc pad bank L.core.cin src q r ha hsrc zp bp
 have ud := A161Carry.unbuildDual_counts acc pad bank L.core.cin src q r ha hsrc bp
 have bt := A161Carry.buildTriple_counts acc pad bank L.core.cin src q r p ha hsrc zp bp
 have ut := A161Carry.unbuildTriple_counts acc pad bank L.core.cin src q r p ha hsrc bp
 have mid := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
 have mask := maskedConstant_counts g (A161Fold.accReg L) A161Fold.cFlipK
 have cm := A161Carry.compiled_counts_set 96 acc pad bank L.core.cin src hs q r p
  (A161Fold.aMiddle L g) newMiddle ha hsrc zp bp (by decide) hl cert
 simp only [A161Fold.aMiddle,toffoliCount_append,measurementCount_append,mask.1,mask.2,mid.1,mid.2] at cm
 simp only [loop,toffoliCount_append,measurementCount_append]
 dsimp only [acc,pad,bank,src,q,r,p] at *
 constructor <;> omega
#print axioms counts
end ECDSAAdd.Entrant.A161GenericFold

end

-- Component Complete
section
namespace ECDSAAdd.Entrant.A161Offsets
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem complete_exact161 (enabled:Bool) (A B O:Nat) :
 SquareReduction.p-1-resAF161 ((if enabled then A else 0)^2)
  (resBF ((if enabled then B else 0)^2) (OwnDiagAll12Square.resCF enabled ((if enabled then A+B else 0)^2) O) enabled) enabled =
 (subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then squareK else 0))%SquareReduction.p := by
 let PA := (if enabled then A else 0)^2
 let OB := resBF ((if enabled then B else 0)^2) (OwnDiagAll12Square.resCF enabled ((if enabled then A+B else 0)^2) O) enabled
 have hp : 0<SquareReduction.p := by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]
 have oldlt : resAF PA OB enabled<SquareReduction.p := ofCast_lt _ _
 have newlt : resAF161 PA OB enabled<SquareReduction.p := ofCast_lt _ _
 have old := complete_exact enabled A B O
 change SquareReduction.p-1-resAF PA OB enabled=_ at old
 have oldfield : ((SquareReduction.p-1-resAF PA OB enabled:Nat):ZMod SquareReduction.p)=
  (((subModValue (if enabled then (A+2^128*B)^2 else 0) O+(if enabled then K else 0))%SquareReduction.p:Nat):ZMod SquareReduction.p) :=
  congrArg (fun n:Nat => (n:ZMod SquareReduction.p)) old
 rw [measuredReflection_zmod _ oldlt] at oldfield
 simp only [ZMod.natCast_mod,Nat.cast_add] at oldfield
 have reflectlt : SquareReduction.p-1-resAF161 PA OB enabled<SquareReduction.p := by omega
 apply measuredOrientationCast_injective false _ _ reflectlt (Nat.mod_lt _ hp)
 simp only [measuredOrientationCast,Bool.false_eq_true,if_false]
 rw [measuredReflection_zmod _ newlt,ZMod.natCast_mod,Nat.cast_add,resAF_delta]
 cases enabled
 · simpa only [Bool.false_eq_true,if_false,Nat.cast_zero,sub_zero,add_zero] using oldfield
 · simp only [if_true] at oldfield ⊢
   rw [squareK_cast]
   linear_combination oldfield
#print axioms complete_exact161
end ECDSAAdd.Entrant.A161Offsets

end
open ECDSAAdd
-- Low4 component Math
section
namespace A161Low4Math
set_option maxHeartbeats 4000000

theorem mask_xor (n v : Nat) (hv : v<2^n) :
 (2^n-1) ^^^ v=2^n-1-v := by
 apply Nat.eq_of_testBit_eq
 intro i
 rw [Nat.testBit_xor,Nat.testBit_two_pow_sub_one,
  show 2^n-1-v=2^n-(v+1) by omega,Nat.testBit_two_pow_sub_succ hv]
 by_cases h:i<n
 · simp [h]
 · have hi : n ≤ i := by omega
   have z:v.testBit i=false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) hi))
   simp [h,z]

theorem shifted_mask_xor (v : Nat) (hv:v<2^157) :
 (2^161-16) ^^^ (16*v)=2^161-16-16*v := by
 have h := @Nat.shiftLeft_xor_distrib 4 (2^157-1) v
 simp only [Nat.shiftLeft_eq] at h
 have flip : (2^161-16) ^^^ (16*v)=((2^157-1) ^^^ v)*16 := by
  norm_num only [Nat.reducePow,Nat.reduceSub] at h ⊢
  simpa only [Nat.mul_comm] using h.symm
 rw [flip,mask_xor 157 v hv]
 norm_num at hv ⊢
 omega

theorem accumulator_div16_bound (H : Nat) (hH:H<2^128) :
 268435517*H<2^157 := by
 norm_num at hH ⊢
 omega

theorem accumulator_mask_xor (H : Nat) (hH:H<2^128) :
 (2^161-16) ^^^ (4294968272*H)=2^161-16-4294968272*H := by
 have h := shifted_mask_xor (268435517*H) (accumulator_div16_bound H hH)
 simpa only [←Nat.mul_assoc,show 16*268435517=4294968272 by decide] using h
theorem mask_xor_multiple (v : Nat) (hv:v<2^161) (hz:v%16=0) :
 (2^161-16) ^^^ v=2^161-16-v := by
 have hvq : v/16<2^157 := by norm_num at hv ⊢; omega
 have h := shifted_mask_xor (v/16) hvq
 have e : 16*(v/16)=v := by omega
 simpa only [e] using h
#print axioms accumulator_mask_xor
end A161Low4Math
end

-- Low4 component Mask
section
namespace ECDSAAdd.Entrant.A161Low4Facts
open Arithmetic
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def Klow : Nat := 2^161-16

theorem complement_delta : (2^163-1)-Klow=3*2^161+15 := by
 norm_num [Klow]

theorem sub_mod16 (v : Nat) (hz:v%16=0) : (Klow-v)%16=0 := by
 norm_num [Klow]
 omega

theorem flip_run (r : List Wire) (hlen:r.length=161) (hn:r.Nodup)
 (g : Wire) (hg:g∉r) (s : State) (m : List Bool)
 (hz:regValue r s.basis%16=0) :
 (run (maskedConstant g r Klow) m s).phase=s.phase ∧
 (∀q,q∉r → (run (maskedConstant g r Klow) m s).basis q=s.basis q) ∧
 regValue r (run (maskedConstant g r Klow) m s).basis=
 (if s.basis g then Klow-regValue r s.basis else regValue r s.basis) := by
 have hk:Klow<2^r.length := by rw [hlen];norm_num [Klow]
 have h:=maskedConstant_correct g r Klow hn hg hk s m
 refine ⟨h.1,h.2.1,?_⟩
 rw [h.2.2]
 cases s.basis g
 · simp
 · simp only [if_true]
   rw [Nat.xor_comm]
   exact A161Low4Math.mask_xor_multiple _ (by simpa only [hlen] using regValue_lt r s.basis) hz
#print axioms flip_run
end ECDSAAdd.Entrant.A161Low4Facts
end

-- Low4 component Ghost
section
namespace ECDSAAdd.Entrant.A161Low4Ghost
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def ghosts (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 [L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.normFlag]
def reg (L : CuccaroStreamedSquareWideLayout) : List Wire := L.core.work.take 161
def ghostAcc (L : CuccaroStreamedSquareWideLayout) : List Wire := ghosts L ++ (reg L).drop 4

theorem ghostAcc_value (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (b : BasisState) (K : Nat) (hv : regValue (reg L) b=16*K)
 (hz : ∀w∈ghosts L,b w=false) : regValue (ghostAcc L) b=regValue (reg L) b := by
 have len : (reg L).length=161 := by simp [reg,hw.core.work]
 have low : regValue ((reg L).take 4) b=0 := by
  rw [regValue_take_mod _ 4 (by omega) b,hv]
  omega
 have old : regValue (reg L) b=16*regValue ((reg L).drop 4) b := by
  calc
   _=regValue (((reg L).take 4)++(reg L).drop 4) b := by rw [List.take_append_drop]
   _=_ := by rw [regValue_append,low];simp [len]
 have gz : regValue (ghosts L) b=0 := (regValue_zero _ _).mpr hz
 rw [ghostAcc,regValue_append,gz]
 simpa [ghosts] using old.symm

theorem ghostAcc_drop (L : CuccaroStreamedSquareWideLayout) (n : Nat) (hn : 4≤n) :
 (ghostAcc L).drop n = (reg L).drop n := by
 have gl : (ghosts L).length=4 := rfl
 have gd : (ghosts L).drop n=[] := List.drop_eq_nil_of_le (by omega)
 rw [ghostAcc,List.drop_append,gd,List.nil_append,gl,List.drop_drop]
 congr 1
 omega

theorem ghostAcc_take_drop (L : CuccaroStreamedSquareWideLayout) (w n : Nat) (hn : 4≤n) :
 ((ghostAcc L).take w).drop n = ((reg L).take w).drop n := by
 rw [List.drop_take,List.drop_take,ghostAcc_drop L n hn]

theorem ghostAcc_length (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) :
 (ghostAcc L).length=161 := by simp [ghostAcc,ghosts,reg,hw.core.work]
theorem ghosts_clean (L:CuccaroStreamedSquareWideLayout) (base:BasisState) (hc:L.PairClean base) :
 ∀q∈ghosts L,base q=false := by
 intro q hq
 simp only [ghosts,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl|rfl
 · exact hc.productHigh
 · exact hc.outHigh
 · exact hc.workHigh
 · exact hc.normFlag

theorem ghosts_out_free (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
 ∀q∈ghosts L,q∉L.core.out := by
 intro q hq
 simp only [ghosts,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl|rfl
 all_goals exact (L.pairAuxAway hn _ (by simp)).2
theorem ghostAcc_zero (L:CuccaroStreamedSquareWideLayout) (base:BasisState) (hc:L.PairClean base) :
 regValue (ghostAcc L) base=0 := by
 apply (regValue_zero _ _).mpr
 intro q hq
 rcases List.mem_append.mp hq with hq|hq
 · exact ghosts_clean L base hc q hq
 · exact (regValue_zero _ _).mp hc.work q (List.mem_of_mem_take (List.mem_of_mem_drop hq))
theorem ghosts_work_free (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
 ∀q∈ghosts L,q∉L.core.work := by
 intro q hq bad
 have parent:=List.nodup_iff_count_le_one.mp hn q
 have work:=List.count_pos_iff.mpr bad
 have flag:=List.count_pos_iff.mpr hq
 simp only [ghosts,List.count_cons,List.count_nil] at flag
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,
  List.count_cons,List.count_append,List.count_nil] at parent
 omega
#print axioms ghostAcc_value
#print axioms ghosts_clean
end ECDSAAdd.Entrant.A161Low4Ghost
end

-- Low4 component Domains
section
namespace ECDSAAdd.Entrant.A161Low4Domains
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

def smallPad (L:CuccaroStreamedSquareWideLayout) : List Wire := (L.foldPad.drop 160).take 31

theorem small_domain_nodup (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
 (L.core.cin::(hiReg L++ghostAcc L++smallPad L++accBank L)).Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro w
 have parent:=List.nodup_iff_count_le_one.mp hn w
 have src:(hiReg L).count w≤L.core.product.count w :=
  ((List.drop_sublist 128 (L.core.product.take 256)).trans (List.take_sublist 256 L.core.product)).count_le w
 have work:((reg L).drop 4).count w≤L.core.work.count w :=
  ((List.drop_sublist 4 (L.core.work.take 161)).trans (List.take_sublist 161 L.core.work)).count_le w
 have ps : (L.foldPad.take 160++(L.foldPad.drop 160).take 31).Sublist L.foldPad := by
  have h:=(List.Sublist.refl (L.foldPad.take 160)).append (List.take_sublist 31 (L.foldPad.drop 160))
  rwa [List.take_append_drop] at h
 have pb:=ps.count_le w
 simp only [List.count_append] at pb
 change (accBank L).count w+(smallPad L).count w≤L.foldPad.count w at pb
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
  List.count_cons,List.count_append,List.count_nil] at parent pb
 simp only [ghostAcc,ghosts,List.count_cons,List.count_append,List.count_nil]
 omega
theorem full_domain_nodup (L:CuccaroStreamedSquareWideLayout) (hn:L.wires.Nodup) :
 (L.core.cin::(hiReg L++ghostAcc L++accZ L++accBank L)).Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro w
 have parent:=List.nodup_iff_count_le_one.mp hn w
 have src:(hiReg L).count w≤L.core.product.count w :=
  ((List.drop_sublist 128 (L.core.product.take 256)).trans (List.take_sublist 256 L.core.product)).count_le w
 have pref : (L.core.work.take 161).Sublist (L.core.work.take 196) := by
  have h:=List.take_sublist 161 (L.core.work.take 196)
  simpa only [List.take_take,show min 161 196=161 by decide] using h
 have ws : ((reg L).drop 4++L.core.work.drop 196).Sublist L.core.work := by
  have h:=((List.drop_sublist 4 (L.core.work.take 161)).trans pref).append (List.Sublist.refl (L.core.work.drop 196))
  rwa [List.take_append_drop] at h
 have work:=ws.count_le w
 simp only [List.count_append] at work
 have pb:(L.foldPad.drop 160).count w+(accBank L).count w=L.foldPad.count w := by
  have h:=congrArg (fun xs:List Wire=>xs.count w) (List.take_append_drop 160 L.foldPad)
  simp only [List.count_append] at h
  change (L.foldPad.drop 160).count w+(L.foldPad.take 160).count w=L.foldPad.count w
  omega
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
  List.count_cons,List.count_append,List.count_nil] at parent pb
 simp only [ghostAcc,ghosts,accZ,foldPad,List.count_cons,List.count_append,List.count_nil]
 omega
#print axioms small_domain_nodup
#print axioms full_domain_nodup
end ECDSAAdd.Entrant.A161Low4Domains
end

-- Low4 component Geometry
section
namespace ECDSAAdd.Entrant.A161Low4Geometry
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
abbrev L := Baselines.layout.dialogStreamedSquareWide
abbrev g := Baselines.layout.core.generic
abbrev d := Baselines.layout.core.poolWire 1540
abbrev ga := ghostAcc L
abbrev src := hiReg L
abbrev pad := (L.foldPad.drop 160).take 31
abbrev fullPad := accZ L
abbrev bank := accBank L
abbrev q := L.core.sumCarry
abbrev r := (L.core.product.drop 256).getD 1 0
abbrev p := L.core.product.getD 1 0

def loans93 := (L.core.work.drop 163).take 33 ++ (L.core.work.drop 255).take 1 ++
 (L.core.work.drop 227).take 28 ++ (L.core.work.drop 201).take 10 ++ (L.core.work.drop 212).take 15 ++
 (L.core.work.drop 211).take 1 ++ (L.core.work.drop 196).take 5
def hs99 := (loans93++(L.core.work.drop 161).take 2)++L.core.work.take 4
def hs100 := hs99++[d]
def domain := L.core.cin::(src++ga++pad++bank)

theorem layout_nd : L.wires.Nodup :=
 Baselines.layout.dialogStreamedSquareWide_nodup Baselines.layout_widths Baselines.layout_nodup

theorem domain_nd : domain.Nodup := A161Low4Domains.small_domain_nodup L layout_nd

theorem full_domain_nd : (L.core.cin::(src++ga++fullPad++bank)).Nodup := A161Low4Domains.full_domain_nodup L layout_nd

theorem geometry : g∉L.wires ∧ hs100.length=100 ∧ hs100.Nodup ∧
 (∀u∈hs100,u∉domain) ∧ (∀u∈hs100,u≠q ∧ u≠r ∧ u≠p) ∧
 q∉domain ∧ r∉domain ∧ p∉domain ∧ r≠q ∧ p≠q ∧ p≠r ∧
 (∀u∈([q,r,p,d]:List Wire),u∉g::(L.core.work.take 161) ∧ u∉L.measuredCore.wires ∧ u∉L.core.out) ∧
 (∀u∈hs99,u∈L.core.work) := by decide

theorem smallFit : ∀f∈earlyHTerms src,Acc.Fits ga pad bank L.core.cin 161 f := by
 intro f hf
 simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
 rcases hf with rfl|rfl|rfl|rfl
 all_goals exact {len:=by decide,zpad:=by decide,bankLen:=by decide,nd:=domain_nd}

theorem fullFit : ∀f∈earlyHTerms src,Acc.Fits ga fullPad bank L.core.cin 161 f := by
 intro f hf
 simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
 rcases hf with rfl|rfl|rfl|rfl
 all_goals exact {len:=by decide,zpad:=by decide,bankLen:=by decide,nd:=full_domain_nd}
#print axioms smallFit
#print axioms geometry
end ECDSAAdd.Entrant.A161Low4Geometry
end

-- Low4 component StructuralBase
section
namespace ECDSAAdd.Entrant.A161Low4StructuralBase
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost
set_option maxHeartbeats 4000000

theorem ty (L:CuccaroStreamedSquareWideLayout) (f:MeasuredSquareFold) (h:4≤f.shift) :
 Acc.ty (ghostAcc L) f=Acc.ty (reg L) f := ghostAcc_drop L f.shift h

theorem ty_take (L:CuccaroStreamedSquareWideLayout) (w:Nat) (f:MeasuredSquareFold) (h:4≤f.shift) :
 Acc.ty ((ghostAcc L).take w) f=Acc.ty ((reg L).take w) f := ghostAcc_take_drop L w f.shift h

theorem seed_eq (L:CuccaroStreamedSquareWideLayout) (Z:List Wire) (w:Nat) (f:MeasuredSquareFold) (h:4≤f.shift) :
 Acc.seedOp (ghostAcc L) Z w f=Acc.seedOp (reg L) Z w f := by
 simp only [Acc.seedOp,ty L f h]

theorem op_eq (L:CuccaroStreamedSquareWideLayout) (Z bank:List Wire) (cin:Wire) (w:Nat)
 (negative:Bool) (f:MeasuredSquareFold) (h:4≤f.shift) :
 Acc.op (ghostAcc L) Z bank cin w negative f=Acc.op (reg L) Z bank cin w negative f := by
 simp only [Acc.op,ty L f h]

theorem op_take_eq (L:CuccaroStreamedSquareWideLayout) (Z bank:List Wire) (cin:Wire) (w:Nat)
 (negative:Bool) (f:MeasuredSquareFold) (h:4≤f.shift) :
 Acc.op ((ghostAcc L).take w) Z bank cin w negative f=Acc.op ((reg L).take w) Z bank cin w negative f := by
 simp only [Acc.op,ty_take L w f h]
#print axioms seed_eq
#print axioms op_take_eq
end ECDSAAdd.Entrant.A161Low4StructuralBase
end

-- Low4 component Structural
section
namespace ECDSAAdd.Entrant.A161Low4Structural
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout A161Low4Ghost
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false

-- Uses the retained ghost-register structural technique from LowAccCarry.lean.
theorem ty (L:CuccaroStreamedSquareWideLayout) (src:List Wire) (neg:Bool) (n:Nat) (hn:4≤n) :
 Acc.ty (ghostAcc L) (Acc.earlyTerm src neg n)=Acc.ty (A161Fold.accReg L) (Acc.earlyTerm src neg n) := by
 change (ghostAcc L).drop n=(reg L).drop n
 exact ghostAcc_drop L n hn

theorem ty_take (L:CuccaroStreamedSquareWideLayout) (src:List Wire) (neg:Bool) (w n:Nat) (hn:4≤n) :
 Acc.ty ((ghostAcc L).take w) (Acc.earlyTerm src neg n)=Acc.ty ((A161Fold.accReg L).take w) (Acc.earlyTerm src neg n) := by
 change ((ghostAcc L).take w).drop n=((reg L).take w).drop n
 exact ghostAcc_take_drop L w n hn

theorem build_eq (L:CuccaroStreamedSquareWideLayout) (Z bank src:List Wire) (cin:Wire) :
 A161NarrowAcc.build8 (ghostAcc L) Z bank cin src=A161NarrowAcc.build8 (A161Fold.accReg L) Z bank cin src := by
 simp only [A161NarrowAcc.build8,A161NarrowAcc.pre8,CodexNarrowSub.accSub,Acc.seedOp,Acc.op]
 rw [ty L src false 4 (by decide),ty_take L src false 139 10 (by decide),
  ty_take L src true 139 6 (by decide),ty_take L src false 161 32 (by decide)]

theorem unbuild_eq (L:CuccaroStreamedSquareWideLayout) (Z bank src:List Wire) (cin:Wire) :
 A161SourceAdd.unbuild (ghostAcc L) Z bank cin src=A161SourceAdd.unbuild (A161Fold.accReg L) Z bank cin src := by
 simp only [A161SourceAdd.unbuild,CodexKnownOnesTail.accSub,A161SourceAdd.add,A161SourceTail.tail,Acc.seedOp]
 rw [ty_take L src false 161 32 (by decide),ghostAcc_take_drop L 139 6 (by decide),
  ghostAcc_take_drop L 139 10 (by decide),ty L src false 4 (by decide)]
 all_goals rfl

theorem buildMany_eq (L:CuccaroStreamedSquareWideLayout) (k:Nat) (Z bank src hs:List Wire) (cin q r p:Wire) :
 A161Carry.buildMany k (ghostAcc L) Z bank cin src hs q r p=
 A161Carry.buildMany k (A161Fold.accReg L) Z bank cin src hs q r p := by
 simp only [A161Carry.buildMany,A161Carry.buildPre,A161Carry.buildPost,Acc.seedOp,Acc.op]
 rw [ty L src false 4 (by decide),ty_take L src false 139 10 (by decide),
  ty_take L src true 139 6 (by decide),ty_take L src false 161 32 (by decide)]

theorem unbuildMany_eq (L:CuccaroStreamedSquareWideLayout) (k:Nat) (Z bank src hs:List Wire) (cin q r p:Wire) :
 A161Carry.unbuildMany k (ghostAcc L) Z bank cin src hs q r p=
 A161Carry.unbuildMany k (A161Fold.accReg L) Z bank cin src hs q r p := by
 simp only [A161Carry.unbuildMany,A161Carry.unbuildPre,A161Carry.unbuildPost,CodexKnownOnesTail.accSub,A161SourceTail.tail,Acc.seedOp]
 rw [ty_take L src false 161 32 (by decide),ghostAcc_take_drop L 139 6 (by decide),
  ghostAcc_take_drop L 139 10 (by decide),ty L src false 4 (by decide)]
 all_goals rfl
#print axioms buildMany_eq
#print axioms unbuildMany_eq
end ECDSAAdd.Entrant.A161Low4Structural
end

-- Low4 component InputEq
section
namespace ECDSAAdd.Entrant.A161Low4Facts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000
set_option linter.unusedSimpArgs false
def acc161 := A161Facts.acc161
def maskTargets : List Wire := [4501,4502,4503,4504,4662,4663]
def trimMasks (P:Program) : Program :=
 P.filter (fun i => decide (i≠.CX 4113 4501 ∧ i≠.CX 4113 4502 ∧ i≠.CX 4113 4503 ∧
  i≠.CX 4113 4504 ∧ i≠.CX 4113 4662 ∧ i≠.CX 4113 4663))
def pLow := trimMasks ParkAData.p0
def middleLow (L:CuccaroStreamedSquareWideLayout) (g:Wire) : Program :=
 maskedConstant g (acc161 L) Klow++(qprogTq L.measuredCore SquareReduction.p++maskedConstant g (acc161 L) Klow)

theorem trimMasks_append (P Q : Program) :
 trimMasks (P++Q)=trimMasks P++trimMasks Q := List.filter_append P Q

theorem trimMasks_eq (P : Program) (hg : 4113∉wires P) : trimMasks P=P := by
 induction P with
 | nil => rfl
 | cons i P ih =>
   have hgi : 4113∉i.wires := fun h => hg (Finset.mem_union_left _ h)
   have hgp : 4113∉wires P := fun h => hg (Finset.mem_union_right _ h)
   have neq (w : Wire) : i≠.CX 4113 w := by
    intro e;subst i;exact hgi (by simp [Instr.wires])
   have keep : decide (i≠.CX 4113 4501 ∧ i≠.CX 4113 4502 ∧ i≠.CX 4113 4503 ∧
    i≠.CX 4113 4504 ∧ i≠.CX 4113 4662 ∧ i≠.CX 4113 4663)=true := by simp [neq]
   simp only [trimMasks,List.filter_cons,keep,ite_true]
   exact congrArg (List.cons i) (ih hgp)

set_option maxRecDepth 100000
set_option maxHeartbeats 500000000

theorem trim_mask :
 trimMasks (maskedConstant A161FixedFold.g (accReg A161FixedFold.L)
   OwnDiagAll12Square.cFlipK)=maskedConstant A161FixedFold.g (acc161 A161FixedFold.L) Klow := by
 rfl

theorem trim_core_general (K : MeasuredCanonicalModLayout) (p : Nat)
 (free : 4113∉K.wires.toFinset) : trimMasks (qprogTq K p)=qprogTq K p :=
 trimMasks_eq (qprogTq K p) (fun h => free (QCore.qprog_supportTq K p h))

theorem trim_core : trimMasks (qprogTq A161FixedFold.L.measuredCore SquareReduction.p)=
 qprogTq A161FixedFold.L.measuredCore SquareReduction.p := by
 have freeList : 4113∉A161FixedFold.L.measuredCore.wires := by decide
 have freeSet : 4113∉A161FixedFold.L.measuredCore.wires.toFinset := by
  simpa only [List.mem_toFinset] using freeList
 exact trim_core_general A161FixedFold.L.measuredCore SquareReduction.p freeSet

theorem input_eq : pLow=middleLow A161FixedFold.L A161FixedFold.g := by
 let A := maskedConstant A161FixedFold.g (accReg A161FixedFold.L) OwnDiagAll12Square.cFlipK
 let Q := qprogTq A161FixedFold.L.measuredCore SquareReduction.p
 let N := maskedConstant A161FixedFold.g (acc161 A161FixedFold.L) Klow
 calc
  pLow=trimMasks (InverseCarryDevelop.aMiddle A161FixedFold.L A161FixedFold.g) :=
   congrArg trimMasks ParkAStagedProof.input_eq
  _ = trimMasks A++(trimMasks Q++trimMasks A) :=
   (trimMasks_append A (Q++A)).trans
    (congrArg (fun t => trimMasks A++t) (trimMasks_append Q A))
  _ = N++(Q++N) :=
   congrArg₂ (fun (P R : Program) => P++R) trim_mask
    (congrArg₂ (fun (P R : Program) => P++R) trim_core trim_mask)
  _ = middleLow A161FixedFold.L A161FixedFold.g := rfl

#print axioms input_eq

end ECDSAAdd.Entrant.A161Low4Facts
end

-- Low4 component Compile99
section
namespace ECDSAAdd.Entrant.A161Low4Facts
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 500000000

def hs99 := A161Facts.loans95 A161FixedFold.L++A161FixedFold.L.core.work.take 4

theorem compiled99 : (ZeroSetDevelop.compileS? hs99 pLow).isSome=true := by
 decide +kernel
#print axioms compiled99
end ECDSAAdd.Entrant.A161Low4Facts
end

-- Low4 component Plain
section
namespace ECDSAAdd.Entrant.A161Low4Fold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop
 ControlLoan1589BFFold ThirdSavedCarryDevelop ZeroReadDevelop A161Fold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires
abbrev accReg := A161Fold.accReg
abbrev acc_lengths := A161Fold.acc_lengths
abbrev accReg_work := A161Fold.accReg_work
abbrev accReg_in := A161Fold.accReg_in
abbrev accReg_nodup := A161Fold.accReg_nodup
abbrev wTerms_fits := A161Fold.wTerms_fits
abbrev wBuild := A161Fold.wBuild
abbrev wUnbuild := A161Fold.wUnbuild
abbrev workSplit := A161Fold.workSplit
abbrev other_away := A161Fold.other_away
abbrev accReg_away := A161Fold.accReg_away
abbrev cFlipK := A161Low4Facts.Klow

def aMiddle (L:CuccaroStreamedSquareWideLayout) (g:Wire) : Program :=
 maskedConstant g (accReg L) cFlipK++(qprogTq L.measuredCore SquareReduction.p++maskedConstant g (accReg L) cFlipK)

theorem flip_run (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉accReg L) (s:State) (m:List Bool) (hz:regValue (accReg L) s.basis%16=0) :
 (run (maskedConstant g (accReg L) cFlipK) m s).phase=s.phase ∧
 (∀q,q∉accReg L → (run (maskedConstant g (accReg L) cFlipK) m s).basis q=s.basis q) ∧
 regValue (accReg L) (run (maskedConstant g (accReg L) cFlipK) m s).basis=
 (if s.basis g then cFlipK-regValue (accReg L) s.basis else regValue (accReg L) s.basis) :=
 A161Low4Facts.flip_run _ (acc_lengths L hw).1 (accReg_nodup L hn) g hg s m hz

theorem a_middle_good (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
    (g : Wire) (hg:g∉L.wires) (base : BasisState) (hc:L.PairClean base) (O : Nat) (hO:O<SquareReduction.p)
    (s : State) (m : List Bool) (hf:SquareFrame L.core.out base O s.basis) :
    let u:=middleState (wBuild L) (aMiddle L g) s m
    regValue (accReg L) u.basis=4294968272*regValue (hiReg L) s.basis ∧
    regValue (hiReg L) u.basis=regValue (hiReg L) s.basis ∧
    (∀w∈accZ L,u.basis w=false) ∧ (∀w∈accBank L,u.basis w=false) ∧ u.basis L.core.cin=false ∧
    (∀q,q∉accReg L → q∉L.core.out → u.basis q=s.basis q) := by
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
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := 4294968272*regValue (hiReg L) base
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^161 := by
    show 4294968272*regValue (hiReg L) base<2^161
    norm_num at hH ⊢
    omega
  have hAM : A%16=0 := by dsimp only [A];omega
  have hAK : A≤cFlipK := by unfold cFlipK A161Low4Facts.Klow;norm_num at hA ⊢;omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^161 := by
    simp only [A']; split
    · unfold cFlipK A161Low4Facts.Klow; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hhi : regValue (hiReg L) b0=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => agree0 q (hiReg_product L q hq))
  have hbuild : Triple (SquareFrame (accReg L) b0 0) (wBuild L) (SquareFrame (accReg L) b0 A) := by
    have h := A161NarrowAcc.build8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) b0 hz hb clean.cin
    rw [hhi] at h
    exact h
  let mb := measurementCount (wBuild L)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (wBuild L) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc) (by rw [eu.2.1];exact hAM)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis
      else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 161) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 161) (L.core.work.drop 161) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 161) u1.basis=0 :=
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
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have hAM' : A'%16=0 := by
    dsimp only [A']
    split
    · exact A161Low4Facts.sub_mod16 A hAM
    · exact hAM
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc) (by rw [accV];exact hAM')
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis
      else regValue (accReg L) v.basis) at fl2
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
  have hhi2 : regValue (hiReg L) base2=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => (b2off q (prodNotOut q (hiReg_product L q hq))).trans
      (agree0 q (hiReg_product L q hq)))
  have offAcc (q : Wire) (hq:q∈hiReg L ∨ q∈L.foldPad ∨ q∈L.core.work.drop 161 ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉accReg L := by
    apply (other_away L hn q ?_).2.2
    tauto
  have source:regValue (hiReg L) v1.basis=regValue (hiReg L) base :=
    (regValue_congr _ _ _ (fun q hq=>frame2.2 q (offAcc q (Or.inl hq)))).trans hhi2
  have zv:∀q∈accZ L,v1.basis q=false := by
    intro q hq
    have na:q∉accReg L := by
      rcases accZ_mem L q hq with h|h
      · exact offAcc q (Or.inr (Or.inl h))
      · apply offAcc q
        have hd:(L.core.work.drop 161).drop 35=L.core.work.drop 196 := by simp [List.drop_drop]
        rw [←hd] at h
        exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
    exact (frame2.2 q na).trans (hz2 q hq)
  have bv:∀q∈accBank L,v1.basis q=false := by
    intro q hq
    exact (frame2.2 q (offAcc q (Or.inr (Or.inl (List.mem_of_mem_take hq))))).trans (hb2 q hq)
  have iv:v1.basis L.core.cin=false :=
    (frame2.2 _ (offAcc _ (by simp))).trans hi2
  have midEq:middleState (wBuild L) (aMiddle L g) s m=v1 := by
    simp only [middleState,aMiddle,run_append,measurementCount_append,
      (maskedConstant_counts _ _ _).2,Nat.zero_add,Nat.add_zero,List.take_zero,List.drop_zero,List.drop_drop]
    dsimp only [v1,v,u1,u,m3,m2,m1,mc,mb,mk]
    simp only [(maskedConstant_counts _ _ _).2,List.take_zero,List.drop_zero,Nat.add_zero,List.take_take,Nat.min_self,List.drop_take,Nat.sub_self]
  rw [midEq]
  exact ⟨frame2.1.trans (by rw [hhi]),source.trans hhi.symm,zv,bv,iv,
    fun q ha ho=>(frame2.2 q ha).trans (b2off q ho)⟩
#print axioms a_middle_good

theorem plain_frame (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (O:Nat) (hO:O<SquareReduction.p) :
 Triple (SquareFrame L.core.out base O) ((wBuild L++aMiddle L g)++wUnbuild L)
  (SquareFrame L.core.out base
   (((if base g then cFlipK-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
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
  have prodNotOut (q : Wire) (hq : q∈L.core.product) : q∉L.core.out :=
    fun ho => List.disjoint_left.mp prodOut hq ho
  have agree0 : ∀q∈L.core.product,b0 q=base q := fun q hq => hf.2 q (prodNotOut q hq)
  let A := 4294968272*regValue (hiReg L) base
  have hH : regValue (hiReg L) base<2^128 := by
    have h := regValue_lt (hiReg L) base
    rwa [hiReg_length L hw] at h
  have hA : A<2^161 := by
    show 4294968272*regValue (hiReg L) base<2^161
    norm_num at hH ⊢
    omega
  have hAM : A%16=0 := by dsimp only [A];omega
  have hAK : A≤cFlipK := by unfold cFlipK A161Low4Facts.Klow;norm_num at hA ⊢;omega
  let A' := if base g then cFlipK-A else A
  have hA' : A'<2^161 := by
    simp only [A']; split
    · unfold cFlipK A161Low4Facts.Klow; omega
    · exact hA
  have accZero : regValue (accReg L) b0=0 :=
    (regValue_zero _ _).mpr (fun q hq => workZero q (accReg_work L q hq))
  have hhi : regValue (hiReg L) b0=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => agree0 q (hiReg_product L q hq))
  have hbuild : Triple (SquareFrame (accReg L) b0 0) (wBuild L) (SquareFrame (accReg L) b0 A) := by
    have h := A161NarrowAcc.build8_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
      lens.1 (by rw [hiReg_length L hw]) (wTerms_fits L hw hn) b0 hz hb clean.cin
    rw [hhi] at h
    exact h
  let mb := measurementCount (wBuild L)
  let m1 := m.drop mb
  let mc := measurementCount (maskedConstant g (accReg L) cFlipK)
  let m2 := m1.drop mc
  let mk := measurementCount (qprogTq L.measuredCore SquareReduction.p)
  let m3 := m2.drop mk
  let u := run (wBuild L) (m.take mb) s
  have eu := hbuild s (m.take mb) ⟨accZero,fun _ _ => rfl⟩
  change u.phase=s.phase ∧ SquareFrame (accReg L) b0 A u.basis at eu
  have gU : u.basis g=base g := (eu.2.2 g gAcc).trans (hf.2 g gOut)
  let u1 := run (maskedConstant g (accReg L) cFlipK) (m1.take mc) u
  have fl := flip_run L hw hn g gAcc u (m1.take mc) (by rw [eu.2.1];exact hAM)
  change u1.phase=u.phase ∧ (∀q,q∉accReg L → u1.basis q=u.basis q) ∧
    regValue (accReg L) u1.basis=(if u.basis g then cFlipK-regValue (accReg L) u.basis
      else regValue (accReg L) u.basis) at fl
  rw [gU,eu.2.1] at fl
  have accU1 : regValue (accReg L) u1.basis=A' := fl.2.2
  have keepU (q : Wire) (hq : q∈L.foldPad++[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,
      L.core.normFlag,L.core.modFlag]++L.core.out++L.core.product++L.core.work.drop 161) : u1.basis q=b0 q :=
    (fl.2.1 q (accReg_away L hn q hq)).trans (eu.2.2 q (accReg_away L hn q hq))
  have workU : regValue L.core.work u1.basis=A' := by
    have sp := regValue_append (L.core.work.take 161) (L.core.work.drop 161) u1.basis
    rw [List.take_append_drop] at sp
    have hi : regValue (L.core.work.drop 161) u1.basis=0 :=
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
  have ek := QCore.qprog_correctTq L.measuredCore 256 SquareReduction.c SquareReduction.p (L.measuredCore_widths hw)
    coreNd (by decide) hp (by norm_num [SquareReduction.c]) A' O hAp hO u1 (m2.take mk)
    workU outU ((keepU _ (by simp [measuredCore])).trans clean.outHigh)
    ((keepU _ (by simp [measuredCore])).trans clean.modFlag)
    carryU ((keepU _ (by simp [measuredCore])).trans clean.cin)
  let v := run (qprogTq L.measuredCore SquareReduction.p) (m2.take mk) u1
  change v.phase=u1.phase ∧ regValue L.core.out v.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p ∧
    ∀q,q∉L.core.out → v.basis q=u1.basis q at ek
  have accOut (q : Wire) (hq : q∈accReg L) : q∉L.core.out := auxAway q (by simp [accReg_work L q hq])
  have gV : v.basis g=base g := (ek.2.2 g gOut).trans ((fl.2.1 g gAcc).trans gU)
  have accV : regValue (accReg L) v.basis=A' :=
    (regValue_congr _ _ _ (fun q hq => ek.2.2 q (accOut q hq))).trans accU1
  let v1 := run (maskedConstant g (accReg L) cFlipK) (m3.take mc) v
  have hAM' : A'%16=0 := by
    dsimp only [A']
    split
    · exact A161Low4Facts.sub_mod16 A hAM
    · exact hAM
  have fl2 := flip_run L hw hn g gAcc v (m3.take mc) (by rw [accV];exact hAM')
  change v1.phase=v.phase ∧ (∀q,q∉accReg L → v1.basis q=v.basis q) ∧
    regValue (accReg L) v1.basis=(if v.basis g then cFlipK-regValue (accReg L) v.basis
      else regValue (accReg L) v.basis) at fl2
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
  have hhi2 : regValue (hiReg L) base2=regValue (hiReg L) base :=
    regValue_congr _ _ _ (fun q hq => (b2off q (prodNotOut q (hiReg_product L q hq))).trans
      (agree0 q (hiReg_product L q hq)))
  have offAcc (q : Wire) (hq:q∈hiReg L ∨ q∈L.foldPad ∨ q∈L.core.work.drop 161 ∨
      q∈[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,L.core.modFlag]) : q∉accReg L := by
    apply (other_away L hn q ?_).2.2
    tauto
  have source:regValue (hiReg L) v1.basis=regValue (hiReg L) base :=
    (regValue_congr _ _ _ (fun q hq=>frame2.2 q (offAcc q (Or.inl hq)))).trans hhi2
  have zv:∀q∈accZ L,v1.basis q=false := by
    intro q hq
    have na:q∉accReg L := by
      rcases accZ_mem L q hq with h|h
      · exact offAcc q (Or.inr (Or.inl h))
      · apply offAcc q
        have hd:(L.core.work.drop 161).drop 35=L.core.work.drop 196 := by simp [List.drop_drop]
        rw [←hd] at h
        exact Or.inr (Or.inr (Or.inl (List.mem_of_mem_drop h)))
    exact (frame2.2 q na).trans (hz2 q hq)
  have bv:∀q∈accBank L,v1.basis q=false := by
    intro q hq
    exact (frame2.2 q (offAcc q (Or.inr (Or.inl (List.mem_of_mem_take hq))))).trans (hb2 q hq)
  have iv:v1.basis L.core.cin=false :=
    (frame2.2 _ (offAcc _ (by simp))).trans hi2
  have midEq:middleState (wBuild L) (aMiddle L g) s m=v1 := by
    simp only [middleState,aMiddle,run_append,measurementCount_append,
      (maskedConstant_counts _ _ _).2,Nat.zero_add,Nat.add_zero,List.take_zero,List.drop_zero,List.drop_drop]
    dsimp only [v1,v,u1,u,m3,m2,m1,mc,mb,mk]
    simp only [(maskedConstant_counts _ _ _).2,List.take_zero,List.drop_zero,Nat.add_zero,List.take_take,Nat.min_self,List.drop_take,Nat.sub_self]
  let post := m.drop (measurementCount (wBuild L)+measurementCount (aMiddle L g))
  have pre2 : SquareFrame (accReg L) base2 (4294968272*regValue (hiReg L) base2) v1.basis := by
    simpa only [hhi2] using frame2
  have inv := A161SourceAdd.unbuild_triple (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L)
    lens.1 (hiReg_length L hw) (wTerms_fits L hw hn) base2 hz2 hb2 hi2 v1 post pre2
  have valuev1 : regValue L.core.out v1.basis=(A'+(SquareReduction.p-1-O))%SquareReduction.p :=
    (regValue_congr _ _ _ (fun q hq => fl2.2.1 q (fun ha => accOut q ha hq))).trans ek.2.1
  have firstTwo : run (wBuild L++aMiddle L g) m s=middleState (wBuild L) (aMiddle L g) s m := by
    simp only [middleState,run_take]
    exact run_cat _ _ _ _
  have loop : run ((wBuild L++aMiddle L g)++wUnbuild L) m s=
    run (wUnbuild L) post (middleState (wBuild L) (aMiddle L g) s m) := by
    rw [run_cat (wBuild L++aMiddle L g) (wUnbuild L) m s,measurementCount_append,firstTwo]
  rw [loop,midEq]
  refine ⟨inv.1.trans (fl2.1.trans (ek.1.trans (fl.1.trans eu.1))),?_,?_⟩
  · have agreeOut : ∀q∈L.core.out,(run (wUnbuild L) post v1).basis q=v1.basis q := by
      intro q hq
      exact (inv.2.2 q (fun ha => accOut q ha hq)).trans (by simp [base2,hq])
    exact (regValue_congr _ _ _ agreeOut).trans valuev1
  · intro q hq
    by_cases ha:q∈accReg L
    · have outZero := (regValue_zero _ _).mp inv.2.1 q ha
      have oldZero := (regValue_zero _ _).mp hc.work q (accReg_work L q ha)
      exact outZero.trans oldZero.symm
    · exact (inv.2.2 q ha).trans ((b2off q hq).trans (hf.2 q hq))

#print axioms plain_frame

end ECDSAAdd.Entrant.A161Low4Fold
end

-- Low4 component GhostReady
section
namespace ECDSAAdd.Entrant.A161Low4Fold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold A161Low4Ghost A161Fold InverseCarryDevelop
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem ghost_middle_good (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hg:g∉L.wires) (base:BasisState) (hc:L.PairClean base) (O:Nat) (hO:O<SquareReduction.p)
 (s:State) (m:List Bool) (hf:SquareFrame L.core.out base O s.basis) :
 let u:=middleState (wBuild L) (aMiddle L g) s m
 regValue (ghostAcc L) u.basis=4294968272*regValue (hiReg L) s.basis ∧
 regValue (hiReg L) u.basis=regValue (hiReg L) s.basis ∧
 (∀w∈accZ L,u.basis w=false) ∧ (∀w∈accBank L,u.basis w=false) ∧ u.basis L.core.cin=false := by
 let u:=middleState (wBuild L) (aMiddle L g) s m
 have h:=a_middle_good L hw hn g hg base hc O hO s m hf
 have clean:=L.squareFrame_clean hn base s.basis O hf hc
 have gz:∀q∈ghosts L,u.basis q=false := by
  intro q hq
  have na:q∉accReg L := fun bad=>ghosts_work_free L hn q hq (accReg_work L q bad)
  have no:=ghosts_out_free L hn q hq
  exact (h.2.2.2.2.2 q na no).trans (ghosts_clean L s.basis clean q hq)
 have val:regValue (reg L) u.basis=16*(268435517*regValue (hiReg L) s.basis) := by
  change regValue (accReg L) u.basis=16*(268435517*regValue (hiReg L) s.basis)
  rw [h.1]
  omega
 have eq:=ghostAcc_value L hw u.basis (268435517*regValue (hiReg L) s.basis) val gz
 exact ⟨eq.trans h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1⟩
#print axioms ghost_middle_good
end ECDSAAdd.Entrant.A161Low4Fold
end

-- Low4 component GenericFold
section
namespace ECDSAAdd.Entrant.A161Low4GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop A161Low4Ghost
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ECDSAAdd.measurementCount ECDSAAdd.toffoliCount

def domain (L : CuccaroStreamedSquareWideLayout) : List Wire :=
 L.core.cin::(hiReg L++ghostAcc L++FullPadDevelop.pad L++accBank L)

def Ready (L : CuccaroStreamedSquareWideLayout) (g : Wire) (hs : List Wire) : Prop :=
 g∉L.wires ∧ hs.length=100 ∧ hs.Nodup ∧
 (∀u∈hs,u∉domain L) ∧ (∀u∈hs,u≠L.core.sumCarry ∧ u≠eV L ∧ u≠spare L) ∧
 L.core.sumCarry∉domain L ∧ eV L∉domain L ∧ spare L∉domain L ∧
 eV L≠L.core.sumCarry ∧ spare L≠L.core.sumCarry ∧ spare L≠eV L ∧
 (∀u∈([L.core.sumCarry,eV L,spare L] : List Wire),
   u∉g::A161Fold.accReg L ∧ u∉L.measuredCore.wires ∧ u∉L.core.out)

def loop (L : CuccaroStreamedSquareWideLayout) (hs : List Wire) (middle : Program) : Program :=
 A161Carry.buildMany 100 (A161Fold.accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L)++middle++
 A161Carry.unbuildMany 100 (A161Fold.accReg L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L)

theorem smallFit (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (ghostAcc L) (FullPadDevelop.pad L) (accBank L) L.core.cin 161 f := by
 intro f hf
 have old:=A161GenericFold.smallFit L hw hn f hf
 have src:f.src=hiReg L := by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> rfl
 exact {toFitsLen:=old.toFitsLen,nd:=by rw [src];exact A161Low4Domains.small_domain_nodup L hn}

theorem fullFit (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup) :
 ∀f∈earlyHTerms (hiReg L),Acc.Fits (ghostAcc L) (accZ L) (accBank L) L.core.cin 161 f := by
 intro f hf
 have old:=A161Fold.wTerms_fits L hw hn f hf
 have src:f.src=hiReg L := by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl <;> rfl
 exact {toFitsLen:=old.toFitsLen,nd:=by rw [src];exact A161Low4Domains.full_domain_nodup L hn}

theorem loop_eq_ghost (L:CuccaroStreamedSquareWideLayout) (hs:List Wire) (P:Program) :
 loop L hs P=A161Carry.buildMany 100 (ghostAcc L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L)++P++
 A161Carry.unbuildMany 100 (ghostAcc L) (FullPadDevelop.pad L) (accBank L) L.core.cin (hiReg L) hs
  L.core.sumCarry (eV L) (spare L) := by
 unfold loop
 rw [←A161Low4Structural.buildMany_eq L 100,←A161Low4Structural.unbuildMany_eq L 100]

theorem free_middle (L : CuccaroStreamedSquareWideLayout) (g u : Wire)
 (ha:u∉g::A161Fold.accReg L) (hc:u∉L.measuredCore.wires) : u∉wires (A161Low4Fold.aMiddle L g) := by
 have hm : u∉wires (maskedConstant g (A161Fold.accReg L) A161Low4Facts.Klow) := by
  intro h
  exact ha (List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h))
 have hk : u∉wires (qprogTq L.measuredCore SquareReduction.p) := by
  have hc' : u∉L.measuredCore.wires.toFinset := by simpa only [List.mem_toFinset] using hc
  exact fun h => hc' (QCore.qprog_supportTq L.measuredCore SquareReduction.p h)
 intro h
 simp only [A161Low4Fold.aMiddle,wires_append,Finset.mem_union] at h
 exact h.elim hm (fun h => h.elim hk hm)

theorem eq_plain (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (ready:Ready L g hs)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle)
 (base:BasisState) (hc:L.PairClean base) (hsum:base L.core.sumCarry=false)
 (hV:base (eV L)=false) (hP:base (spare L)=false)
 (O:Nat) (hO:O<SquareReduction.p) (s:State) (m:List Bool)
 (hf:SquareFrame L.core.out base O s.basis) (zeroU:∀u∈hs,s.basis u=false) :
 run (loop L hs newMiddle) m s=
 run ((A161Fold.wBuild L++A161Low4Fold.aMiddle L g)++A161Fold.wUnbuild L) m s := by
  rw [loop_eq_ghost]
  let acc := ghostAcc L
  let pad := FullPadDevelop.pad L
  let bank := accBank L
  let src := hiReg L
  let q := L.core.sumCarry
  let r := eV L
  let p := spare L
  let middleProgram := A161Low4Fold.aMiddle L g
  have smallFit := smallFit L hw hn
  rcases ready with ⟨hg,hlen,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,fmid⟩
  have lens := A161Fold.acc_lengths L hw
  have haLen:acc.length=161:=ghostAcc_length L hw
  have hsrc := hiReg_length L hw
  have fullfit := fullFit L hw hn
  have clean := L.squareFrame_clean hn base s.basis O hf hc
  have hzFull : ∀u∈accZ L,s.basis u=false := by
   intro u hu
   rcases accZ_mem L u hu with hu|hu
   · exact (regValue_zero _ _).mp clean.pad u hu
   · exact (regValue_zero _ _).mp clean.work u (List.mem_of_mem_drop hu)
  have hz : ∀u∈pad,s.basis u=false := fun u hu => hzFull u ((FullPadDevelop.pad_sublist L).subset hu)
  have hb : ∀u∈bank,s.basis u=false := fun u hu => (regValue_zero _ _).mp clean.pad u (List.mem_of_mem_take hu)
  have ha : regValue acc s.basis=0 := ghostAcc_zero L s.basis clean
  have zq := (hf.2 q (fmid q (by simp [q,r,p])).2.2).trans hsum
  have zr := (hf.2 r (fmid r (by simp [q,r,p])).2.2).trans hV
  have zp := (hf.2 p (fmid p (by simp [q,r,p])).2.2).trans hP
  have offq := A161Carry.wloop_original_off acc pad bank L.core.cin src q haLen hsrc smallFit fq
  have offr := A161Carry.wloop_original_off acc pad bank L.core.cin src r haLen hsrc smallFit fr
  have offp := A161Carry.wloop_original_off acc pad bank L.core.cin src p haLen hsrc smallFit fp
  have plen := FullPadDevelop.pad_length L hw
  have blen := lens.2.2.1
  have bd := A161Carry.buildDual_support acc pad bank L.core.cin src q r haLen hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have ud := A161Carry.unbuildDual_support acc pad bank L.core.cin src q r haLen hsrc (by change 132≤(accBank L).length; omega)
  have b0 := A161Carry.buildCached_support acc pad bank L.core.cin src q haLen hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have u0 := A161Carry.unbuildConsumed_support acc pad bank L.core.cin src q haLen hsrc (by change 132≤(accBank L).length; omega)
  have offpd : p∉wires (A161Carry.buildDual acc pad bank L.core.cin src q r) ∧
   p∉wires (A161Carry.unbuildDual acc pad bank L.core.cin src q r) := by
   constructor
   · intro h
     exact (Finset.mem_insert.mp (bd h)).elim pr (fun h => (Finset.mem_insert.mp (b0 h)).elim pq offp.1)
   · intro h
     exact (Finset.mem_insert.mp (ud h)).elim pr (fun h => (Finset.mem_insert.mp (u0 h)).elim pq offp.2)
  have offU (u:Wire) (hu:u∈hs) := A161Carry.fresh_off_triple acc pad bank L.core.cin src q r p u
   haLen hsrc smallFit (hfresh u hu) (hne u hu).1 (hne u hu).2.1 (hne u hu).2.2
  have mq := free_middle L g q (fmid q (by simp [q,r,p])).1 (fmid q (by simp [q,r,p])).2.1
  have mr := free_middle L g r (fmid r (by simp [q,r,p])).1 (fmid r (by simp [q,r,p])).2.1
  have mp := free_middle L g p (fmid p (by simp [q,r,p])).1 (fmid p (by simp [q,r,p])).2.1
  have oldGood := A161Low4Fold.ghost_middle_good L hw hn g hg base hc O hO s m hf
  simp only [A161Fold.wBuild] at oldGood
  rw [←A161Low4Structural.build_eq L] at oldGood
  have middleEq := A161Repad.middle_repad acc (accZ L) pad bank L.core.cin src middleProgram haLen hsrc fullfit smallFit
   s m hzFull hz hb clean.cin ha
  have good : WReady acc pad bank L.core.cin src (regValue src s.basis)
   (middleState (A161NarrowAcc.build8 acc pad bank L.core.cin src) middleProgram s m) := by
   rw [←middleEq]
   exact ⟨oldGood.1,oldGood.2.1,(fun u hu => oldGood.2.2.1 u ((FullPadDevelop.pad_sublist L).subset hu)),oldGood.2.2.2⟩
  have eq := A161Carry.compiled_wloop_many_eq_set 100 acc pad bank L.core.cin src hs q r p middleProgram newMiddle
   haLen hsrc smallFit s m hz hb clean.cin ha zq zr zp fq fr rq fp pq pr
   offq.1 mq offq.2 offr.1 mr offr.2 offpd.1 mp offpd.2
   (by decide) hnd hlen zeroU hfresh hne (fun u hu => (offU u hu).1) (fun u hu => (offU u hu).2) cert good
  have plain := A161Carry.triple_plain_eq acc pad bank L.core.cin src q r p middleProgram haLen hsrc smallFit
   s m hz hb clean.cin ha zq zr zp fq fr rq fp pq pr offq.1 mq offq.2 offr.1 mr offr.2 offpd.1 mp offpd.2 good
  have repad := A161Repad.plain_loop_repad acc (accZ L) pad bank L.core.cin src middleProgram haLen hsrc fullfit smallFit
   (FullPadDevelop.pad_sublist L).subset s m hzFull hb clean.cin ha (regValue src s.basis)
   (by simpa only [middleState,run_take] using oldGood)
  have combine := eq.trans (plain.trans repad.symm)
  have assoc : ((A161Fold.wBuild L++middleProgram)++A161Fold.wUnbuild L)=
   (A161NarrowAcc.build8 acc (accZ L) bank L.core.cin src++middleProgram++A161SourceAdd.unbuild acc (accZ L) bank L.core.cin src) :=
   by
    dsimp only [acc,bank,src]
    rw [A161Low4Structural.build_eq,A161Low4Structural.unbuild_eq]
    all_goals rfl
  exact combine.trans (congrArg (fun P : Program => run P m s) assoc.symm)


#print axioms eq_plain
end ECDSAAdd.Entrant.A161Low4GenericFold
end

-- Low4 component FixedData
section
namespace ECDSAAdd.Entrant.A161Low4FixedFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
abbrev L:=A161FixedFold.L
abbrev g:=A161FixedFold.g
abbrev d:=A161FixedFold.d
abbrev q:=L.core.sumCarry
abbrev r:=eV L
abbrev p:=spare L
abbrev hs99:=A161Low4Facts.hs99
abbrev hs100:=hs99++[d]

theorem hw:L.Widths:=A161FixedFold.hw
theorem hn:L.wires.Nodup:=A161FixedFold.hn

def checked : ZeroSetDevelop.CheckedS hs99 A161Low4Facts.pLow :=
 (ZeroSetDevelop.compileS? hs99 A161Low4Facts.pLow).get A161Low4Facts.compiled99
attribute [local irreducible] checked

theorem cert99 : ZeroSetDevelop.SRewrites hs99 (A161Low4Fold.aMiddle L g) checked.out := by
 have h:=Eq.mp (congrArg (fun P:Program=>ZeroSetDevelop.SRewrites hs99 P checked.out) A161Low4Facts.input_eq) checked.proof
 simpa only [A161Low4Facts.middleLow,A161Low4Facts.acc161,A161Facts.acc161,
  A161Low4Fold.aMiddle,A161Low4Fold.accReg,A161Fold.accReg,A161Low4Fold.cFlipK] using h

theorem ready : A161Low4GenericFold.Ready L g hs100 := by
 rcases A161Low4Geometry.geometry with ⟨hg,hl,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,fmid,hwork⟩
 refine ⟨hg,hl,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,?_⟩
 intro u hu
 apply fmid u
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hu ⊢
 tauto

theorem cert100 : ZeroSetDevelop.SRewrites hs100 (A161Low4Fold.aMiddle L g) checked.out := by
 rcases A161Low4Geometry.geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,fmid,_⟩
 have free:=fmid d (by simp)
 exact A161Extend.SRewrites_extend hs99 d _ checked.out cert99
  (A161Low4GenericFold.free_middle L g d free.1 free.2.1)

def fold100 : Program:=A161Low4GenericFold.loop L hs100 checked.out

theorem hostClean (base:BasisState) (hc:L.PairClean base) (hd:base d=false) :
 ∀u∈hs100,u∉L.core.out ∧ base u=false := by
 rcases A161Low4Geometry.geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,fmid,hwork⟩
 intro u hu
 rcases List.mem_append.mp hu with hu|hu
 · have hw:u∈L.core.work:=hwork u hu
   exact ⟨(L.pairAuxAway hn u (by simp [hw])).2,(regValue_zero _ _).mp hc.work u hw⟩
 · have e:u=d:=by simpa only [List.mem_singleton] using hu
   subst u
   exact ⟨(fmid d (by simp)).2.2,hd⟩

theorem frame (base:BasisState) (hc:L.PairClean base) (hsum:base q=false)
 (hV:base r=false) (hP:base p=false) (hd:base d=false) (O:Nat) (hO:O<SquareReduction.p) :
 Triple (SquareFrame L.core.out base O) fold100
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
     (SquareReduction.p-1-O))%SquareReduction.p)) := by
 intro s m hf
 have hz:∀u∈hs100,s.basis u=false:=fun u hu=>(hf.2 u (hostClean base hc hd u hu).1).trans (hostClean base hc hd u hu).2
 have eq:run fold100 m s=run ((A161Fold.wBuild L++A161Low4Fold.aMiddle L g)++A161Fold.wUnbuild L) m s :=A161Low4GenericFold.eq_plain L hw hn g hs100 checked.out ready cert100 base hc hsum hV hP O hO s m hf hz
 rw [eq]
 exact A161Low4Fold.plain_frame L hw hn g ready.1 base hc O hO s m hf
#print axioms cert100
#print axioms frame
end ECDSAAdd.Entrant.A161Low4FixedFold
end

-- Low4 component LoopResources
section
namespace ECDSAAdd.Entrant.A161Low4GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run

theorem physical (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (ready:Ready L g hs)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle) :
 GatePhysical (loop L hs newMiddle) := by
  rw [loop_eq_ghost]
  let acc := A161Low4Ghost.ghostAcc L
  let pad := FullPadDevelop.pad L
  let bank := accBank L
  let src := hiReg L
  let q := L.core.sumCarry
  let r := eV L
  let p := spare L
  let middleProgram := A161Low4Fold.aMiddle L g
  have smallFit := smallFit L hw hn
  rcases ready with ⟨hg,hlen,hnd,hfresh,hne,fq,fr,fp,rq,pq,pr,fmid⟩
  have lens := A161Fold.acc_lengths L hw
  have haLen:acc.length=161:=A161Low4Ghost.ghostAcc_length L hw
  have hsrc := hiReg_length L hw
  have offq := A161Carry.wloop_original_off acc pad bank L.core.cin src q haLen hsrc smallFit fq
  have offr := A161Carry.wloop_original_off acc pad bank L.core.cin src r haLen hsrc smallFit fr
  have offp := A161Carry.wloop_original_off acc pad bank L.core.cin src p haLen hsrc smallFit fp
  have plen := FullPadDevelop.pad_length L hw
  have blen := lens.2.2.1
  have bd := A161Carry.buildDual_support acc pad bank L.core.cin src q r haLen hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have ud := A161Carry.unbuildDual_support acc pad bank L.core.cin src q r haLen hsrc (by change 132≤(accBank L).length; omega)
  have b0 := A161Carry.buildCached_support acc pad bank L.core.cin src q haLen hsrc (by change 5≤(FullPadDevelop.pad L).length; omega) (by change 132≤(accBank L).length; omega)
  have u0 := A161Carry.unbuildConsumed_support acc pad bank L.core.cin src q haLen hsrc (by change 132≤(accBank L).length; omega)
  have offpd : p∉wires (A161Carry.buildDual acc pad bank L.core.cin src q r) ∧
   p∉wires (A161Carry.unbuildDual acc pad bank L.core.cin src q r) := by
   constructor
   · intro h
     exact (Finset.mem_insert.mp (bd h)).elim pr (fun h => (Finset.mem_insert.mp (b0 h)).elim pq offp.1)
   · intro h
     exact (Finset.mem_insert.mp (ud h)).elim pr (fun h => (Finset.mem_insert.mp (u0 h)).elim pq offp.2)
  have pp := A161Carry.physical acc pad bank L.core.cin src q r p haLen hsrc smallFit rq
   offq.1 offq.2 offr.1 offr.2 offpd.1 offpd.2
  have coreNd : L.measuredCore.wires.Nodup :=
   (List.nodup_cons.mp (by simpa using L.measuredFold_interfaces hn [] (by simp))).2
  have mc := maskedConstant_physical g (A161Fold.accReg L) A161Low4Facts.Klow (fun h => hg (A161Fold.accReg_in L g h))
  have mid : GatePhysical middleProgram := by
   simp only [middleProgram,A161Low4Fold.aMiddle,gatePhysical_append]
   exact ⟨mc,QCore.qprog_physicalTq L.measuredCore SquareReduction.p coreNd,mc⟩
  have fresh : ∀u∈hs,u∉bank := by
   intro u hu hb
   exact hfresh u hu (by simp [domain,bank,hb])
  have physical : GatePhysical (A161Carry.buildTriple acc pad bank L.core.cin src q r p++middleProgram++A161Carry.unbuildTriple acc pad bank L.core.cin src q r p) := by
   simp only [gatePhysical_append]
   exact ⟨⟨pp.1,mid⟩,pp.2⟩
  exact A161Carry.compiled_physical_set 100 acc pad bank L.core.cin src hs q r p middleProgram newMiddle
   haLen hsrc (by change 5≤(FullPadDevelop.pad L).length; omega)
   (by change 132≤(accBank L).length; omega) (by decide) fresh cert physical

def ambient (L : CuccaroStreamedSquareWideLayout) (g : Wire) (hs : List Wire) : List Wire :=
 g::spare L::eV L::L.core.sumCarry::(A161GenericFold.domain L++L.measuredCore.wires++hs)

theorem support (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle) :
 wires (loop L hs newMiddle)⊆(ambient L g hs).toFinset := by
 let acc := A161Fold.accReg L
 let pad := FullPadDevelop.pad L
 let bank := accBank L
 let src := hiReg L
 have lens := A161Fold.acc_lengths L hw
 have hsrc := hiReg_length L hw
 have plen := FullPadDevelop.pad_length L hw
 have hfit := A161GenericFold.smallFit L hw hn
 have tri := A161Carry.support acc pad bank L.core.cin src L.core.sumCarry (eV L) (spare L) lens.1 hsrc hfit
 have cmp := A161Carry.compiled_support_set 100 acc pad bank L.core.cin src hs L.core.sumCarry (eV L) (spare L)
  (A161Low4Fold.aMiddle L g) newMiddle lens.1 hsrc (by change 5≤(FullPadDevelop.pad L).length; omega)
  (by change 132≤(accBank L).length; omega) (by decide) cert
 have sub (u:Wire) (h:u∈(spare L::eV L::L.core.sumCarry::L.core.cin::(src++acc++pad++bank)).toFinset) :
  u∈(ambient L g hs).toFinset := by
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  simp only [ambient,A161GenericFold.domain,List.mem_toFinset,List.mem_cons,List.mem_append]
  tauto
 intro u hu
 rcases Finset.mem_union.mp (cmp hu) with h|h
 · simp only [wires_append,Finset.mem_union] at h
   rcases h with (h|h)|h
   · exact sub u (tri.1 h)
   · simp only [A161Low4Fold.aMiddle,wires_append,Finset.mem_union] at h
     rcases h with h|(h|h)
     · have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
       simp only [List.mem_cons] at h
       simp only [ambient,A161GenericFold.domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       tauto
     · have h := List.mem_toFinset.mp (QCore.qprog_supportTq L.measuredCore SquareReduction.p h)
       simp only [ambient,A161GenericFold.domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       tauto
     · have h := List.mem_toFinset.mp (maskedConstant_wires_subset _ _ _ h)
       simp only [List.mem_cons] at h
       simp only [ambient,A161GenericFold.domain,List.mem_toFinset,List.mem_cons,List.mem_append]
       tauto
   · exact sub u (tri.2 h)
 · have h := List.mem_toFinset.mp h
   simp only [ambient,List.mem_toFinset,List.mem_cons,List.mem_append]
   tauto

#print axioms physical
#print axioms support
end ECDSAAdd.Entrant.A161Low4GenericFold
end

-- Low4 component Counts
section
namespace ECDSAAdd.Entrant.A161Low4GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount

theorem counts (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (hl:hs.length=100)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle) :
 toffoliCount (loop L hs newMiddle)≤1283 ∧ measurementCount (loop L hs newMiddle)=1543 := by
 let acc := A161Fold.accReg L
 let pad := FullPadDevelop.pad L
 let bank := accBank L
 let src := hiReg L
 let q := L.core.sumCarry
 let r := eV L
 let p := spare L
 have ha := (A161Fold.acc_lengths L hw).1
 have hb := (A161Fold.acc_lengths L hw).2.2.1
 have hsrc : src.length=128 := hiReg_length L hw
 have hz := FullPadDevelop.pad_length L hw
 have zp : 5≤pad.length := by change 5≤(FullPadDevelop.pad L).length; omega
 have bp : 132≤bank.length := by change 132≤(accBank L).length; omega
 have fit := A161GenericFold.smallFit L hw hn
 have b := A161KnownTail.build8_counts acc pad bank L.core.cin src ha (by omega) (fun f h => (fit f h).toFitsLen)
 rw [A161KnownTail.build8_eq] at b
 have u := A161SourceAdd.unbuild_resources acc pad bank L.core.cin src ha hsrc (fun f h => (fit f h).toFitsLen)
 have bc := A161Carry.buildCached_counts acc pad bank L.core.cin src q ha hsrc zp bp
 have uc := A161Carry.unbuildConsumed_counts acc pad bank L.core.cin src q ha hsrc bp
 have bd := A161Carry.buildDual_counts acc pad bank L.core.cin src q r ha hsrc zp bp
 have ud := A161Carry.unbuildDual_counts acc pad bank L.core.cin src q r ha hsrc bp
 have bt := A161Carry.buildTriple_counts acc pad bank L.core.cin src q r p ha hsrc zp bp
 have ut := A161Carry.unbuildTriple_counts acc pad bank L.core.cin src q r p ha hsrc bp
 have mid := QCore.qprog_countsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw) (by decide)
 have mask := maskedConstant_counts g (A161Fold.accReg L) A161Low4Facts.Klow
 have cm := A161Carry.compiled_counts_set 100 acc pad bank L.core.cin src hs q r p
  (A161Low4Fold.aMiddle L g) newMiddle ha hsrc zp bp (by decide) hl cert
 simp only [A161Low4Fold.aMiddle,toffoliCount_append,measurementCount_append,mask.1,mask.2,mid.1,mid.2] at cm
 simp only [loop,toffoliCount_append,measurementCount_append]
 dsimp only [acc,pad,bank,src,q,r,p] at *
 constructor <;> omega
#print axioms counts
end ECDSAAdd.Entrant.A161Low4GenericFold

namespace ECDSAAdd.Entrant.A161Low4GenericFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] Challenge.gateSlots ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
theorem slots (L : CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (g:Wire) (hs:List Wire) (newMiddle:Program) (hl:hs.length=100)
 (cert:ZeroSetDevelop.SRewrites hs (A161Low4Fold.aMiddle L g) newMiddle) :
 Challenge.gateSlots (loop L hs newMiddle)≤40000 := by
 let acc := A161Fold.accReg L
 let pad := FullPadDevelop.pad L
 let bank := accBank L
 let src := hiReg L
 let q := L.core.sumCarry
 let r := eV L
 let p := spare L
 have ha := (A161Fold.acc_lengths L hw).1
 have hb := (A161Fold.acc_lengths L hw).2.2.1
 have hsrc : src.length=128 := hiReg_length L hw
 have hz := FullPadDevelop.pad_length L hw
 have zp : 5≤pad.length := by change 5≤(FullPadDevelop.pad L).length; omega
 have bp : 132≤bank.length := by change 132≤(accBank L).length; omega
 have fit := A161GenericFold.smallFit L hw hn
 have b := A161KnownTail.build8_gateSlots acc pad bank L.core.cin src ha (by omega) (fun f h => (fit f h).toFitsLen)
 rw [A161KnownTail.build8_eq] at b
 have u := A161SourceAdd.unbuild_resources acc pad bank L.core.cin src ha hsrc (fun f h => (fit f h).toFitsLen)
 have bc := A161Carry.buildCached_counts acc pad bank L.core.cin src q ha hsrc zp bp
 have uc := A161Carry.unbuildConsumed_counts acc pad bank L.core.cin src q ha hsrc bp
 have bd := A161Carry.buildDual_counts acc pad bank L.core.cin src q r ha hsrc zp bp
 have ud := A161Carry.unbuildDual_counts acc pad bank L.core.cin src q r ha hsrc bp
 have bt := A161Carry.buildTriple_counts acc pad bank L.core.cin src q r p ha hsrc zp bp
 have ut := A161Carry.unbuildTriple_counts acc pad bank L.core.cin src q r p ha hsrc bp
 have mid := QCore.qprog_gateSlotsTq L.measuredCore 256 SquareReduction.p (L.measuredCore_widths hw)
 have mask := Baselines.maskedConstant_gateSlots_le g (A161Fold.accReg L) A161Low4Facts.Klow
 have cm := A161Carry.compiled_counts_set 100 acc pad bank L.core.cin src hs q r p
  (A161Low4Fold.aMiddle L g) newMiddle ha hsrc zp bp (by decide) hl cert
 simp only [A161Low4Fold.aMiddle,A161Low4Fold.accReg,A161Low4Fold.cFlipK,Challenge.gateSlots_append] at cm
 simp only [loop,Challenge.gateSlots_append]
 dsimp only [acc,pad,bank,src,q,r,p] at *
 omega

#print axioms slots
end ECDSAAdd.Entrant.A161Low4GenericFold
end

-- Low4 component Offsets
section
namespace ECDSAAdd.Entrant.A161Low4Offsets
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false

def delta : Nat := 3*2^161+15

theorem flip_decomposition : OwnDiagAll12Square.cFlipK=A161Low4Facts.Klow+delta := by
 norm_num [OwnDiagAll12Square.cFlipK,A161Low4Facts.Klow,delta]

-- The A body is reflected: reducing its complement decreases the reflected output,
-- and therefore increases the unreflected square offset.
def squareK : Nat := ControlLoan1589BFFold.K+delta

theorem squareK_lt : squareK<SquareReduction.p := by
 norm_num [squareK,delta,ControlLoan1589BFFold.K,SquareReduction.p,SquareReduction.B,SquareReduction.c]

theorem squareK_cast : (squareK : ZMod SquareReduction.p)=
 (ControlLoan1589BFFold.K : ZMod SquareReduction.p)+(delta : ZMod SquareReduction.p) := by
 rw [squareK,Nat.cast_add]

def resAFlow (P O : Nat) (g : Bool) : Nat :=
 ofCast true (measuredOrientationCast false O+((P : ZMod SquareReduction.p)*2^128-P-
   (if g then (A161Low4Facts.Klow : ZMod SquareReduction.p) else 0)))

theorem resAF_delta (P O : Nat) (g : Bool) : (resAFlow P O g : ZMod SquareReduction.p)=
 (resAF P O g : ZMod SquareReduction.p)-(if g then (delta : ZMod SquareReduction.p) else 0) := by
 haveI : NeZero SquareReduction.p := ⟨by norm_num [SquareReduction.p,SquareReduction.B,SquareReduction.c]⟩
 simp only [resAFlow,resAF,ofCast,if_true,ZMod.natCast_zmod_val]
 cases g
 · simp
 · simp only [if_true]
   rw [flip_decomposition,Nat.cast_add]
   ring

theorem absorb {F : Type*} [CommRing F] (X S K c d : F) (g : Bool) :
 (X-(if g then S else 0)+(if g then K+d else 0))+(if g then c-d else 0)=
 (X-(if g then S else 0)+(if g then K else 0))+(if g then c else 0) := by
 cases g <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring

#print axioms resAF_delta
#print axioms squareK_cast
#print axioms absorb
end ECDSAAdd.Entrant.A161Low4Offsets
end

-- Low4 component Body
section
namespace ECDSAAdd.Entrant.A161Low4Body
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem body_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hzero:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) (fold : Program)
    (foldFrame : ∀ O, O<SquareReduction.p →
      Triple (SquareFrame L.core.out base O) fold
       (SquareFrame L.core.out base
        (((if base c then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base else 4294968272*regValue (hiReg L) base)+
         (SquareReduction.p-1-O))%SquareReduction.p))) :
    Triple (SquareFrame L.core.out base O) (measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)) (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base c))) := by
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
#print axioms body_frame
end ECDSAAdd.Entrant.A161Low4Body
end

-- Low4 component FixedBody
section
namespace ECDSAAdd.Entrant.A161Low4FixedFold
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
 ThirdSavedCarryDevelop InverseCarryDevelop ZeroReadDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires checked List.toFinset

def body : Program := measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold100)

theorem ambient_sites : (A161Low4GenericFold.ambient L g hs100).toFinset⊆(d::g::L.wires).toFinset := by
 rcases A161Low4Geometry.geometry with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hwork⟩
 exact A161GenericFold.ambient_sites_general L hw g d hs100 (A161GenericFold.append_hosts L hs99 d hwork)

theorem ambient_eU : eU L∉(A161Low4GenericFold.ambient L g hs100).toFinset := by
 simpa only [List.mem_toFinset] using (show eU L∉A161Low4GenericFold.ambient L g hs100 from by decide)

theorem fold_support : wires fold100⊆(d::g::L.wires).toFinset :=
 (A161Low4GenericFold.support L hw hn g hs100 checked.out cert100).trans ambient_sites

theorem fold_physical : GatePhysical fold100 :=
 A161Low4GenericFold.physical L hw hn g hs100 checked.out ready cert100

theorem body_frame (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base g=false → M=0) (hd:base d=false) :
 Triple (SquareFrame L.core.out base O) body
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base g))) := by
 have hb:M^2<2^256:=by simpa using square_bound M 128 hM
 have vZero:base (eV L)=false:=eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
 have pZero:base (spare L)=false:=spare_zero L hw base M hP
 have ff : ∀ O, O<SquareReduction.p →
  Triple (SquareFrame L.core.out base O) fold100
   (SquareFrame L.core.out base (((if base g then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base
    else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) :=
  fun O hO=>frame base hc hzero vZero pZero hd O hO
 exact A161Low4Body.body_frame L hw hn g ready.1 base M hM hP hc hzero O hO hg fold100 ff

theorem body_support : wires body⊆(d::g::L.wires).toFinset := by
 have p1 := measuredFoldQ_supportTq L g (negP L) (by
  intro u hu
  exact List.mem_of_mem_take hu)
 have p2 := measuredFoldQ_supportTq L g (rot128F L) (by
  intro u hu
  rcases List.mem_append.mp hu with hu|hu
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hu)
  · exact List.mem_of_mem_take hu)
 intro u hu
 simp only [body,wires_append,Finset.mem_union] at hu
 rcases hu with hu|(hu|hu)
 · exact List.mem_toFinset.mpr (List.mem_cons_of_mem d (List.mem_toFinset.mp (p1 hu)))
 · exact List.mem_toFinset.mpr (List.mem_cons_of_mem d (List.mem_toFinset.mp (p2 hu)))
 · exact fold_support hu

theorem body_eU_free : eU L∉wires body := by
 have old : eU L∉wires (aBodyTriple L g) := fun h=>
  InverseCarryDevelop.eU_off_aBodyDual L hw hn g ready.1 (aBodyTriple_subset L hw g h)
 simp only [aBodyTriple,wires_append,Finset.mem_union,not_or] at old
 simp only [body,wires_append,Finset.mem_union,not_or]
 refine ⟨old.1,old.2.1,?_⟩
 exact fun h => ambient_eU (A161Low4GenericFold.support L hw hn g hs100 checked.out cert100 h)

#print axioms body_frame
#print axioms fold_physical
#print axioms body_support
#print axioms body_eU_free
end ECDSAAdd.Entrant.A161Low4FixedFold
end
