import ECDSAAdd.Submission.Entrant.KnownZeroArithmetic

-- Verified component RelocatedKnownA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.GhostRelocatedKnown
open Arithmetic InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ECDSAAdd.toffoliCount ECDSAAdd.measurementCount RelocateThreeGhosts.program RelocateThreeGhosts.first RelocateThreeGhosts.second ClearCopyBorrow.program ClearXorBorrow.program
namespace A
abbrev acc:List Wire:=ReorderedAFixed.acc
abbrev src:List Wire:=ReorderedAFixed.src
abbrev L:Arithmetic.CuccaroStreamedSquareWideLayout:=ReorderedAFixed.L
abbrev original:Program:=KnownAMidStaged.body
def program:Program:=RelocateThreeGhosts.program ports original

theorem maps:acc.getD 0 0=4757 ∧ acc.getD 1 0=4758 ∧ acc.getD 2 0=4759 ∧
 src.getD 0 0=4243 ∧ src.getD 1 0=4244 ∧ src.getD 2 0=4245 ∧
 acc.getD 4 0=4505 ∧ acc.getD 5 0=4506 ∧ acc.getD 6 0=4507:=by decide +kernel

theorem source_free(u:Wire)(hu:u∈([4243,4244,4245]:List Wire)):u∉wires original:=by
 intro bad
 have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownAMidStaged.cert
 have old:=Skip4.wires_mono_of_mem original _ (fun _ h=>sub.subset h) bad
 have off:u∉wires A161Low4FixedFold.checked.out:=by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl|rfl|rfl
  all_goals exact GhostMiddleSupport.a_free _ (by decide +kernel) (by decide +kernel)
 exact off old

theorem equivalent(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc ReorderedAFixed.pad ReorderedAFixed.bank L.core.cin src H s)
 (after:WReady acc ReorderedAFixed.pad ReorderedAFixed.bank L.core.cin src H (run original m s)):
 run program m s=run original m s:=by
 rcases maps with ⟨q0,q1,q2,a0,a1,a2,b0,b1,b2⟩
 have val:regValue acc s.basis=4294968272*regValue src s.basis:=by rw [before.2.1];exact before.1
 have copies:=LowWordRecovery.copies acc src s.basis
  (by have h:=ReorderedAFixed.lengths.1;change acc.length=_ at h;omega)
  (by have h:=ReorderedAFixed.lengths.2.2.2;change src.length=_ at h;omega) val
 simp only [a0,a1,a2,b0,b1,b2] at copies
 have zi(i:Nat)(hi:i<3):s.basis (acc.getD i 0)=false:=
  LowWordRecovery.low_register_zero acc s.basis H i (by omega)
   (by have h:=ReorderedAFixed.lengths.1;change acc.length=_ at h;omega) before.1
 have zo(i:Nat)(hi:i<3):(run original m s).basis (acc.getD i 0)=false:=
  LowWordRecovery.low_register_zero acc (run original m s).basis H i (by omega)
   (by have h:=ReorderedAFixed.lengths.1;change acc.length=_ at h;omega) after.1
 have stable:∀u∈acc,(run original m s).basis u=s.basis u:=
  (regValue_eq_iff acc _ _).mp (after.1.trans before.1.symm)
 apply RelocateThreeGhosts.equivalent ports ports_inj original s m
 · exact source_free _ (by decide)
 · exact source_free _ (by decide)
 · exact source_free _ (by decide)
 · simpa only [q0] using zi 0 (by decide)
 · simpa only [q1] using zi 1 (by decide)
 · simpa only [q2] using zi 2 (by decide)
 · exact copies.1
 · exact copies.2.1
 · exact copies.2.2
 · simpa only [q0] using zo 0 (by decide)
 · simpa only [q1] using zo 1 (by decide)
 · simpa only [q2] using zo 2 (by decide)
 · exact stable _ (by decide +kernel)
 · exact stable _ (by decide +kernel)
 · exact stable _ (by decide +kernel)
#print axioms equivalent
end A
end ECDSAAdd.Entrant.GhostRelocatedKnown

namespace ECDSAAdd.Entrant.GhostRelocatedKnown
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount RelocateThreeGhosts.program
namespace A
theorem counts:toffoliCount program=toffoliCount original ∧ measurementCount program=measurementCount original:=RelocateThreeGhosts.counts ports original

theorem ghosts_free:4757∉wires program ∧ 4758∉wires program ∧ 4759∉wires program:=by
 exact RelocateThreeGhosts.ghosts_free ports ports_inj original
  (source_free _ (by decide)) (source_free _ (by decide)) (source_free _ (by decide))

#print axioms ghosts_free
end A
end ECDSAAdd.Entrant.GhostRelocatedKnown

end

-- Verified component Ghost3CacheASetup
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
def spares:List Wire:=[4757,4758,4759]
def phantoms:List Wire:=[100000,100001,100002]
def viewPerm:Wire→Wire:=fun q=>Equiv.swap 4757 100000 (Equiv.swap 4758 100001 (Equiv.swap 4759 100002 q))
def viewAcc:List Wire:=acc.map viewPerm
def hosts : List Wire := ReorderedAFixed.hosts++spares

theorem geometry : hosts.Nodup ∧ hosts.length=106 ∧ viewAcc.length=161 ∧
 (∀h∈hosts,h∉L.core.cin::(src++viewAcc++pad++bank)):=by decide +kernel

theorem fitsView(f:MeasuredSquareFold)(hm:f∈earlyHTerms src):
 Acc.Fits viewAcc pad bank L.core.cin 161 f:=by
 have old:=ReorderedAFixed.fits f hm
 have hsrc:f.src=src:=by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl <;>rfl
 refine {toFitsLen:=old.toFitsLen,nd:=?_}
 rw [hsrc]
 decide +kernel

theorem drop4:viewAcc.drop 4=acc.drop 4:=by decide +kernel
theorem drop6:(viewAcc.take 138).drop 6=(acc.take 138).drop 6:=by decide +kernel
theorem drop10:(viewAcc.take 138).drop 10=(acc.take 138).drop 10:=by decide +kernel
theorem drop32:(viewAcc.take 161).drop 32=(acc.take 161).drop 32:=by decide +kernel
theorem plainBuild_eq:
 ReorderedAPlain.build viewAcc pad bank L.core.cin src=ReorderedAPlain.build acc pad bank L.core.cin src:=by
 simp only [ReorderedAPlain.build,ReorderedAPre.pre,A161Carry.buildPost,Acc.seedOp,Acc.op,Acc.ty,Acc.earlyTerm,drop4,drop6,drop10,drop32]
theorem plainUnbuild_eq:
 ReorderedAPlain.unbuild viewAcc pad bank L.core.cin src=ReorderedAPlain.unbuild acc pad bank L.core.cin src:=by
 simp only [ReorderedAPlain.unbuild,A161Carry.unbuildPre,CodexKnownOnesTail.accSub,ReorderedATail.tail,Acc.seedOp,Acc.op,Acc.ty,Acc.earlyTerm,drop4,drop6,drop10,drop32]
#print axioms geometry
end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAState
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

def erase(s:State):State:=EraseListProof.erase phantoms s

theorem phantom_off(q:Wire)(hq:q∈phantoms):q∉L.core.cin::(src++acc++pad++bank):=by
 simp only [phantoms,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel

theorem spare_mem(q:Wire)(hq:q∈spares):q∈acc:=by
 simp only [spares,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel

theorem bit_same(s:State)(q:Wire)(h:q∉phantoms):(erase s).basis q=s.basis q:=by
 exact (EraseListProof.basis phantoms s q).trans (if_neg h)

theorem reg_map(xs:List Wire)(f:Wire→Wire)(s t:BasisState)
 (h:∀q∈xs,s (f q)=t q):regValue (xs.map f) s=regValue xs t:=by
 induction xs with
 | nil=>rfl
 | cons a as ih=>
  have ha:=h a (by simp)
  have hr:=ih (fun q hq=>h q (by simp [hq]))
  simp only [regValue,List.map_cons,List.foldr_cons] at hr ⊢
  rw [ha,hr]

theorem reg_view(s:State)(hz:∀q∈spares,s.basis q=false):regValue viewAcc (erase s).basis=regValue acc s.basis:=by
 apply reg_map
 intro q hq
 have off:q∉phantoms:=by intro h;exact phantom_off q h (by simp [hq])
 by_cases h0:q=4757
 · subst q
   simp [viewPerm,Equiv.swap_apply_def,erase,EraseListProof.basis,phantoms,hz 4757 (by decide)]
 by_cases h1:q=4758
 · subst q
   simp [viewPerm,Equiv.swap_apply_def,erase,EraseListProof.basis,phantoms,hz 4758 (by decide)]
 by_cases h2:q=4759
 · subst q
   simp [viewPerm,Equiv.swap_apply_def,erase,EraseListProof.basis,phantoms,hz 4759 (by decide)]
 have p0:q≠100000:=by intro e;apply off;subst q;decide
 have p1:q≠100001:=by intro e;apply off;subst q;decide
 have p2:q≠100002:=by intro e;apply off;subst q;decide
 have fix:viewPerm q=q:=by simp [viewPerm,Equiv.swap_apply_def,h0,h1,h2,p0,p1,p2]
 rw [fix]
 exact bit_same s q off

theorem reg_same(xs:List Wire)(s:State)(off:∀q∈phantoms,q∉xs):
 regValue xs (erase s).basis=regValue xs s.basis:=by
 apply regValue_congr
 intro q hq
 exact bit_same s q (fun h=>off q h hq)

theorem ready_view(H:Nat)(s:State)(hz:∀q∈spares,s.basis q=false)(h:WReady acc pad bank L.core.cin src H s):
 WReady viewAcc pad bank L.core.cin src H (erase s):=by
 refine ⟨(reg_view s hz).trans h.1,?_,?_,?_,?_⟩
 · exact (reg_same src s (fun q hq bad=>phantom_off q hq (by simp [bad]))).trans h.2.1
 · intro q hq
   exact (bit_same s q (fun bad=>phantom_off q bad (by simp [hq]))).trans (h.2.2.1 q hq)
 · intro q hq
   exact (bit_same s q (fun bad=>phantom_off q bad (by simp [hq]))).trans (h.2.2.2.1 q hq)
 · exact (bit_same s L.core.cin (fun bad=>phantom_off _ bad (by simp))).trans h.2.2.2.2

theorem run_erase(P:Program)(m:List Bool)(s:State)(off:∀q∈phantoms,q∉wires P):
 run P m (erase s)=erase (run P m s):=EraseListProof.commute phantoms P m s off

theorem erase_eq_implies(s t:State)(hv:∀q∈phantoms,s.basis q=t.basis q)(he:erase s=erase t):s=t:=
 EraseListProof.cancel phantoms s t hv he
#print axioms ready_view
end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAPlainSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset

theorem plain_support(A:List Wire)(len:A.length=161)
 (fit:∀f∈earlyHTerms src,Acc.Fits A pad bank L.core.cin 161 f):
 wires (ReorderedAPlain.build A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset ∧
 wires (ReorderedAPlain.unbuild A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=by
 have seed:=Acc.seed_support A pad bank L.core.cin 161 (Acc.earlyTerm src false 4) len
  (fit _ (A161NarrowAcc.terms_mem src).1)
 have op6:=Acc.op_prefix_support A pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  len (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) true
 have op10(neg:Bool):wires (Acc.op (A.take 138) pad bank L.core.cin 138 neg (Acc.earlyTerm src false 10))⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=by
  have ff:=ReorderedAcc.fits_prefix A pad bank L.core.cin 161 138 (Acc.earlyTerm src false 10)
   (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.1) (by decide) (by decide)
  rw [ReorderedAcc.op_wires (A.take 138) pad bank L.core.cin 138 neg (Acc.earlyTerm src false 10) (by simp [len]) ff]
  intro q hq
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,if_true,List.mem_cons,List.mem_append] at h ⊢
  have pa:∀k,q∈pad.take k→q∈pad:=fun _=>List.mem_of_mem_take
  have aa:q∈(A.take 138).drop 10→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:∀k,q∈bank.take k→q∈bank:=fun _=>List.mem_of_mem_take
  tauto
 have top(neg:Bool):wires (Acc.op (A.take 161) pad bank L.core.cin 161 neg (Acc.earlyTerm src false 32))⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=
  Acc.op_prefix_support A pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
   len (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide) neg
 have f32:=Acc.fits_prefix A pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide)
 have preInv:wires (A161Carry.unbuildPre A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=
  (CodexNarrowTailResource.accSub_support 106 (A.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32)
   (by simp [len]) f32.toFitsLen (by decide)).trans (top true)
 have tail:=KnownOutputAdder.program_support (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
  ((A.take 138).drop 6) (bank.take 131) L.core.cin
 rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tail
 have td:((src++pad.take 4)++src.drop 2++(A.take 138).drop 6++bank.take 131++[L.core.cin]).toFinset⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=by
  intro q hq
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [List.mem_append,List.mem_singleton] at h
  have pp:q∈pad.take 4→q∈pad:=List.mem_of_mem_take
  have ss:q∈src.drop 2→q∈src:=List.mem_of_mem_drop
  have aa:q∈(A.take 138).drop 6→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:q∈bank.take 131→q∈bank:=List.mem_of_mem_take
  simp only [List.mem_cons,List.mem_append]
  tauto
 have tailSupport:wires (ReorderedATail.tail A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=tail.trans td
 constructor
 · simp only [ReorderedAPlain.build,ReorderedAPre.pre,A161Carry.buildPost,wires_append]
   exact Finset.union_subset (Finset.union_subset (Finset.union_subset seed op6) (op10 false)) (top false)
 · simp only [ReorderedAPlain.unbuild,wires_append]
   exact Finset.union_subset (Finset.union_subset (Finset.union_subset preInv (op10 true)) tailSupport) seed
#print axioms plain_support
end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheACachedSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset

theorem cached_support(A:List Wire)(len:A.length=161)
 (fit:∀f∈earlyHTerms src,Acc.Fits A pad bank L.core.cin 161 f):
 wires (ReorderedABuild.build 106 A pad bank L.core.cin src Ghost3CacheA.hosts)⊆
  (L.core.cin::(src++A++pad++bank)).toFinset∪Ghost3CacheA.hosts.toFinset ∧
 wires (ReorderedAUnbuild.unbuild 106 A pad bank L.core.cin src Ghost3CacheA.hosts)⊆
  (L.core.cin::(src++A++pad++bank)).toFinset∪Ghost3CacheA.hosts.toFinset:=by
 let D:Finset Wire:=(L.core.cin::(src++A++pad++bank)).toFinset∪Ghost3CacheA.hosts.toFinset
 have pf:wires (ReorderedAPlain.build A pad bank L.core.cin src)⊆D:=
  (plain_support A len fit).1.trans Finset.subset_union_left
 have pi:wires (ReorderedAPlain.unbuild A pad bank L.core.cin src)⊆D:=
  (plain_support A len fit).2.trans Finset.subset_union_left
 have cd:(L.core.cin::(src++(A.take 138).drop 10++bank.take 127)).toFinset∪Ghost3CacheA.hosts.toFinset⊆D:=by
  apply Finset.union_subset ?_ Finset.subset_union_right
  intro q hq
  apply Finset.mem_union_left
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [List.mem_cons,List.mem_append] at h ⊢
  have aa:q∈(A.take 138).drop 10→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:q∈bank.take 127→q∈bank:=List.mem_of_mem_take
  tauto
 have cc:=ReorderedSupport.cached 106 src ((A.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin
  (by decide) (by simp [len]) (by decide) (by simp [len];decide +kernel) (by simp [len];decide +kernel)
 have ci:=ReorderedSupport.consumed 106 src ((A.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin
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
#print axioms cached_support
end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAPrograms
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop FourthASavedCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def build:Program:=ReorderedABuild.build 106 acc pad bank L.core.cin src hosts
def unbuild:Program:=ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts
abbrev middle:Program:=GhostRelocatedKnown.A.program

theorem build_view:ReorderedABuild.build 106 viewAcc pad bank L.core.cin src hosts=build:=by
 simp only [build,ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,
  Acc.seedOp,Acc.op,Acc.ty,Acc.earlyTerm,drop4,drop6,drop10,drop32]
theorem unbuild_view:ReorderedAUnbuild.unbuild 106 viewAcc pad bank L.core.cin src hosts=unbuild:=by
 simp only [unbuild,ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,A161Carry.unbuildPre,
  ReorderedATail.tail,CodexKnownOnesTail.accSub,Acc.seedOp,Acc.op,Acc.ty,Acc.earlyTerm,drop4,drop6,drop10,drop32]

theorem not_wire(P:Program)(q:Wire)(h:hasWire P q=false):q∉wires P:=by
 intro bad
 have e:hasWire P q=true:=(hasWire_iff P q).mpr bad
 rw [h] at e
 cases e

theorem spare_off_build(q:Wire)(hq:q∈spares):q∉wires (ReorderedAPlain.build acc pad bank L.core.cin src):=by
 rw [←plainBuild_eq]
 intro bad
 have sub:=(plain_support viewAcc geometry.2.2.1 fitsView).1 bad
 exact geometry.2.2.2 q (by simp only [Ghost3CacheA.hosts,List.mem_append];exact Or.inr hq) (List.mem_toFinset.mp sub)
theorem spare_off_unbuild(q:Wire)(hq:q∈spares):q∉wires (ReorderedAPlain.unbuild acc pad bank L.core.cin src):=by
 rw [←plainUnbuild_eq]
 intro bad
 have sub:=(plain_support viewAcc geometry.2.2.1 fitsView).2 bad
 exact geometry.2.2.2 q (by simp only [Ghost3CacheA.hosts,List.mem_append];exact Or.inr hq) (List.mem_toFinset.mp sub)
theorem spare_off_middle(q:Wire)(hq:q∈spares):q∉wires middle:=by
 simp only [spares,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl
 · exact GhostRelocatedKnown.A.ghosts_free.1
 · exact GhostRelocatedKnown.A.ghosts_free.2.1
 · exact GhostRelocatedKnown.A.ghosts_free.2.2

theorem phantom_off_from_small(P:Program)(sm:SmallWireProof.small P=true)(q:Wire)(hq:q∈phantoms):q∉wires P:=by
 have lo:100000≤q:=by
  simp only [phantoms,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl <;>decide
 exact fun bad=>Nat.not_lt_of_ge lo (SmallWireProof.support P sm q bad)

theorem phantom_not_host:∀q∈phantoms,q∉Ghost3CacheA.hosts:=by decide +kernel

theorem phantom_off_build:∀q∈phantoms,q∉wires build:=by
 intro q hq bad
 have sub:=(cached_support acc lengths.1 fits).1 bad
 rcases Finset.mem_union.mp sub with dom|host
 · exact phantom_off q hq (List.mem_toFinset.mp dom)
 · exact phantom_not_host q hq (List.mem_toFinset.mp host)
theorem phantom_off_unbuild:∀q∈phantoms,q∉wires unbuild:=by
 intro q hq bad
 have sub:=(cached_support acc lengths.1 fits).2 bad
 rcases Finset.mem_union.mp sub with dom|host
 · exact phantom_off q hq (List.mem_toFinset.mp dom)
 · exact phantom_not_host q hq (List.mem_toFinset.mp host)
theorem phantom_off_plain_build:∀q∈phantoms,q∉wires (ReorderedAPlain.build acc pad bank L.core.cin src):=by
 intro q hq bad
 exact phantom_off q hq (List.mem_toFinset.mp ((plain_support acc lengths.1 fits).1 bad))
theorem phantom_off_plain_unbuild:∀q∈phantoms,q∉wires (ReorderedAPlain.unbuild acc pad bank L.core.cin src):=by
 intro q hq bad
 exact phantom_off q hq (List.mem_toFinset.mp ((plain_support acc lengths.1 fits).2 bad))
theorem phantom_off_middle(q:Wire)(hq:q∈phantoms):q∉wires middle:=by
 apply RelocateThreeGhosts.outside GhostRelocatedKnown.ports GhostRelocatedKnown.A.original q
 · intro i
   simp only [phantoms,List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl <;>fin_cases i <;>decide
 · intro bad
   have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownAMidStaged.cert
   have old:=Skip4.wires_mono_of_mem _ _ (fun _ h=>sub.subset h) bad
   have off:q∉wires A161Low4FixedFold.checked.out:=by
    simp only [phantoms,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    all_goals exact GhostMiddleSupport.a_free _ (by decide +kernel) (by decide +kernel)
   exact off old
#print axioms phantom_off_middle
end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheALoop
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ReorderedAPlain.build ReorderedAPlain.unbuild ReorderedABuild.build ReorderedAUnbuild.unbuild
 RelocateThreeGhosts.program

def loop:Program:=build++middle++unbuild

theorem host_off_plain(u:Wire)(hu:u∈Ghost3CacheA.hosts):
 u∉wires (ReorderedAPlain.build acc pad bank L.core.cin src) ∧
 u∉wires (ReorderedAPlain.unbuild acc pad bank L.core.cin src) ∧ u∉wires middle:=by
 simp only [Ghost3CacheA.hosts,List.mem_append] at hu
 rcases hu with old|extra
 · refine ⟨(ReorderedAFixed.off_plain u old).1,(ReorderedAFixed.off_plain u old).2,?_⟩
   apply RelocateThreeGhosts.outside GhostRelocatedKnown.ports GhostRelocatedKnown.A.original u
   · exact (by decide +kernel :∀u∈ReorderedAFixed.hosts,∀i:Fin 9,u≠GhostRelocatedKnown.ports i) u old
   · intro bad
     have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownAMidStaged.cert
     have h:=Skip4.wires_mono_of_mem _ _ (fun _ h=>sub.subset h) bad
     exact ReorderedAFixed.off_middle u old h
 · exact ⟨spare_off_build u extra,spare_off_unbuild u extra,spare_off_middle u extra⟩

theorem loop_eq(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)
 (ha:regValue acc s.basis=0)(zero:∀h∈Ghost3CacheA.hosts,s.basis h=false)
 (good:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) middle s m)):
 run loop m s=run (ReorderedAPlain.build acc pad bank L.core.cin src++middle++
  ReorderedAPlain.unbuild acc pad bank L.core.cin src) m s:=by
 have hv:∀q∈phantoms,q∉Ghost3CacheA.hosts:=by decide +kernel
 have hsrc:∀q∈phantoms,q∉src:=fun q hq bad=>phantom_off q hq (by simp [bad])
 have hpad:∀q∈phantoms,q∉pad:=fun q hq bad=>phantom_off q hq (by simp [bad])
 have hbank:∀q∈phantoms,q∉bank:=fun q hq bad=>phantom_off q hq (by simp [bad])
 have hcin:L.core.cin∉phantoms:=fun hq=>phantom_off _ hq (by simp)
 have hzE:∀q∈pad,(erase s).basis q=false:=by
  intro q hq
  exact (bit_same s q (fun bad=>hpad q bad hq)).trans (hz q hq)
 have hbE:∀q∈bank,(erase s).basis q=false:=by
  intro q hq
  exact (bit_same s q (fun bad=>hbank q bad hq)).trans (hb q hq)
 have hiE:(erase s).basis L.core.cin=false:=(bit_same s _ hcin).trans hi
 have zs:∀q∈spares,s.basis q=false:=fun q hq=>zero q (by simp only [Ghost3CacheA.hosts,List.mem_append];exact Or.inr hq)
 have haE:regValue viewAcc (erase s).basis=0:=(reg_view s zs).trans ha
 have zeroE:∀h∈Ghost3CacheA.hosts,(erase s).basis h=false:=by
  intro h hh
  exact (bit_same s h (fun bad=>hv h bad hh)).trans (zero h hh)
 let u:=middleState (ReorderedAPlain.build acc pad bank L.core.cin src) middle s m
 have uz:∀q∈spares,u.basis q=false:=by
  intro q hq
  unfold u middleState
  exact (run_preserves_outside _ _ _ q (spare_off_middle q hq)).trans
   ((run_preserves_outside _ _ _ q (spare_off_build q hq)).trans (zs q hq))
 have me:middleState (ReorderedAPlain.build viewAcc pad bank L.core.cin src) middle (erase s) m=erase u:=by
  rw [plainBuild_eq]
  unfold middleState u
  rw [run_erase _ _ _ phantom_off_plain_build,run_erase _ _ _ phantom_off_middle]
  rfl
 have sourceE:=reg_same src s hsrc
 have goodE:WReady viewAcc pad bank L.core.cin src (regValue src (erase s).basis)
  (middleState (ReorderedAPlain.build viewAcc pad bank L.core.cin src) middle (erase s) m):=by
  rw [sourceE,me]
  exact ready_view _ u uz good
 have offF:∀h∈Ghost3CacheA.hosts,h∉wires (ReorderedAPlain.build viewAcc pad bank L.core.cin src):=by
  rw [plainBuild_eq]
  exact fun h hh=>(host_off_plain h hh).1
 have offI:∀h∈Ghost3CacheA.hosts,h∉wires (ReorderedAPlain.unbuild viewAcc pad bank L.core.cin src):=by
  rw [plainUnbuild_eq]
  exact fun h hh=>(host_off_plain h hh).2.1
 have eq:=ReorderedALoop.loop_eq 106 viewAcc pad bank L.core.cin src Ghost3CacheA.hosts middle
  geometry.2.2.1 lengths.2.2.2 fitsView (erase s) m hzE hbE hiE haE (by decide)
  geometry.1 geometry.2.1 geometry.2.2.2 offF offI (fun h hh=>(host_off_plain h hh).2.2) zeroE goodE
 rw [build_view,unbuild_view,plainBuild_eq,plainUnbuild_eq] at eq
 have leftOff:∀q∈phantoms,q∉wires (build++middle++unbuild):=by
  intro q hq
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨⟨phantom_off_build q hq,phantom_off_middle q hq⟩,phantom_off_unbuild q hq⟩
 have rightOff:∀q∈phantoms,q∉wires (ReorderedAPlain.build acc pad bank L.core.cin src++middle++
  ReorderedAPlain.unbuild acc pad bank L.core.cin src):=by
  intro q hq
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨⟨phantom_off_plain_build q hq,phantom_off_middle q hq⟩,phantom_off_plain_unbuild q hq⟩
 rw [run_erase _ _ _ leftOff,run_erase _ _ _ rightOff] at eq
 apply erase_eq_implies
 · intro q hq
   exact (run_preserves_outside _ m s q (leftOff q hq)).trans
    (run_preserves_outside _ m s q (rightOff q hq)).symm
 · exact eq
#print axioms loop_eq
end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAMiddleFrames
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic ReorderedAFixed InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked

theorem plain_ready(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)(ha:regValue acc s.basis=0):
 WReady acc pad bank L.core.cin src (regValue src s.basis) (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s):=by
 have f:=ReorderedAPlain.build_triple acc pad bank L.core.cin src lengths.1 lengths.2.2.2 fits s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have away:∀q∈src++pad++bank++[L.core.cin],q∉acc:=by decide +kernel
 refine ⟨f.2.1,?_,?_,?_,?_⟩
 · exact regValue_congr _ _ _ (fun q hq=>f.2.2 q (away q (by simp [hq])))
 · intro q hq
   exact (f.2.2 q (away q (by simp [hq]))).trans (hz q hq)
 · intro q hq
   exact (f.2.2 q (away q (by simp [hq]))).trans (hb q hq)
 · exact (f.2.2 _ (away _ (by simp))).trans hi

theorem relocated_middle_counts:
 measurementCount GhostRelocatedKnown.A.program=measurementCount A161Low4FixedFold.checked.out:=
 GhostRelocatedKnown.A.counts.2.trans (KnownSparseFold.Cert.counts _ _ _ _ _ KnownAMidStaged.cert).2

theorem relocated_middle_eq(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc pad bank L.core.cin src H s)
 (after:WReady acc pad bank L.core.cin src H (run A161Low4FixedFold.checked.out m s)):
 run GhostRelocatedKnown.A.program m s=run A161Low4FixedFold.checked.out m s:=by
 have z:KnownSparseFold.Zero KnownAMidStaged.known0 s:=by
  intro u hu
  rcases ReorderedKnownA.guard u hu with ⟨_,_,hb⟩
  exact hb.elim (fun h=>before.2.2.2.1 u h) (fun h=>h.symm ▸ before.2.2.2.2)
 have km:run KnownAMidStaged.body m s=run A161Low4FixedFold.checked.out m s:=(KnownSparseFold.Cert.correct _ _ _ _ _ KnownAMidStaged.cert s m z).1
 have good:WReady acc pad bank L.core.cin src H (run KnownAMidStaged.body m s):=by rw [km];exact after
 exact (GhostRelocatedKnown.A.equivalent H s m before good).trans km

theorem relocated_middleState_eq(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)(ha:regValue acc s.basis=0)
 (after:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out s m)):
 middleState (ReorderedAPlain.build acc pad bank L.core.cin src) GhostRelocatedKnown.A.program s m=
 middleState (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out s m:=by
 unfold middleState
 rw [relocated_middle_counts]
 apply relocated_middle_eq (regValue src s.basis) _ _ ?_ after
 exact plain_ready s _ hz hb hi ha
#print axioms relocated_middleState_eq
end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3CacheAFrame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked
abbrev p:=ReorderedAFixed.p
theorem frame(base:BasisState)(hc:L.PairClean base)(hsum:base q=false)(hV:base r=false)(hP:base p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
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
 have qz:s.basis q=false:=(hf.2 q (by decide)).trans hsum
 have rz:s.basis r=false:=(hf.2 r (by decide)).trans hV
 have pz:s.basis p=false:=(hf.2 p (by decide)).trans hP
 have zeroU:∀u∈hs,s.basis u=false:=fun u hu=>
  (hf.2 u (A161Low4FixedFold.hostClean base hc hd u hu).1).trans (A161Low4FixedFold.hostClean base hc hd u hu).2
 have zeroOld:∀u∈ReorderedAFixed.hosts,s.basis u=false:=by
  change ∀u∈q::r::p::hs,s.basis u=false
  rw [List.forall_mem_cons,List.forall_mem_cons,List.forall_mem_cons]
  exact ⟨qz,rz,pz,zeroU⟩
 have zero:∀u∈Ghost3CacheA.hosts,s.basis u=false:=by
  intro u hu
  simp only [Ghost3CacheA.hosts,List.mem_append] at hu
  rcases hu with old|extra
  · exact zeroOld u old
  · exact (regValue_zero acc s.basis).mp ha u (spare_mem u extra)
 have offHs:∀u∈hs,u∉wires (ReorderedAPlain.build acc pad bank L.core.cin src):=by
  intro u hu
  exact (off_plain u (by change u∈q::r::p::hs;simp only [List.mem_cons];exact Or.inr (Or.inr (Or.inr hu)))).1
 have goodOriginal:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) (A161Low4Fold.aMiddle L g) s m):=by
  rw [ReorderedARetape.a_middle_eq acc pad bank L.core.cin src (A161Low4Fold.aMiddle L g)
   lengths.1 lengths.2.2.2 fits s m hz hb clean.cin ha]
  exact good_old base hc O hO s _ hf
 have middleEq:=A161Low4FixedFold.cert100.middle_eq hs (A161Low4Fold.aMiddle L g) A161Low4FixedFold.checked.out
  (ReorderedAPlain.build acc pad bank L.core.cin src) s m zeroU offHs
 have good:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out s m):=by
  rw [middleEq]
  exact goodOriginal
 have changed:=relocated_middleState_eq s m hz hb clean.cin ha good
 have goodNew:WReady acc pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedAPlain.build acc pad bank L.core.cin src) middle s m):=by
  rw [changed]
  exact good
 have cachedNew:=Ghost3CacheA.loop_eq s m hz hb clean.cin ha zero goodNew
 have midEq:run middle (m.drop (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s)=
  run A161Low4FixedFold.checked.out (m.drop (measurementCount (ReorderedAPlain.build acc pad bank L.core.cin src)))
  (run (ReorderedAPlain.build acc pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using changed
 have ctxt:=ReorderedKnownA.context_eq
  (ReorderedAPlain.build acc pad bank L.core.cin src) A161Low4FixedFold.checked.out middle
  (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m relocated_middle_counts midEq
 have cached:=cachedNew.trans ctxt
 have middleReplace:=A161Low4FixedFold.cert100.surround_eq hs (A161Low4Fold.aMiddle L g) A161Low4FixedFold.checked.out
  (ReorderedAPlain.build acc pad bank L.core.cin src) (ReorderedAPlain.unbuild acc pad bank L.core.cin src) s m zeroU offHs
 have eq:run loop m s=run (ReorderedAPlain.build acc pad bank L.core.cin src++A161Low4Fold.aMiddle L g++
  ReorderedAPlain.unbuild acc pad bank L.core.cin src) m s:=cached.trans middleReplace
 exact transport _ s _ _ eq (plain_frame base hc O hO s m hf)


#print axioms frame
end ECDSAAdd.Entrant.Ghost3CacheA

end

-- Verified component Ghost3KnownA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3KnownA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev p:=ReorderedAFixed.p
abbrev hosts:=Ghost3CacheA.hosts
abbrev loop:=Ghost3CacheA.loop
abbrev frame:=Ghost3CacheA.frame
def fold:Program:=loop

def rawBody:Program:=measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)
theorem raw_body_frame (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base g=false → M=0) (hd:base d=false) :
 Triple (SquareFrame L.core.out base O) rawBody
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base g))) := by
 have hb:M^2<2^256:=by simpa using square_bound M 128 hM
 have vZero:base (eV L)=false:=eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
 have pZero:base (spare L)=false:=spare_zero L hw base M hP
 have ff : ∀ O, O<SquareReduction.p →
  Triple (SquareFrame L.core.out base O) fold
   (SquareFrame L.core.out base (((if base g then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base
    else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) :=
  fun O hO=>frame base hc hzero vZero pZero hd O hO
 exact A161Low4Body.body_frame L hw hn g A161Low4FixedFold.ready.1 base M hM hP hc hzero O hO hg fold ff


def body:Program:=rawBody++ReorderedRecordPadding.program 4 L.core.cin

theorem body_frame (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base g=false → M=0) (hd:base d=false) :
 Triple (SquareFrame L.core.out base O) body
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base g))) := by
 intro s m hf
 have f:=raw_body_frame base M hM hP hc hzero O hO hg hd s (m.take (measurementCount rawBody)) hf
 have hz:(run rawBody (m.take (measurementCount rawBody)) s).basis L.core.cin=false:=
  (f.2.2 L.core.cin (by decide)).trans hc.cin
 have eq:run body m s=run rawBody (m.take (measurementCount rawBody)) s:=by
  rw [body,run_append,ReorderedRecordPadding.run_zero 4 L.core.cin _ _ hz]
 exact ReorderedAFixed.transport _ s _ _ eq f
#print axioms body_frame
end ECDSAAdd.Entrant.Ghost3KnownA

end

-- Verified component Ghost3SignA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3SignA
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed A161Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=Ghost3CacheA.hosts
abbrev p:=ReorderedAFixed.p

def suffix:Program:=ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin++
 A161Carry.buildPost acc pad bank L.core.cin src++Ghost3CacheA.middle++
 ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts

def loop:Program:=SignAHead.head++suffix

theorem loop_eq(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p)
 (s:State)(m:List Bool)(hf:SquareFrame L.core.out base O s.basis):
 run loop m s=run Ghost3KnownA.loop
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
 have eq:=SignRetape.replace SignAHead.head (ReorderedAHead.head acc pad bank L.core.cin src) suffix s m h
 simpa only [loop,suffix,Ghost3KnownA.loop,Ghost3CacheA.loop,Ghost3CacheA.build,Ghost3CacheA.unbuild,Ghost3KnownA.hosts,ReorderedABuild.build,List.append_assoc] using eq

theorem frame(base:BasisState)(hc:L.PairClean base)(hsum:base q=false)(hV:base r=false)(hP:base p=false)
 (hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then A161Low4Facts.Klow-4294968272*regValue src base else 4294968272*regValue src base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have e:=loop_eq base hc O hO s m hf
 have old:=Ghost3KnownA.frame base hc hsum hV hP hd O hO s (SignRetape.tape SignAHead.head (ReorderedAHead.head acc pad bank L.core.cin src) m) hf
 exact ReorderedAFixed.transport _ s _ _ e old

def fold:Program:=loop

def rawBody:Program:=measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++fold)
theorem raw_body_frame (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base g=false → M=0) (hd:base d=false) :
 Triple (SquareFrame L.core.out base O) rawBody
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base g))) := by
 have hb:M^2<2^256:=by simpa using square_bound M 128 hM
 have vZero:base (eV L)=false:=eV_zero_of_product_lt L hw base (by rw [hP];exact hb)
 have pZero:base (spare L)=false:=spare_zero L hw base M hP
 have ff : ∀ O, O<SquareReduction.p →
  Triple (SquareFrame L.core.out base O) fold
   (SquareFrame L.core.out base (((if base g then A161Low4Facts.Klow-4294968272*regValue (hiReg L) base
    else 4294968272*regValue (hiReg L) base)+(SquareReduction.p-1-O))%SquareReduction.p)) :=
  fun O hO=>frame base hc hzero vZero pZero hd O hO
 exact A161Low4Body.body_frame L hw hn g A161Low4FixedFold.ready.1 base M hM hP hc hzero O hO hg fold ff


def body:Program:=rawBody++ReorderedRecordPadding.program 7 L.core.cin

theorem body_frame (base:BasisState) (M:Nat) (hM:M<2^128)
 (hP:regValue L.core.product base=M^2) (hc:L.PairClean base) (hzero:base q=false)
 (O:Nat) (hO:O<SquareReduction.p) (hg:base g=false → M=0) (hd:base d=false) :
 Triple (SquareFrame L.core.out base O) body
  (SquareFrame L.core.out base (A161Low4Offsets.resAFlow (M^2) O (base g))) := by
 intro s m hf
 have f:=raw_body_frame base M hM hP hc hzero O hO hg hd s (m.take (measurementCount rawBody)) hf
 have hz:(run rawBody (m.take (measurementCount rawBody)) s).basis L.core.cin=false:=
  (f.2.2 L.core.cin (by decide)).trans hc.cin
 have eq:run body m s=run rawBody (m.take (measurementCount rawBody)) s:=by
  rw [body,run_append,ReorderedRecordPadding.run_zero 7 L.core.cin _ _ hz]
 exact ReorderedAFixed.transport _ s _ _ eq f
#print axioms loop_eq
#print axioms body_frame
end ECDSAAdd.Entrant.Ghost3SignA

end

-- Verified component Ghost3ACounts
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3ACounts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed ControlLoan1589BFFold
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
abbrev p:=ReorderedAFixed.p
abbrev hosts:=Ghost3CacheA.hosts

theorem cache_counts:
 toffoliCount (ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127 ∧
 measurementCount (ReorderedGenericCache.cachedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127 ∧
 toffoliCount (ReorderedGenericCache.consumedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=21 ∧
 measurementCount (ReorderedGenericCache.consumedAdd 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin)=127:=by
 have old:=addInPlace_counts src ((acc.take 138).drop 10) (bank.take 127) L.core.cin (by decide) (by decide)
 rw [←MixedLiteralAdderDevelop.read_add_eq] at old
 have bal:=ReorderedGenericCache.count_balance 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by decide) (by decide)
 change toffoliCount (mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) L.core.cin)=127 ∧
  measurementCount (mappedAdd (mappedRead src false) ((acc.take 138).drop 10) (bank.take 127) L.core.cin)=127 at old
 omega

theorem pieces:
 toffoliCount (ReorderedABuild.build 106 acc pad bank L.core.cin src hosts)=386 ∧
 measurementCount (ReorderedABuild.build 106 acc pad bank L.core.cin src hosts)=386 ∧
 toffoliCount (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts)=126 ∧
 measurementCount (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts)=386:=by
 have f6:=Acc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide)
 have f32:=Acc.fits_prefix acc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide)
 have seed:=Acc.seed_counts acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (A161NarrowAcc.terms_mem src).1).toFitsLen
 have sub:=Acc.op_counts (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6) (by decide) f6.toFitsLen
 have top:=Acc.op_counts (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen
 have preInv:=CodexNarrowTailResource.accSub_counts 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32)
  (by decide) f32.toFitsLen (by decide)
 have tail:=ReorderedKnownTail.counts src pad ((acc.take 138).drop 6) (bank.take 131) L.core.cin
  (by decide) (by decide) (by decide) (by decide)
 have notC:=notRegister_counts ((acc.take 138).drop 10)
 have cache:=cache_counts
 change toffoliCount (ReorderedATail.tail acc pad bank L.core.cin src)=0 ∧
  measurementCount (ReorderedATail.tail acc pad bank L.core.cin src)=131 at tail
 change toffoliCount (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))=131 ∧
  measurementCount (Acc.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6))=131 at sub
 change toffoliCount (Acc.op (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32))=128 ∧
  measurementCount (Acc.op (acc.take 161) pad bank L.core.cin 161 false (Acc.earlyTerm src false 32))=128 at top
 change toffoliCount (CodexKnownOnesTail.accSub 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32))=105 ∧
  measurementCount (CodexKnownOnesTail.accSub 106 (acc.take 161) pad bank L.core.cin 161 (Acc.earlyTerm src false 32))=128 at preInv
 simp only [ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,
  ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,ReorderedConsumedSub.consumed,A161Carry.unbuildPre,
  toffoliCount_append,measurementCount_append]
 omega

#print axioms pieces

end ECDSAAdd.Entrant.Ghost3ACounts

end

-- Verified component Ghost3APhysical
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3APhysical
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires A161Low4FixedFold.checked
abbrev hosts:=Ghost3CacheA.hosts

theorem body_physical:GatePhysical Ghost3KnownA.body:=by
 have f6:=ReorderedAcc.fits_prefix acc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have subP:=ReorderedPhysical.op (acc.take 138) pad bank L.core.cin 138 true (Acc.earlyTerm src true 6) f6
 have seedP:GatePhysical (Acc.seedOp acc pad 161 (Acc.earlyTerm src false 4)):=by
  have nd:=Acc.fits_nodup acc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
   (fits _ (A161NarrowAcc.terms_mem src).1)
  exact copyRegister_physical none _ _
   ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
 have topP:=Acc.op_prefix_physical acc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide) false
 have nd:(L.core.cin::(src++(acc.take 138).drop 10++bank.take 127)).Nodup:=by decide +kernel
 have cacheP:=ReorderedPhysical.cached 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by decide) (by decide) nd (by
   intro h hh bad
   exact (by decide +kernel : ∀h∈hosts,h∉bank) h hh (List.mem_of_mem_take bad))
 have buildP:GatePhysical (ReorderedABuild.build 106 acc pad bank L.core.cin src hosts):=by
  simp only [ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,gatePhysical_append]
  exact ⟨⟨⟨seedP,subP⟩,cacheP.1⟩,topP⟩
 have notP:=notRegister_physical ((acc.take 138).drop 10)
 have inverseP:GatePhysical (ReorderedConsumedSub.consumed 106 src ((acc.take 138).drop 10) (bank.take 127) hosts L.core.cin):=by
  simp only [ReorderedConsumedSub.consumed,gatePhysical_append]
  exact ⟨⟨notP,cacheP.2⟩,notP⟩
 have tailP:GatePhysical (ReorderedATail.tail acc pad bank L.core.cin src):=by
  apply KnownOutputAdder.program_physical (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
   ((acc.take 138).drop 6) (bank.take 131) L.core.cin
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
 have oldInv:=(A161KnownTail.build8_physical acc pad bank L.core.cin src lengths.1 (by decide) fits).2
 simp only [A161KnownTail.unbuild8,gatePhysical_append] at oldInv
 have preInv:GatePhysical (A161Carry.unbuildPre acc pad bank L.core.cin src):=oldInv.1.1.1
 have unbuildP:GatePhysical (ReorderedAUnbuild.unbuild 106 acc pad bank L.core.cin src hosts):=by
  simp only [ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,gatePhysical_append]
  exact ⟨⟨preInv,inverseP⟩,⟨tailP,seedP⟩⟩
 have old:GatePhysical A161Low4FixedFold.body:=by
  have base:=aBodyTriple_physical L hw g (List.nodup_cons.mpr ⟨A161Low4FixedFold.ready.1,hn⟩)
  simp only [aBodyTriple,gatePhysical_append] at base
  simp only [A161Low4FixedFold.body,gatePhysical_append]
  exact ⟨base.1,base.2.1,A161Low4FixedFold.fold_physical⟩
 simp only [A161Low4FixedFold.body,A161Low4FixedFold.fold100,A161Low4GenericFold.loop,
  gatePhysical_append] at old
 have midOld:GatePhysical KnownAMidStaged.body:=by
  unfold GatePhysical
  intro i hi
  exact old.2.2.1.2 i ((KnownSparseFold.Cert.sublist _ _ _ _ _ KnownAMidStaged.cert).subset hi)
 have midP:GatePhysical Ghost3CacheA.middle:=
  RelocateResources.physical GhostRelocatedKnown.ports GhostRelocatedKnown.ports_inj KnownAMidStaged.body midOld
 simp only [Ghost3KnownA.body,Ghost3KnownA.rawBody,Ghost3KnownA.fold,Ghost3KnownA.loop,Ghost3CacheA.loop,Ghost3CacheA.build,Ghost3CacheA.unbuild,gatePhysical_append]
 exact ⟨⟨old.1,old.2.1,⟨⟨buildP,midP⟩,unbuildP⟩⟩,ReorderedPhysical.padding 4 L.core.cin⟩
#print axioms body_physical

end ECDSAAdd.Entrant.Ghost3APhysical

end

-- Verified component Ghost3ABalance
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3ABalance
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedAFixed Challenge
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem counts:toffoliCount Ghost3SignA.body+3=toffoliCount SignKnownA.body ∧
 measurementCount Ghost3SignA.body=measurementCount SignKnownA.body:=by
 have nc:=Ghost3ACounts.cache_counts
 have oc:=ReorderedACounts.cache_counts
 have np:=Ghost3ACounts.pieces
 have op:=ReorderedACounts.pieces
 have mid:=GhostRelocatedKnown.A.counts
 change toffoliCount GhostRelocatedKnown.A.program=toffoliCount KnownAMidStaged.body ∧
  measurementCount GhostRelocatedKnown.A.program=measurementCount KnownAMidStaged.body at mid
 simp only [Ghost3ACounts.hosts] at nc np
 simp only [ReorderedACounts.hosts] at oc op
 simp only [Ghost3SignA.body,Ghost3SignA.rawBody,Ghost3SignA.fold,Ghost3SignA.loop,Ghost3SignA.suffix,Ghost3SignA.hosts,Ghost3CacheA.middle,
  SignKnownA.body,SignKnownA.rawBody,SignKnownA.fold,SignKnownA.loop,SignKnownA.suffix,toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩

theorem slots:gateSlots Ghost3SignA.body+1=gateSlots SignKnownA.body:=by
 have nc:=ReorderedSlots.cache 106 src ((acc.take 138).drop 10) (bank.take 127) Ghost3CacheA.hosts L.core.cin
  (by decide) (by decide) (by decide) Ghost3CacheA.geometry.2.1
 have oc:=ReorderedSlots.cache 103 src ((acc.take 138).drop 10) (bank.take 127) ReorderedAFixed.hosts L.core.cin
  (by decide) (by decide) (by decide) ReorderedAFixed.host_geometry.2.1
 have mid:=RelocateResources.slots GhostRelocatedKnown.ports KnownAMidStaged.body
 simp only [Ghost3SignA.body,Ghost3SignA.rawBody,Ghost3SignA.fold,Ghost3SignA.loop,Ghost3SignA.suffix,Ghost3SignA.hosts,Ghost3CacheA.middle,
  SignKnownA.body,SignKnownA.rawBody,SignKnownA.fold,SignKnownA.loop,SignKnownA.suffix,
  ReorderedAUnbuild.unbuild,ReorderedConsumedSub.consumed,gateSlots_append]
 change gateSlots GhostRelocatedKnown.A.program=gateSlots KnownAMidStaged.body+8 at mid
 omega

end ECDSAAdd.Entrant.Ghost3ABalance

end

-- Verified component SignedBodySupportA
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3BodyResources
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout Challenge
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots List.toFinset

open ReorderedAFixed in
theorem a_support:wires Ghost3SignA.body⊆wires Ghost3KnownA.body:=by
 have loop:wires Ghost3SignA.loop⊆wires Ghost3KnownA.loop:=by
  have eq:Ghost3KnownA.loop=ReorderedAHead.head acc pad bank L.core.cin src++Ghost3SignA.suffix:=by
   simp only [Ghost3KnownA.loop,Ghost3CacheA.loop,Ghost3CacheA.build,Ghost3CacheA.unbuild,ReorderedABuild.build,Ghost3KnownA.hosts,Ghost3SignA.suffix,Ghost3SignA.hosts,List.append_assoc]
  rw [Ghost3SignA.loop,eq,wires_append,wires_append]
  exact Finset.union_subset_union SignAHeadSupport.support (Finset.Subset.refl _)
 have pad:wires (ReorderedRecordPadding.program 7 L.core.cin)=wires (ReorderedRecordPadding.program 4 L.core.cin):=by
  simp [ReorderedRecordPadding.program,List.replicate_succ,wires,Instr.wires,correctionWires]
 simp only [Ghost3SignA.body,Ghost3SignA.rawBody,Ghost3SignA.fold,Ghost3KnownA.body,Ghost3KnownA.rawBody,
  Ghost3KnownA.fold,wires_append]
 rw [pad]
 repeat' first
  | exact loop
  | exact Finset.Subset.refl _
  | apply Finset.union_subset_union

open ReorderedAFixed in
theorem a_physical:GatePhysical Ghost3SignA.body:=by
 have old:=Ghost3APhysical.body_physical
 have head:=SignAHeadResources.physical
 have pad:=ReorderedPhysical.padding 7 L.core.cin
 simp only [Ghost3SignA.body,Ghost3SignA.rawBody,Ghost3SignA.fold,Ghost3SignA.loop,Ghost3SignA.suffix,Ghost3SignA.hosts,
  Ghost3KnownA.body,Ghost3KnownA.rawBody,Ghost3KnownA.fold,Ghost3KnownA.loop,Ghost3CacheA.loop,Ghost3CacheA.build,Ghost3CacheA.unbuild,Ghost3KnownA.hosts,
  ReorderedABuild.build,gatePhysical_append] at old ⊢
 tauto

end ECDSAAdd.Entrant.Ghost3BodyResources

end

-- Verified component Ghost3AFine
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3AFine
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop ReorderedAFixed OwnDiagAll12Square ControlLoan1589BFFold
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] RelocateThreeGhosts.program
attribute [local irreducible] ECDSAAdd.wires A161Low4FixedFold.checked List.toFinset
abbrev realAcc:=A161Fold.accReg L
def ambient:List Wire:=A161Low4GenericFold.ambient L g hs
abbrev hosts:=Ghost3CacheA.hosts
def domain:Finset Wire:=(L.core.cin::(src++realAcc++pad++bank)).toFinset

theorem list_support(A B:List Wire)(h:∀q∈A,q∈B):A.toFinset⊆B.toFinset:=by
 intro q hq
 exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem domain_in:domain⊆ambient.toFinset:=
 list_support (L.core.cin::(src++realAcc++pad++bank)) ambient (by decide +kernel)

theorem loop_support:wires Ghost3KnownA.loop⊆ambient.toFinset:=by
 have fit:=A161GenericFold.smallFit L hw hn
 have len:=A161Fold.acc_lengths L hw
 have seed:=(Acc.seed_support realAcc pad bank L.core.cin 161 (Acc.earlyTerm src false 4)
  len.1 (fit _ (A161NarrowAcc.terms_mem src).1)).trans domain_in
 have sub:=(Acc.op_prefix_support realAcc pad bank L.core.cin 161 138 (Acc.earlyTerm src true 6)
  len.1 (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.1) (by decide) true).trans domain_in
 have top(neg:Bool):wires (Acc.op (realAcc.take 161) pad bank L.core.cin 161 neg (Acc.earlyTerm src false 32))⊆ambient.toFinset:=
  (Acc.op_prefix_support realAcc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
   len.1 (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide) neg).trans domain_in
 have cacheDomain:(L.core.cin::(src++(realAcc.take 138).drop 10++bank.take 127)).toFinset∪hosts.toFinset⊆
  ambient.toFinset:=Finset.union_subset
   (list_support _ _ (by decide +kernel)) (list_support _ _ (by decide +kernel))
 have cached:=ReorderedSupport.cached 106 src ((realAcc.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by decide) (by decide) (by decide) (by decide)
 have build:wires (ReorderedABuild.build 106 realAcc pad bank L.core.cin src hosts)⊆ambient.toFinset:=by
  simp only [ReorderedABuild.build,ReorderedAHead.head,A161Carry.buildPost,wires_append]
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset seed sub) (cached.1.trans cacheDomain)) (top false)
 have f32:=Acc.fits_prefix realAcc pad bank L.core.cin 161 161 (Acc.earlyTerm src false 32)
  (by decide) (fit _ (A161NarrowAcc.terms_mem src).2.2.2) (by decide)
 have preInv:wires (A161Carry.unbuildPre realAcc pad bank L.core.cin src)⊆ambient.toFinset:=
  (CodexNarrowTailResource.accSub_support 106 (realAcc.take 161) pad bank L.core.cin 161
   (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen (by decide)).trans (top true)
 have consumed:=(ReorderedSupport.consumed 106 src ((realAcc.take 138).drop 10) (bank.take 127) hosts L.core.cin
  (by decide) (by decide) (by decide) (by decide) (by decide)).trans cacheDomain
 have tail:=KnownOutputAdder.program_support (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
  ((realAcc.take 138).drop 6) (bank.take 131) L.core.cin
 rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tail
 have tailDomain:((src++pad.take 4)++src.drop 2++(realAcc.take 138).drop 6++bank.take 131++[L.core.cin]).toFinset⊆
  ambient.toFinset:=list_support _ _ (by decide +kernel)
 have unbuild:wires (ReorderedAUnbuild.unbuild 106 realAcc pad bank L.core.cin src hosts)⊆ambient.toFinset:=by
  simp only [ReorderedAUnbuild.unbuild,ReorderedAUnbuild.after,wires_append]
  exact Finset.union_subset (Finset.union_subset preInv consumed) (Finset.union_subset (tail.trans tailDomain) seed)
 have midOld:wires KnownAMidStaged.body⊆ambient.toFinset:=by
  intro u hu
  have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownAMidStaged.cert
  have checked:u∈wires A161Low4FixedFold.checked.out:=Skip4.wires_mono_of_mem _ _ (fun _ h=>sub.subset h) hu
  have old:u∈wires A161Low4FixedFold.fold100:=by
   simp only [A161Low4FixedFold.fold100,A161Low4GenericFold.loop,wires_append,Finset.mem_union]
   exact Or.inl (Or.inr checked)
  exact A161Low4GenericFold.support L hw hn g hs A161Low4FixedFold.checked.out A161Low4FixedFold.cert100 old
 have mid:wires Ghost3CacheA.middle⊆ambient.toFinset:=
  RelocateResources.support GhostRelocatedKnown.ports KnownAMidStaged.body _ midOld
   (by intro i;apply List.mem_toFinset.mpr;fin_cases i <;>decide +kernel)
 simp only [Ghost3KnownA.loop,Ghost3CacheA.loop,wires_append]
 rw [Ghost3CacheA.build,Ghost3CacheA.unbuild,ReorderedAStructural.build_eq,ReorderedAStructural.unbuild_eq]
 exact Finset.union_subset (Finset.union_subset build mid) unbuild

theorem padding_support:wires (ReorderedRecordPadding.program 4 L.core.cin)⊆ambient.toFinset:=by
 have sub:wires (ReorderedRecordPadding.program 4 L.core.cin)⊆[L.core.cin].toFinset:=by decide +kernel
 exact sub.trans (list_support _ _ (by decide +kernel))

theorem body_fine:wires Ghost3KnownA.body⊆insert d (wires (aBodyTriple L g)):=by
 intro u hu
 simp only [Ghost3KnownA.body,Ghost3KnownA.rawBody,Ghost3KnownA.fold,wires_append,Finset.mem_union] at hu
 rcases hu with (hu|(hu|hu))|hu
 · apply Finset.mem_insert_of_mem
   simp only [aBodyTriple,wires_append,Finset.mem_union]
   exact Or.inl hu
 · apply Finset.mem_insert_of_mem
   simp only [aBodyTriple,wires_append,Finset.mem_union]
   exact Or.inr (Or.inl hu)
 · exact A161Low4Fine.ambient_fine (loop_support hu)
 · exact A161Low4Fine.ambient_fine (padding_support hu)

#print axioms body_fine
end ECDSAAdd.Entrant.Ghost3AFine

end

-- Verified component Ghost3AFineSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3AFineSupport
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop ReorderedAFixed ControlLoan1589BFFold
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.wires List.toFinset

theorem body_support:wires Ghost3KnownA.body⊆(d::g::L.wires).toFinset:=by
 have h:=Ghost3AFine.body_fine.trans (Finset.insert_subset_insert d (aBodyTriple_support L hw hn g))
 simpa only [List.toFinset_cons] using h

theorem body_eU_free:eU L∉wires Ghost3KnownA.body:=by
 have old:eU L∉wires (aBodyTriple L g):=fun h=>
  eU_off_aBodyDual L hw hn g A161Low4FixedFold.ready.1 (aBodyTriple_subset L hw g h)
 have ne:eU L≠d:=by decide
 exact fun h=>(Finset.mem_insert.mp (Ghost3AFine.body_fine h)).elim ne old
#print axioms body_support
#print axioms body_eU_free
end ECDSAAdd.Entrant.Ghost3AFineSupport

end

section

-- Verified component RelocatedKnownC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.GhostRelocatedKnown
open Arithmetic InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ECDSAAdd.toffoliCount ECDSAAdd.measurementCount RelocateThreeGhosts.program RelocateThreeGhosts.first RelocateThreeGhosts.second ClearCopyBorrow.program ClearXorBorrow.program
namespace C
abbrev acc:List Wire:=C163Low4Middle.ga
abbrev src:List Wire:=C163Low4Middle.src
abbrev L:Arithmetic.CuccaroStreamedSquareWideLayout:=C163Low4Middle.L
abbrev original:Program:=KnownCMidStaged.body
def program:Program:=RelocateThreeGhosts.program ports original

theorem maps:acc.getD 0 0=4757 ∧ acc.getD 1 0=4758 ∧ acc.getD 2 0=4759 ∧
 src.getD 0 0=4243 ∧ src.getD 1 0=4244 ∧ src.getD 2 0=4245 ∧
 acc.getD 4 0=4505 ∧ acc.getD 5 0=4506 ∧ acc.getD 6 0=4507:=by decide +kernel

theorem source_free(u:Wire)(hu:u∈([4243,4244,4245]:List Wire)):u∉wires original:=by
 intro bad
 have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert
 have old:=Skip4.wires_mono_of_mem original _ (fun _ h=>sub.subset h) bad
 have off:u∉wires C163Low4Middle.bankChecked.out:=by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
  rcases hu with rfl|rfl|rfl
  all_goals exact GhostMiddleSupport.c_free _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
 exact off old

theorem equivalent(H:Nat)(s:State)(m:List Bool)
 (before:WReady acc C163Low4Middle.pad C163Low4Middle.bank L.core.cin src H s)
 (after:WReady acc C163Low4Middle.pad C163Low4Middle.bank L.core.cin src H (run original m s)):
 run program m s=run original m s:=by
 rcases maps with ⟨q0,q1,q2,a0,a1,a2,b0,b1,b2⟩
 have val:regValue acc s.basis=4294968272*regValue src s.basis:=by rw [before.2.1];exact before.1
 have copies:=LowWordRecovery.copies acc src s.basis
  (by have h:=C163Low4Middle.lengths.1;change acc.length=_ at h;omega)
  (by have h:=C163Low4Middle.lengths.2.2.2;change src.length=_ at h;omega) val
 simp only [a0,a1,a2,b0,b1,b2] at copies
 have zi(i:Nat)(hi:i<3):s.basis (acc.getD i 0)=false:=
  LowWordRecovery.low_register_zero acc s.basis H i (by omega)
   (by have h:=C163Low4Middle.lengths.1;change acc.length=_ at h;omega) before.1
 have zo(i:Nat)(hi:i<3):(run original m s).basis (acc.getD i 0)=false:=
  LowWordRecovery.low_register_zero acc (run original m s).basis H i (by omega)
   (by have h:=C163Low4Middle.lengths.1;change acc.length=_ at h;omega) after.1
 have stable:∀u∈acc,(run original m s).basis u=s.basis u:=
  (regValue_eq_iff acc _ _).mp (after.1.trans before.1.symm)
 apply RelocateThreeGhosts.equivalent ports ports_inj original s m
 · exact source_free _ (by decide)
 · exact source_free _ (by decide)
 · exact source_free _ (by decide)
 · simpa only [q0] using zi 0 (by decide)
 · simpa only [q1] using zi 1 (by decide)
 · simpa only [q2] using zi 2 (by decide)
 · exact copies.1
 · exact copies.2.1
 · exact copies.2.2
 · simpa only [q0] using zo 0 (by decide)
 · simpa only [q1] using zo 1 (by decide)
 · simpa only [q2] using zo 2 (by decide)
 · exact stable _ (by decide +kernel)
 · exact stable _ (by decide +kernel)
 · exact stable _ (by decide +kernel)
#print axioms equivalent
end C
end ECDSAAdd.Entrant.GhostRelocatedKnown

namespace ECDSAAdd.Entrant.GhostRelocatedKnown
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.toffoliCount ECDSAAdd.measurementCount RelocateThreeGhosts.program
namespace C
theorem counts:toffoliCount program=toffoliCount original ∧ measurementCount program=measurementCount original:=RelocateThreeGhosts.counts ports original

theorem ghosts_free:4757∉wires program ∧ 4758∉wires program ∧ 4759∉wires program:=by
 exact RelocateThreeGhosts.ghosts_free ports ports_inj original
  (source_free _ (by decide)) (source_free _ (by decide)) (source_free _ (by decide))

#print axioms ghosts_free
end C
end ECDSAAdd.Entrant.GhostRelocatedKnown

end

-- Verified component Ghost3CacheCSetup
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
def spares:List Wire:=[4757,4758,4759]
def phantoms:List Wire:=[100000,100001,100002]
def viewPerm:Wire→Wire:=fun q=>Equiv.swap 4757 100000 (Equiv.swap 4758 100001 (Equiv.swap 4759 100002 q))
def viewAcc:List Wire:=ga.map viewPerm
def hosts : List Wire := ReorderedCFixed.hosts++spares

theorem geometry : hosts.Nodup ∧ hosts.length=102 ∧ viewAcc.length=163 ∧
 (∀h∈hosts,h∉L.core.cin::(src++viewAcc++pad++bank)):=by decide +kernel

theorem fitsView(f:MeasuredSquareFold)(hm:f∈earlyHTerms src):
 Acc.Fits viewAcc pad bank L.core.cin 163 f:=by
 have old:=C163Low4Middle.fits f hm
 have hsrc:f.src=src:=by
  simp only [earlyHTerms,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl <;>rfl
 refine {toFitsLen:=old.toFitsLen,nd:=?_}
 rw [hsrc]
 decide +kernel

theorem drop4:viewAcc.drop 4=ga.drop 4:=by decide +kernel
theorem drop6:(viewAcc.take 140).drop 6=(ga.take 140).drop 6:=by decide +kernel
theorem drop10:(viewAcc.take 140).drop 10=(ga.take 140).drop 10:=by decide +kernel
theorem drop32:(viewAcc.take 163).drop 32=(ga.take 163).drop 32:=by decide +kernel
theorem plainBuild_eq:
 ReorderedCPlain.build viewAcc pad bank L.core.cin src=ReorderedCPlain.build ga pad bank L.core.cin src:=by
 simp only [ReorderedCPlain.build,ReorderedCPre.pre,C163Carry.buildPost,Acc.seedOp,Acc.op,Acc.ty,Acc.earlyTerm,drop4,drop6,drop10,drop32]
theorem plainUnbuild_eq:
 ReorderedCPlain.unbuild viewAcc pad bank L.core.cin src=ReorderedCPlain.unbuild ga pad bank L.core.cin src:=by
 simp only [ReorderedCPlain.unbuild,C163Carry.unbuildPre,CodexKnownOnesTail.accSub,ReorderedCTail.tail,Acc.seedOp,Acc.op,Acc.ty,Acc.earlyTerm,drop4,drop6,drop10,drop32]
#print axioms geometry
end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCState
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run

def erase(s:State):State:=EraseListProof.erase phantoms s

theorem phantom_off(q:Wire)(hq:q∈phantoms):q∉L.core.cin::(src++ga++pad++bank):=by
 simp only [phantoms,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel

theorem spare_mem(q:Wire)(hq:q∈spares):q∈ga:=by
 simp only [spares,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl <;>decide +kernel

theorem bit_same(s:State)(q:Wire)(h:q∉phantoms):(erase s).basis q=s.basis q:=by
 exact (EraseListProof.basis phantoms s q).trans (if_neg h)

theorem reg_map(xs:List Wire)(f:Wire→Wire)(s t:BasisState)
 (h:∀q∈xs,s (f q)=t q):regValue (xs.map f) s=regValue xs t:=by
 induction xs with
 | nil=>rfl
 | cons a as ih=>
  have ha:=h a (by simp)
  have hr:=ih (fun q hq=>h q (by simp [hq]))
  simp only [regValue,List.map_cons,List.foldr_cons] at hr ⊢
  rw [ha,hr]

theorem reg_view(s:State)(hz:∀q∈spares,s.basis q=false):regValue viewAcc (erase s).basis=regValue ga s.basis:=by
 apply reg_map
 intro q hq
 have off:q∉phantoms:=by intro h;exact phantom_off q h (by simp [hq])
 by_cases h0:q=4757
 · subst q
   simp [viewPerm,Equiv.swap_apply_def,erase,EraseListProof.basis,phantoms,hz 4757 (by decide)]
 by_cases h1:q=4758
 · subst q
   simp [viewPerm,Equiv.swap_apply_def,erase,EraseListProof.basis,phantoms,hz 4758 (by decide)]
 by_cases h2:q=4759
 · subst q
   simp [viewPerm,Equiv.swap_apply_def,erase,EraseListProof.basis,phantoms,hz 4759 (by decide)]
 have p0:q≠100000:=by intro e;apply off;subst q;decide
 have p1:q≠100001:=by intro e;apply off;subst q;decide
 have p2:q≠100002:=by intro e;apply off;subst q;decide
 have fix:viewPerm q=q:=by simp [viewPerm,Equiv.swap_apply_def,h0,h1,h2,p0,p1,p2]
 rw [fix]
 exact bit_same s q off

theorem reg_same(xs:List Wire)(s:State)(off:∀q∈phantoms,q∉xs):
 regValue xs (erase s).basis=regValue xs s.basis:=by
 apply regValue_congr
 intro q hq
 exact bit_same s q (fun h=>off q h hq)

theorem ready_view(H:Nat)(s:State)(hz:∀q∈spares,s.basis q=false)(h:WReady ga pad bank L.core.cin src H s):
 WReady viewAcc pad bank L.core.cin src H (erase s):=by
 refine ⟨(reg_view s hz).trans h.1,?_,?_,?_,?_⟩
 · exact (reg_same src s (fun q hq bad=>phantom_off q hq (by simp [bad]))).trans h.2.1
 · intro q hq
   exact (bit_same s q (fun bad=>phantom_off q bad (by simp [hq]))).trans (h.2.2.1 q hq)
 · intro q hq
   exact (bit_same s q (fun bad=>phantom_off q bad (by simp [hq]))).trans (h.2.2.2.1 q hq)
 · exact (bit_same s L.core.cin (fun bad=>phantom_off _ bad (by simp))).trans h.2.2.2.2

theorem run_erase(P:Program)(m:List Bool)(s:State)(off:∀q∈phantoms,q∉wires P):
 run P m (erase s)=erase (run P m s):=EraseListProof.commute phantoms P m s off

theorem erase_eq_implies(s t:State)(hv:∀q∈phantoms,s.basis q=t.basis q)(he:erase s=erase t):s=t:=
 EraseListProof.cancel phantoms s t hv he
#print axioms ready_view
end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCPlainSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset

theorem plain_support(A:List Wire)(len:A.length=163)
 (fit:∀f∈earlyHTerms src,Acc.Fits A pad bank L.core.cin 163 f):
 wires (ReorderedCPlain.build A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset ∧
 wires (ReorderedCPlain.unbuild A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=by
 have seed:=Acc.seed_support A pad bank L.core.cin 163 (Acc.earlyTerm src false 4) len
  (fit _ (C163NarrowAcc.terms_mem src).1)
 have op6:=Acc.op_prefix_support A pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  len (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) true
 have op10(neg:Bool):wires (Acc.op (A.take 140) pad bank L.core.cin 140 neg (Acc.earlyTerm src false 10))⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=by
  have ff:=ReorderedAcc.fits_prefix A pad bank L.core.cin 163 140 (Acc.earlyTerm src false 10)
   (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.1) (by decide) (by decide)
  rw [ReorderedAcc.op_wires (A.take 140) pad bank L.core.cin 140 neg (Acc.earlyTerm src false 10) (by simp [len]) ff]
  intro q hq
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [Acc.tx,Acc.ty,Acc.tc,Acc.earlyTerm,if_true,List.mem_cons,List.mem_append] at h ⊢
  have pa:∀k,q∈pad.take k→q∈pad:=fun _=>List.mem_of_mem_take
  have aa:q∈(A.take 140).drop 10→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:∀k,q∈bank.take k→q∈bank:=fun _=>List.mem_of_mem_take
  tauto
 have top(neg:Bool):wires (Acc.op (A.take 163) pad bank L.core.cin 163 neg (Acc.earlyTerm src false 32))⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=
  Acc.op_prefix_support A pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
   len (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide) neg
 have f32:=Acc.fits_prefix A pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide)
 have preInv:wires (C163Carry.unbuildPre A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=
  (CodexNarrowTailResource.accSub_support 108 (A.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32)
   (by simp [len]) f32.toFitsLen (by decide)).trans (top true)
 have tail:=KnownOutputAdder.program_support (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
  ((A.take 140).drop 6) (bank.take 133) L.core.cin
 rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tail
 have td:((src++pad.take 4)++src.drop 2++(A.take 140).drop 6++bank.take 133++[L.core.cin]).toFinset⊆
  (L.core.cin::(src++A++pad++bank)).toFinset:=by
  intro q hq
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [List.mem_append,List.mem_singleton] at h
  have pp:q∈pad.take 4→q∈pad:=List.mem_of_mem_take
  have ss:q∈src.drop 2→q∈src:=List.mem_of_mem_drop
  have aa:q∈(A.take 140).drop 6→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:q∈bank.take 133→q∈bank:=List.mem_of_mem_take
  simp only [List.mem_cons,List.mem_append]
  tauto
 have tailSupport:wires (ReorderedCTail.tail A pad bank L.core.cin src)⊆(L.core.cin::(src++A++pad++bank)).toFinset:=tail.trans td
 constructor
 · simp only [ReorderedCPlain.build,ReorderedCPre.pre,C163Carry.buildPost,wires_append]
   exact Finset.union_subset (Finset.union_subset (Finset.union_subset seed op6) (op10 false)) (top false)
 · simp only [ReorderedCPlain.unbuild,wires_append]
   exact Finset.union_subset (Finset.union_subset (Finset.union_subset preInv (op10 true)) tailSupport) seed
#print axioms plain_support
end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCCachedSupport
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires List.toFinset

theorem cached_support(A:List Wire)(len:A.length=163)
 (fit:∀f∈earlyHTerms src,Acc.Fits A pad bank L.core.cin 163 f):
 wires (ReorderedCBuild.build 102 A pad bank L.core.cin src Ghost3CacheC.hosts)⊆
  (L.core.cin::(src++A++pad++bank)).toFinset∪Ghost3CacheC.hosts.toFinset ∧
 wires (ReorderedCUnbuild.unbuild 102 A pad bank L.core.cin src Ghost3CacheC.hosts)⊆
  (L.core.cin::(src++A++pad++bank)).toFinset∪Ghost3CacheC.hosts.toFinset:=by
 let D:Finset Wire:=(L.core.cin::(src++A++pad++bank)).toFinset∪Ghost3CacheC.hosts.toFinset
 have pf:wires (ReorderedCPlain.build A pad bank L.core.cin src)⊆D:=
  (plain_support A len fit).1.trans Finset.subset_union_left
 have pi:wires (ReorderedCPlain.unbuild A pad bank L.core.cin src)⊆D:=
  (plain_support A len fit).2.trans Finset.subset_union_left
 have cd:(L.core.cin::(src++(A.take 140).drop 10++bank.take 129)).toFinset∪Ghost3CacheC.hosts.toFinset⊆D:=by
  apply Finset.union_subset ?_ Finset.subset_union_right
  intro q hq
  apply Finset.mem_union_left
  have h:=List.mem_toFinset.mp hq
  apply List.mem_toFinset.mpr
  simp only [List.mem_cons,List.mem_append] at h ⊢
  have aa:q∈(A.take 140).drop 10→q∈A:=fun hh=>List.mem_of_mem_take (List.mem_of_mem_drop hh)
  have bb:q∈bank.take 129→q∈bank:=List.mem_of_mem_take
  tauto
 have cc:=ReorderedSupport.cached 102 src ((A.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin
  (by decide) (by simp [len]) (by decide) (by simp [len];decide +kernel) (by simp [len];decide +kernel)
 have ci:=ReorderedSupport.consumed 102 src ((A.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin
  (by decide) (by simp [len]) (by decide) (by simp [len];decide +kernel) (by simp [len];decide +kernel)
 have hhead:wires (ReorderedCHead.head A pad bank L.core.cin src)⊆D:=by
  intro q hq
  apply pf
  simp only [ReorderedCPlain.build,ReorderedCPre.pre,ReorderedCHead.head,C163Carry.buildPost,wires_append,Finset.mem_union] at hq ⊢
  tauto
 have hpost:wires (C163Carry.buildPost A pad bank L.core.cin src)⊆D:=by
  intro q hq
  apply pf
  simp only [ReorderedCPlain.build,ReorderedCPre.pre,C163Carry.buildPost,wires_append,Finset.mem_union] at hq ⊢
  tauto
 have hpre:wires (C163Carry.unbuildPre A pad bank L.core.cin src)⊆D:=by
  intro q hq
  apply pi
  simp only [ReorderedCPlain.unbuild,wires_append,Finset.mem_union]
  tauto
 have hafter:wires (ReorderedCUnbuild.after A pad bank L.core.cin src)⊆D:=by
  intro q hq
  apply pi
  simp only [ReorderedCPlain.unbuild,ReorderedCUnbuild.after,wires_append,Finset.mem_union] at hq ⊢
  tauto
 constructor
 · simp only [ReorderedCBuild.build,wires_append]
   exact Finset.union_subset (Finset.union_subset hhead (cc.1.trans cd)) hpost
 · simp only [ReorderedCUnbuild.unbuild,wires_append]
   exact Finset.union_subset (Finset.union_subset hpre (ci.trans cd)) hafter
#print axioms cached_support
end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCPrograms
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop FourthASavedCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

def build:Program:=ReorderedCBuild.build 102 ga pad bank L.core.cin src hosts
def unbuild:Program:=ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts
abbrev middle:Program:=GhostRelocatedKnown.C.program

theorem build_view:ReorderedCBuild.build 102 viewAcc pad bank L.core.cin src hosts=build:=by
 simp only [build,ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,
  Acc.seedOp,Acc.op,Acc.ty,Acc.earlyTerm,drop4,drop6,drop10,drop32]
theorem unbuild_view:ReorderedCUnbuild.unbuild 102 viewAcc pad bank L.core.cin src hosts=unbuild:=by
 simp only [unbuild,ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,C163Carry.unbuildPre,
  ReorderedCTail.tail,CodexKnownOnesTail.accSub,Acc.seedOp,Acc.op,Acc.ty,Acc.earlyTerm,drop4,drop6,drop10,drop32]

theorem not_wire(P:Program)(q:Wire)(h:hasWire P q=false):q∉wires P:=by
 intro bad
 have e:hasWire P q=true:=(hasWire_iff P q).mpr bad
 rw [h] at e
 cases e

theorem spare_off_build(q:Wire)(hq:q∈spares):q∉wires (ReorderedCPlain.build ga pad bank L.core.cin src):=by
 rw [←plainBuild_eq]
 intro bad
 have sub:=(plain_support viewAcc geometry.2.2.1 fitsView).1 bad
 exact geometry.2.2.2 q (by simp only [Ghost3CacheC.hosts,List.mem_append];exact Or.inr hq) (List.mem_toFinset.mp sub)
theorem spare_off_unbuild(q:Wire)(hq:q∈spares):q∉wires (ReorderedCPlain.unbuild ga pad bank L.core.cin src):=by
 rw [←plainUnbuild_eq]
 intro bad
 have sub:=(plain_support viewAcc geometry.2.2.1 fitsView).2 bad
 exact geometry.2.2.2 q (by simp only [Ghost3CacheC.hosts,List.mem_append];exact Or.inr hq) (List.mem_toFinset.mp sub)
theorem spare_off_middle(q:Wire)(hq:q∈spares):q∉wires middle:=by
 simp only [spares,List.mem_cons,List.not_mem_nil,or_false] at hq
 rcases hq with rfl|rfl|rfl
 · exact GhostRelocatedKnown.C.ghosts_free.1
 · exact GhostRelocatedKnown.C.ghosts_free.2.1
 · exact GhostRelocatedKnown.C.ghosts_free.2.2

theorem phantom_off_from_small(P:Program)(sm:SmallWireProof.small P=true)(q:Wire)(hq:q∈phantoms):q∉wires P:=by
 have lo:100000≤q:=by
  simp only [phantoms,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl <;>decide
 exact fun bad=>Nat.not_lt_of_ge lo (SmallWireProof.support P sm q bad)

theorem phantom_not_host:∀q∈phantoms,q∉Ghost3CacheC.hosts:=by decide +kernel

theorem phantom_off_build:∀q∈phantoms,q∉wires build:=by
 intro q hq bad
 have sub:=(cached_support ga lengths.1 fits).1 bad
 rcases Finset.mem_union.mp sub with dom|host
 · exact phantom_off q hq (List.mem_toFinset.mp dom)
 · exact phantom_not_host q hq (List.mem_toFinset.mp host)
theorem phantom_off_unbuild:∀q∈phantoms,q∉wires unbuild:=by
 intro q hq bad
 have sub:=(cached_support ga lengths.1 fits).2 bad
 rcases Finset.mem_union.mp sub with dom|host
 · exact phantom_off q hq (List.mem_toFinset.mp dom)
 · exact phantom_not_host q hq (List.mem_toFinset.mp host)
theorem phantom_off_plain_build:∀q∈phantoms,q∉wires (ReorderedCPlain.build ga pad bank L.core.cin src):=by
 intro q hq bad
 exact phantom_off q hq (List.mem_toFinset.mp ((plain_support ga lengths.1 fits).1 bad))
theorem phantom_off_plain_unbuild:∀q∈phantoms,q∉wires (ReorderedCPlain.unbuild ga pad bank L.core.cin src):=by
 intro q hq bad
 exact phantom_off q hq (List.mem_toFinset.mp ((plain_support ga lengths.1 fits).2 bad))
theorem phantom_off_middle(q:Wire)(hq:q∈phantoms):q∉wires middle:=by
 apply RelocateThreeGhosts.outside GhostRelocatedKnown.ports GhostRelocatedKnown.C.original q
 · intro i
   simp only [phantoms,List.mem_cons,List.not_mem_nil,or_false] at hq
   rcases hq with rfl|rfl|rfl <;>fin_cases i <;>decide
 · intro bad
   have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert
   have old:=Skip4.wires_mono_of_mem _ _ (fun _ h=>sub.subset h) bad
   have off:q∉wires C163Low4Middle.bankChecked.out:=by
    simp only [phantoms,List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl
    all_goals exact GhostMiddleSupport.c_free _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
   exact off old
#print axioms phantom_off_middle
end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCLoop
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop ControlledBorrowResearch
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked
 ReorderedCPlain.build ReorderedCPlain.unbuild ReorderedCBuild.build ReorderedCUnbuild.unbuild
 RelocateThreeGhosts.program

def loop:Program:=build++middle++unbuild

theorem host_off_plain(u:Wire)(hu:u∈Ghost3CacheC.hosts):
 u∉wires (ReorderedCPlain.build ga pad bank L.core.cin src) ∧
 u∉wires (ReorderedCPlain.unbuild ga pad bank L.core.cin src) ∧ u∉wires middle:=by
 simp only [Ghost3CacheC.hosts,List.mem_append] at hu
 rcases hu with old|extra
 · refine ⟨(ReorderedCFixed.off_plain u old).1,(ReorderedCFixed.off_plain u old).2,?_⟩
   apply RelocateThreeGhosts.outside GhostRelocatedKnown.ports GhostRelocatedKnown.C.original u
   · exact (by decide +kernel :∀u∈ReorderedCFixed.hosts,∀i:Fin 9,u≠GhostRelocatedKnown.ports i) u old
   · intro bad
     have sub:=KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert
     have h:=Skip4.wires_mono_of_mem _ _ (fun _ h=>sub.subset h) bad
     exact ReorderedCFixed.off_middle u old h
 · exact ⟨spare_off_build u extra,spare_off_unbuild u extra,spare_off_middle u extra⟩

theorem loop_eq(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)
 (ha:regValue ga s.basis=0)(zero:∀h∈Ghost3CacheC.hosts,s.basis h=false)
 (good:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) middle s m)):
 run loop m s=run (ReorderedCPlain.build ga pad bank L.core.cin src++middle++
  ReorderedCPlain.unbuild ga pad bank L.core.cin src) m s:=by
 have hv:∀q∈phantoms,q∉Ghost3CacheC.hosts:=by decide +kernel
 have hsrc:∀q∈phantoms,q∉src:=fun q hq bad=>phantom_off q hq (by simp [bad])
 have hpad:∀q∈phantoms,q∉pad:=fun q hq bad=>phantom_off q hq (by simp [bad])
 have hbank:∀q∈phantoms,q∉bank:=fun q hq bad=>phantom_off q hq (by simp [bad])
 have hcin:L.core.cin∉phantoms:=fun hq=>phantom_off _ hq (by simp)
 have hzE:∀q∈pad,(erase s).basis q=false:=by
  intro q hq
  exact (bit_same s q (fun bad=>hpad q bad hq)).trans (hz q hq)
 have hbE:∀q∈bank,(erase s).basis q=false:=by
  intro q hq
  exact (bit_same s q (fun bad=>hbank q bad hq)).trans (hb q hq)
 have hiE:(erase s).basis L.core.cin=false:=(bit_same s _ hcin).trans hi
 have zs:∀q∈spares,s.basis q=false:=fun q hq=>zero q (by simp only [Ghost3CacheC.hosts,List.mem_append];exact Or.inr hq)
 have haE:regValue viewAcc (erase s).basis=0:=(reg_view s zs).trans ha
 have zeroE:∀h∈Ghost3CacheC.hosts,(erase s).basis h=false:=by
  intro h hh
  exact (bit_same s h (fun bad=>hv h bad hh)).trans (zero h hh)
 let u:=middleState (ReorderedCPlain.build ga pad bank L.core.cin src) middle s m
 have uz:∀q∈spares,u.basis q=false:=by
  intro q hq
  unfold u middleState
  exact (run_preserves_outside _ _ _ q (spare_off_middle q hq)).trans
   ((run_preserves_outside _ _ _ q (spare_off_build q hq)).trans (zs q hq))
 have me:middleState (ReorderedCPlain.build viewAcc pad bank L.core.cin src) middle (erase s) m=erase u:=by
  rw [plainBuild_eq]
  unfold middleState u
  rw [run_erase _ _ _ phantom_off_plain_build,run_erase _ _ _ phantom_off_middle]
  rfl
 have sourceE:=reg_same src s hsrc
 have goodE:WReady viewAcc pad bank L.core.cin src (regValue src (erase s).basis)
  (middleState (ReorderedCPlain.build viewAcc pad bank L.core.cin src) middle (erase s) m):=by
  rw [sourceE,me]
  exact ready_view _ u uz good
 have offF:∀h∈Ghost3CacheC.hosts,h∉wires (ReorderedCPlain.build viewAcc pad bank L.core.cin src):=by
  rw [plainBuild_eq]
  exact fun h hh=>(host_off_plain h hh).1
 have offI:∀h∈Ghost3CacheC.hosts,h∉wires (ReorderedCPlain.unbuild viewAcc pad bank L.core.cin src):=by
  rw [plainUnbuild_eq]
  exact fun h hh=>(host_off_plain h hh).2.1
 have eq:=ReorderedCLoop.loop_eq 102 viewAcc pad bank L.core.cin src Ghost3CacheC.hosts middle
  geometry.2.2.1 lengths.2.2.2 fitsView (erase s) m hzE hbE hiE haE (by decide)
  geometry.1 geometry.2.1 geometry.2.2.2 offF offI (fun h hh=>(host_off_plain h hh).2.2) zeroE goodE
 rw [build_view,unbuild_view,plainBuild_eq,plainUnbuild_eq] at eq
 have leftOff:∀q∈phantoms,q∉wires (build++middle++unbuild):=by
  intro q hq
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨⟨phantom_off_build q hq,phantom_off_middle q hq⟩,phantom_off_unbuild q hq⟩
 have rightOff:∀q∈phantoms,q∉wires (ReorderedCPlain.build ga pad bank L.core.cin src++middle++
  ReorderedCPlain.unbuild ga pad bank L.core.cin src):=by
  intro q hq
  simp only [wires_append,Finset.mem_union,not_or]
  exact ⟨⟨phantom_off_plain_build q hq,phantom_off_middle q hq⟩,phantom_off_plain_unbuild q hq⟩
 rw [run_erase _ _ _ leftOff,run_erase _ _ _ rightOff] at eq
 apply erase_eq_implies
 · intro q hq
   exact (run_preserves_outside _ m s q (leftOff q hq)).trans
    (run_preserves_outside _ m s q (rightOff q hq)).symm
 · exact eq
#print axioms loop_eq
end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCMiddleFrames
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic ReorderedCFixed C163Low4Middle InverseCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires A161Low4FixedFold.checked C163Low4Middle.bankChecked

theorem plain_ready(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)(ha:regValue ga s.basis=0):
 WReady ga pad bank L.core.cin src (regValue src s.basis) (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s):=by
 have f:=ReorderedCPlain.build_triple ga pad bank L.core.cin src lengths.1 lengths.2.2.2 fits s.basis hz hb hi s m ⟨ha,fun _ _=>rfl⟩
 have away:∀q∈src++pad++bank++[L.core.cin],q∉ga:=by decide +kernel
 refine ⟨f.2.1,?_,?_,?_,?_⟩
 · exact regValue_congr _ _ _ (fun q hq=>f.2.2 q (away q (by simp [hq])))
 · intro q hq
   exact (f.2.2 q (away q (by simp [hq]))).trans (hz q hq)
 · intro q hq
   exact (f.2.2 q (away q (by simp [hq]))).trans (hb q hq)
 · exact (f.2.2 _ (away _ (by simp))).trans hi

theorem relocated_middle_counts:
 measurementCount GhostRelocatedKnown.C.program=measurementCount C163Low4Middle.bankChecked.out:=
 GhostRelocatedKnown.C.counts.2.trans (KnownSparseFold.Cert.counts _ _ _ _ _ KnownCMidStaged.cert).2

theorem relocated_middle_eq(H:Nat)(s:State)(m:List Bool)
 (before:WReady ga pad bank L.core.cin src H s)
 (after:WReady ga pad bank L.core.cin src H (run C163Low4Middle.bankChecked.out m s)):
 run GhostRelocatedKnown.C.program m s=run C163Low4Middle.bankChecked.out m s:=by
 have z:KnownSparseFold.Zero KnownCMidStaged.known0 s:=by
  intro u hu
  rcases ReorderedKnownC.guard u hu with ⟨_,_,hb⟩
  exact hb.elim (fun h=>before.2.2.2.1 u h) (fun h=>h.symm ▸ before.2.2.2.2)
 have km:run KnownCMidStaged.body m s=run C163Low4Middle.bankChecked.out m s:=(KnownSparseFold.Cert.correct _ _ _ _ _ KnownCMidStaged.cert s m z).1
 have good:WReady ga pad bank L.core.cin src H (run KnownCMidStaged.body m s):=by rw [km];exact after
 exact (GhostRelocatedKnown.C.equivalent H s m before good).trans km

theorem relocated_middleState_eq(s:State)(m:List Bool)
 (hz:∀q∈pad,s.basis q=false)(hb:∀q∈bank,s.basis q=false)(hi:s.basis L.core.cin=false)(ha:regValue ga s.basis=0)
 (after:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) C163Low4Middle.bankChecked.out s m)):
 middleState (ReorderedCPlain.build ga pad bank L.core.cin src) GhostRelocatedKnown.C.program s m=
 middleState (ReorderedCPlain.build ga pad bank L.core.cin src) C163Low4Middle.bankChecked.out s m:=by
 unfold middleState
 rw [relocated_middle_counts]
 apply relocated_middle_eq (regValue src s.basis) _ _ ?_ after
 exact plain_ready s _ hz hb hi ha
#print axioms relocated_middleState_eq
end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3CacheCFrame
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CacheC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle
 InverseCarryDevelop ThirdSavedCarryDevelop ManyACarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires C163Low4Middle.bankChecked C163Low4Middle.specialChecked
abbrev p:=C163Low4Middle.p
theorem frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
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
 have zero:∀u∈Ghost3CacheC.hosts,s.basis u=false:=by
  intro u hu
  simp only [Ghost3CacheC.hosts,List.mem_append] at hu
  rcases hu with old|extra
  · exact zeroOld u old
  · exact (regValue_zero ga s.basis).mp ha u (spare_mem u extra)
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
 have changed:=relocated_middleState_eq s m hz hb clean.cin ha goodBank
 have goodNew:WReady ga pad bank L.core.cin src (regValue src s.basis)
  (middleState (ReorderedCPlain.build ga pad bank L.core.cin src) middle s m):=by
  rw [changed]
  exact goodBank
 have cachedNew:=Ghost3CacheC.loop_eq s m hz hb clean.cin ha zero goodNew
 have midEq:run middle (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s)=
  run bankChecked.out (m.drop (measurementCount (ReorderedCPlain.build ga pad bank L.core.cin src)))
  (run (ReorderedCPlain.build ga pad bank L.core.cin src) m s):=by
  simpa only [middleState,run_take] using changed
 have ctxt:=ReorderedKnownC.context_eq
  (ReorderedCPlain.build ga pad bank L.core.cin src) bankChecked.out middle
  (ReorderedCPlain.unbuild ga pad bank L.core.cin src) s m relocated_middle_counts midEq
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
 have finalEq:run loop m s=run (C163NarrowAcc.build8 ga pad bank L.core.cin src++specialChecked.out++
  C163SourceAdd.unbuild ga pad bank L.core.cin src) record s:=cacheEq.trans (middleReplace.trans plainEq)
 exact transport (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)) s _ _ finalEq oldFrame


#print axioms frame
end ECDSAAdd.Entrant.Ghost3CacheC

end

-- Verified component Ghost3KnownC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3KnownC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev p:=C163Low4Middle.p
abbrev hosts:=Ghost3CacheC.hosts
abbrev loop:=Ghost3CacheC.loop
abbrev frame:=Ghost3CacheC.frame
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

def body:Program:=rawBody++ReorderedRecordPadding.program 4 L.core.cin

theorem body_frame(base:BasisState)(M:Nat)(pv:regValue L.core.product base=M^2)
 (clean:L.PairClean base)(disabled:base g=false→M=0)(hd:base d=false)(O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) body
  (SquareFrame L.core.out base (C163Low4Body.resCFK C163Low4Facts.Klow (base g) (M^2) O)):=by
 intro s m hf
 have f:=raw_body_frame base M pv clean disabled hd O hO s (m.take (measurementCount rawBody)) hf
 have hz:(run rawBody (m.take (measurementCount rawBody)) s).basis L.core.cin=false:=
  (f.2.2 L.core.cin (by decide)).trans clean.cin
 have eq:run body m s=run rawBody (m.take (measurementCount rawBody)) s:=by
  rw [body,run_append,ReorderedRecordPadding.run_zero 4 L.core.cin _ _ hz]
 exact ReorderedCFixed.transport _ s _ _ eq f

#print axioms body_frame
end ECDSAAdd.Entrant.Ghost3KnownC

end

-- Verified component Ghost3SignC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3SignC
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle C163Low4Ghost
 ControlLoan1589BFFold InverseCarryDevelop ThirdSavedCarryDevelop
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
abbrev hosts:=Ghost3CacheC.hosts
abbrev p:=C163Low4Middle.p

def suffix:Program:=ReorderedGenericCache.cachedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin++
 C163Carry.buildPost ga pad bank L.core.cin src++Ghost3CacheC.middle++
 ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts

def loop:Program:=SignCHead.head++suffix

theorem loop_eq(base:BasisState)(hc:L.PairClean base)(O:Nat)(hO:O<SquareReduction.p)
 (s:State)(m:List Bool)(hf:SquareFrame L.core.out base O s.basis):
 run loop m s=run Ghost3KnownC.loop
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
 simpa only [loop,suffix,Ghost3KnownC.loop,Ghost3CacheC.loop,Ghost3CacheC.build,Ghost3CacheC.unbuild,Ghost3KnownC.hosts,ReorderedCBuild.build,List.append_assoc] using eq

theorem frame(base:BasisState)(hc:L.PairClean base)(hp:base p=false)(hd:base d=false)
 (O:Nat)(hO:O<SquareReduction.p):
 Triple (SquareFrame L.core.out base O) loop
  (SquareFrame L.core.out base
   (((if base g then C163Low4Facts.Klow-C163Fold.payload L base else C163Fold.payload L base)+
    (SquareReduction.p-1-O))%SquareReduction.p)):=by
 intro s m hf
 have e:=loop_eq base hc O hO s m hf
 have old:=Ghost3KnownC.frame base hc hp hd O hO s (SignRetape.tape SignCHead.head (ReorderedCHead.head ga pad bank L.core.cin src) m) hf
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
end ECDSAAdd.Entrant.Ghost3SignC

end

-- Verified component Ghost3CCounts
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CCounts
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle ControlLoan1589BFFold
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount
abbrev hosts:=Ghost3CacheC.hosts

theorem cache_counts:
 toffoliCount (ReorderedGenericCache.cachedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129 ∧
 measurementCount (ReorderedGenericCache.cachedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129 ∧
 toffoliCount (ReorderedGenericCache.consumedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=27 ∧
 measurementCount (ReorderedGenericCache.consumedAdd 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin)=129:=by
 have old:=addInPlace_counts src ((ga.take 140).drop 10) (bank.take 129) L.core.cin (by decide) (by decide)
 rw [←MixedLiteralAdderDevelop.read_add_eq] at old
 have bal:=ReorderedGenericCache.count_balance 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide)
 change toffoliCount (mappedAdd (mappedRead src false) ((ga.take 140).drop 10) (bank.take 129) L.core.cin)=129 ∧
  measurementCount (mappedAdd (mappedRead src false) ((ga.take 140).drop 10) (bank.take 129) L.core.cin)=129 at old
 omega

theorem pieces:
 toffoliCount (ReorderedCBuild.build 102 ga pad bank L.core.cin src hosts)=392 ∧
 measurementCount (ReorderedCBuild.build 102 ga pad bank L.core.cin src hosts)=392 ∧
 toffoliCount (ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts)=134 ∧
 measurementCount (ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts)=392:=by
 have f6:=Acc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide)
 have f32:=Acc.fits_prefix ga pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide)
 have seed:=Acc.seed_counts ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
  lengths.1 (fits _ (C163NarrowAcc.terms_mem src).1).toFitsLen
 have sub:=Acc.op_counts (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6) (by decide) f6.toFitsLen
 have top:=Acc.op_counts (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen
 have preInv:=CodexNarrowTailResource.accSub_counts 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32)
  (by decide) f32.toFitsLen (by decide)
 have tail:=ReorderedKnownTail.counts src pad ((ga.take 140).drop 6) (bank.take 133) L.core.cin
  (by decide) (by decide) (by decide) (by decide)
 have notC:=notRegister_counts ((ga.take 140).drop 10)
 have cache:=cache_counts
 change toffoliCount (ReorderedCTail.tail ga pad bank L.core.cin src)=0 ∧
  measurementCount (ReorderedCTail.tail ga pad bank L.core.cin src)=133 at tail
 change toffoliCount (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))=133 ∧
  measurementCount (Acc.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6))=133 at sub
 change toffoliCount (Acc.op (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32))=130 ∧
  measurementCount (Acc.op (ga.take 163) pad bank L.core.cin 163 false (Acc.earlyTerm src false 32))=130 at top
 change toffoliCount (CodexKnownOnesTail.accSub 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32))=107 ∧
  measurementCount (CodexKnownOnesTail.accSub 108 (ga.take 163) pad bank L.core.cin 163 (Acc.earlyTerm src false 32))=130 at preInv
 simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,
  ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,ReorderedConsumedSub.consumed,C163Carry.unbuildPre,
  toffoliCount_append,measurementCount_append]
 omega


end ECDSAAdd.Entrant.Ghost3CCounts

end

-- Verified component Ghost3CPhysical
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CPhysical
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.wires specialChecked bankChecked
abbrev hosts:=Ghost3CacheC.hosts

theorem body_physical:GatePhysical Ghost3KnownC.body:=by
 have f6:=ReorderedAcc.fits_prefix ga pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) (by decide)
 have subP:=ReorderedPhysical.op (ga.take 140) pad bank L.core.cin 140 true (Acc.earlyTerm src true 6) f6
 have seedP:GatePhysical (Acc.seedOp ga pad 163 (Acc.earlyTerm src false 4)):=by
  have nd:=Acc.fits_nodup ga pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
   (fits _ (C163NarrowAcc.terms_mem src).1)
  exact copyRegister_physical none _ _
   ((List.nodup_cons.mp nd).2.sublist (List.sublist_append_left _ _)) (by simp)
 have topP:=Acc.op_prefix_physical ga pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fits _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide) false
 have nd:(L.core.cin::(src++(ga.take 140).drop 10++bank.take 129)).Nodup:=by decide +kernel
 have cacheP:=ReorderedPhysical.cached 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide) nd (by
   intro h hh bad
   exact (by decide +kernel : ∀h∈hosts,h∉bank) h hh (List.mem_of_mem_take bad))
 have buildP:GatePhysical (ReorderedCBuild.build 102 ga pad bank L.core.cin src hosts):=by
  simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,gatePhysical_append]
  exact ⟨⟨⟨seedP,subP⟩,cacheP.1⟩,topP⟩
 have notP:=notRegister_physical ((ga.take 140).drop 10)
 have inverseP:GatePhysical (ReorderedConsumedSub.consumed 102 src ((ga.take 140).drop 10) (bank.take 129) hosts L.core.cin):=by
  simp only [ReorderedConsumedSub.consumed,gatePhysical_append]
  exact ⟨⟨notP,cacheP.2⟩,notP⟩
 have tailP:GatePhysical (ReorderedCTail.tail ga pad bank L.core.cin src):=by
  apply KnownOutputAdder.program_physical (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
   ((ga.take 140).drop 6) (bank.take 133) L.core.cin
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
 have oldInv:=C163SourceAdd.unbuild_physical ga pad bank L.core.cin src lengths.1 lengths.2.2.2 fits
 simp only [C163SourceAdd.unbuild,gatePhysical_append] at oldInv
 have preInv:GatePhysical (C163Carry.unbuildPre ga pad bank L.core.cin src):=oldInv.1.1.1
 have unbuildP:GatePhysical (ReorderedCUnbuild.unbuild 102 ga pad bank L.core.cin src hosts):=by
  simp only [ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,gatePhysical_append]
  exact ⟨⟨preInv,inverseP⟩,⟨tailP,seedP⟩⟩
 have old:=C163Low4Middle.body_physical
 simp only [C163Low4Middle.body,C163Low4Body.bodyProgram,C163Low4Middle.loop,gatePhysical_append] at old
 have midOld:GatePhysical KnownCMidStaged.body:=by
  unfold GatePhysical
  intro i hi
  exact old.2.1.2 i ((KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert).subset hi)
 have midP:GatePhysical Ghost3CacheC.middle:=
  RelocateResources.physical GhostRelocatedKnown.ports GhostRelocatedKnown.ports_inj KnownCMidStaged.body midOld
 simp only [Ghost3KnownC.body,Ghost3KnownC.rawBody,C163Low4Body.bodyProgram,Ghost3KnownC.loop,Ghost3CacheC.loop,Ghost3CacheC.build,Ghost3CacheC.unbuild,gatePhysical_append]
 exact ⟨⟨old.1,⟨⟨buildP,midP⟩,unbuildP⟩⟩,ReorderedPhysical.padding 4 L.core.cin⟩

#print axioms body_physical

end ECDSAAdd.Entrant.Ghost3CPhysical

end

-- Verified component Ghost3CBalance
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CBalance
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ReorderedCFixed C163Low4Middle Challenge
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount Challenge.gateSlots

theorem counts:toffoliCount Ghost3SignC.body+3=toffoliCount SignKnownC.body ∧
 measurementCount Ghost3SignC.body=measurementCount SignKnownC.body:=by
 have nc:=Ghost3CCounts.cache_counts
 have oc:=ReorderedCCounts.cache_counts
 have np:=Ghost3CCounts.pieces
 have op:=ReorderedCCounts.pieces
 have mid:=GhostRelocatedKnown.C.counts
 change toffoliCount GhostRelocatedKnown.C.program=toffoliCount KnownCMidStaged.body ∧
  measurementCount GhostRelocatedKnown.C.program=measurementCount KnownCMidStaged.body at mid
 simp only [Ghost3CCounts.hosts] at nc np
 simp only [ReorderedCCounts.hosts] at oc op
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,C163Low4Body.bodyProgram,Ghost3SignC.loop,Ghost3SignC.suffix,Ghost3SignC.hosts,Ghost3CacheC.middle,
  SignKnownC.body,SignKnownC.rawBody,SignKnownC.loop,SignKnownC.suffix,toffoliCount_append,measurementCount_append]
 exact ⟨by omega,by omega⟩

theorem slots:gateSlots Ghost3SignC.body+1=gateSlots SignKnownC.body:=by
 have nc:=ReorderedSlots.cache 102 src ((ga.take 140).drop 10) (bank.take 129) Ghost3CacheC.hosts L.core.cin
  (by decide) (by decide) (by decide) Ghost3CacheC.geometry.2.1
 have oc:=ReorderedSlots.cache 99 src ((ga.take 140).drop 10) (bank.take 129) ReorderedCFixed.hosts L.core.cin
  (by decide) (by decide) (by decide) ReorderedCFixed.host_geometry.2.1
 have mid:=RelocateResources.slots GhostRelocatedKnown.ports KnownCMidStaged.body
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,C163Low4Body.bodyProgram,Ghost3SignC.loop,Ghost3SignC.suffix,Ghost3SignC.hosts,Ghost3CacheC.middle,
  SignKnownC.body,SignKnownC.rawBody,SignKnownC.loop,SignKnownC.suffix,
  ReorderedCUnbuild.unbuild,ReorderedConsumedSub.consumed,gateSlots_append]
 change gateSlots GhostRelocatedKnown.C.program=gateSlots KnownCMidStaged.body+8 at mid
 omega

end ECDSAAdd.Entrant.Ghost3CBalance

end

-- Verified component SignedBodySupportC
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3BodyResources
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout Challenge
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.wires Challenge.gateSlots List.toFinset

open ReorderedCFixed C163Low4Middle in
theorem c_support:wires Ghost3SignC.body⊆wires Ghost3KnownC.body:=by
 have loop:wires Ghost3SignC.loop⊆wires Ghost3KnownC.loop:=by
  have eq:Ghost3KnownC.loop=ReorderedCHead.head ga pad bank L.core.cin src++Ghost3SignC.suffix:=by
   simp only [Ghost3KnownC.loop,Ghost3CacheC.loop,Ghost3CacheC.build,Ghost3CacheC.unbuild,ReorderedCBuild.build,Ghost3KnownC.hosts,Ghost3SignC.suffix,Ghost3SignC.hosts,List.append_assoc]
  rw [Ghost3SignC.loop,eq,wires_append,wires_append]
  exact Finset.union_subset_union SignCHeadSupport.support (Finset.Subset.refl _)
 have pad:wires (ReorderedRecordPadding.program 7 L.core.cin)=wires (ReorderedRecordPadding.program 4 L.core.cin):=by
  simp [ReorderedRecordPadding.program,List.replicate_succ,wires,Instr.wires,correctionWires]
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,C163Low4Body.bodyProgram,Ghost3KnownC.body,Ghost3KnownC.rawBody,wires_append]
 rw [pad]
 repeat' first
  | exact loop
  | exact Finset.Subset.refl _
  | apply Finset.union_subset_union

open ReorderedCFixed C163Low4Middle in
theorem c_physical:GatePhysical Ghost3SignC.body:=by
 have old:=Ghost3CPhysical.body_physical
 have head:=SignCHeadResources.physical
 have pad:=ReorderedPhysical.padding 7 L.core.cin
 simp only [Ghost3SignC.body,Ghost3SignC.rawBody,Ghost3SignC.loop,Ghost3SignC.suffix,Ghost3SignC.hosts,
  Ghost3KnownC.body,Ghost3KnownC.rawBody,C163Low4Body.bodyProgram,Ghost3KnownC.loop,Ghost3CacheC.loop,Ghost3CacheC.build,Ghost3CacheC.unbuild,Ghost3KnownC.hosts,
  ReorderedCBuild.build,gatePhysical_append] at old ⊢
 tauto

end ECDSAAdd.Entrant.Ghost3BodyResources

end

-- Verified component Ghost3CFine
section
open ECDSAAdd ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Ghost3CFine
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout InverseCarryDevelop ThirdSavedCarryDevelop
 ManyACarryDevelop C163Low4Middle OwnDiagAll12Square
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
attribute [local irreducible] RelocateThreeGhosts.program
attribute [local irreducible] ECDSAAdd.wires specialChecked bankChecked List.toFinset
abbrev hosts:=Ghost3CacheC.hosts
def domain:Finset Wire:=(L.core.cin::(src++acc++pad++bank)).toFinset

theorem list_support(A B:List Wire)(h:∀q∈A,q∈B):A.toFinset⊆B.toFinset:=by
 intro q hq
 exact List.mem_toFinset.mpr (h q (List.mem_toFinset.mp hq))

theorem domain_in:domain⊆C163Middle.ambient.toFinset:=
 list_support (L.core.cin::(src++acc++pad++bank)) C163Middle.ambient (by decide +kernel)

theorem loop_support:wires Ghost3KnownC.loop⊆C163Middle.ambient.toFinset:=by
 have fit:=C163Fold.terms_fits L hw hn
 have len:=C163Fold.lengths L hw
 have seed:=(Acc.seed_support acc pad bank L.core.cin 163 (Acc.earlyTerm src false 4)
  len.1 (fit _ (C163NarrowAcc.terms_mem src).1)).trans domain_in
 have sub:=(Acc.op_prefix_support acc pad bank L.core.cin 163 140 (Acc.earlyTerm src true 6)
  len.1 (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.1) (by decide) true).trans domain_in
 have top(neg:Bool):wires (Acc.op (acc.take 163) pad bank L.core.cin 163 neg (Acc.earlyTerm src false 32))⊆C163Middle.ambient.toFinset:=
  (Acc.op_prefix_support acc pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
   len.1 (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide) neg).trans domain_in
 have cacheDomain:(L.core.cin::(src++(acc.take 140).drop 10++bank.take 129)).toFinset∪hosts.toFinset⊆
  C163Middle.ambient.toFinset:=Finset.union_subset
   (list_support _ _ (by decide +kernel)) (list_support _ _ (by decide +kernel))
 have cached:=ReorderedSupport.cached 102 src ((acc.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide) (by decide) (by decide)
 have build:wires (ReorderedCBuild.build 102 acc pad bank L.core.cin src hosts)⊆C163Middle.ambient.toFinset:=by
  simp only [ReorderedCBuild.build,ReorderedCHead.head,C163Carry.buildPost,wires_append]
  exact Finset.union_subset (Finset.union_subset (Finset.union_subset seed sub) (cached.1.trans cacheDomain)) (top false)
 have f32:=Acc.fits_prefix acc pad bank L.core.cin 163 163 (Acc.earlyTerm src false 32)
  (by decide) (fit _ (C163NarrowAcc.terms_mem src).2.2.2) (by decide)
 have preInv:wires (C163Carry.unbuildPre acc pad bank L.core.cin src)⊆C163Middle.ambient.toFinset:=
  (CodexNarrowTailResource.accSub_support 108 (acc.take 163) pad bank L.core.cin 163
   (Acc.earlyTerm src false 32) (by decide) f32.toFitsLen (by decide)).trans (top true)
 have consumed:=(ReorderedSupport.consumed 102 src ((acc.take 140).drop 10) (bank.take 129) hosts L.core.cin
  (by decide) (by decide) (by decide) (by decide) (by decide)).trans cacheDomain
 have tail:=KnownOutputAdder.program_support (mappedRead (src++pad.take 4) false) (ReorderedKnownTail.desired src)
  ((acc.take 140).drop 6) (bank.take 133) L.core.cin
 rw [mappedRead_wires,ReorderedKnownTail.desired_wires] at tail
 have tailDomain:((src++pad.take 4)++src.drop 2++(acc.take 140).drop 6++bank.take 133++[L.core.cin]).toFinset⊆
  C163Middle.ambient.toFinset:=list_support _ _ (by decide +kernel)
 have unbuild:wires (ReorderedCUnbuild.unbuild 102 acc pad bank L.core.cin src hosts)⊆C163Middle.ambient.toFinset:=by
  simp only [ReorderedCUnbuild.unbuild,ReorderedCUnbuild.after,wires_append]
  exact Finset.union_subset (Finset.union_subset preInv consumed) (Finset.union_subset (tail.trans tailDomain) seed)
 have midOld:wires KnownCMidStaged.body⊆C163Middle.ambient.toFinset:=
  (Skip4.wires_mono_of_mem _ _ (fun _ hi=>(KnownSparseFold.Cert.sublist _ _ _ _ _ KnownCMidStaged.cert).subset hi)).trans
   (ReorderedBankSupport.subset.trans
    ((special_cert.support [q,r] middle specialChecked.out).1.trans
     (middle_subset.trans C163Middle.middle_support)))
 have mid:wires Ghost3CacheC.middle⊆C163Middle.ambient.toFinset:=
  RelocateResources.support GhostRelocatedKnown.ports KnownCMidStaged.body _ midOld
   (by intro i;apply List.mem_toFinset.mpr;fin_cases i <;>decide +kernel)
 simp only [Ghost3KnownC.loop,Ghost3CacheC.loop,wires_append]
 rw [Ghost3CacheC.build,Ghost3CacheC.unbuild,ReorderedCStructural.build_eq,ReorderedCStructural.unbuild_eq]
 exact Finset.union_subset (Finset.union_subset build mid) unbuild

theorem padding_support:wires (ReorderedRecordPadding.program 4 L.core.cin)⊆C163Middle.ambient.toFinset:=by
 have sub:wires (ReorderedRecordPadding.program 4 L.core.cin)⊆[L.core.cin].toFinset:=by decide +kernel
 exact sub.trans (list_support _ _ (by decide +kernel))

theorem body_fine:wires Ghost3KnownC.body⊆insert d (wires (bodyCKTq L g)):=by
 intro u hu
 simp only [Ghost3KnownC.body,Ghost3KnownC.rawBody,C163Low4Body.bodyProgram,wires_append,Finset.mem_union] at hu
 rcases hu with (hu|hu)|hu
 · apply Finset.mem_insert_of_mem
   simp only [bodyCKTq,wires_append,Finset.mem_union]
   exact Or.inl hu
 · exact C163FineFast.ambient_fine (loop_support hu)
 · exact C163FineFast.ambient_fine (padding_support hu)

theorem body_coarse:wires Ghost3KnownC.body⊆insert d (g::L.wires).toFinset:=
 body_fine.trans (Finset.insert_subset_insert d (bodyCK_supportTq L hw hn g))

#print axioms body_fine
end ECDSAAdd.Entrant.Ghost3CFine

end

end
