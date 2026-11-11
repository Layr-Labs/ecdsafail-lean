import ECDSAAdd.Submission.Entrant.LowAccMiddleLiteral

namespace ECDSAAdd.Entrant.LowAccIdentityTransfer
open Arithmetic ManyACarryDevelop ZeroSetDevelop B84WindowResearch
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run B84CachedBlockResearch.headPart compileS?

def Q : List Wire := [4501,4502,4503,4504]

def literalHead : Program := (B84PostLiteralResearch.postLiteral++FullPadBData.p5).take 9124

theorem literalHead_eq : literalHead=B84CachedBlockResearch.headPart := by
 unfold literalHead B84CachedBlockResearch.headPart B84CachedBlockResearch.original
 exact congrArg (fun p=>(p++FullPadBData.p5).take 9124) B84PostLiteralResearch.post_eq.symm

theorem literalHead_condition (s : State) (m : List Bool) : query (run literalHead m s).basis=false := by
 rw [literalHead_eq]
 exact B84CachedBlockResearch.prefix_condition s m

theorem query_scatter (s : State) (vs : List Bool) :
 query (scatterState Q vs s).basis=query s.basis := by
 simp only [query]
 rw [scatter_outside Q vs s 4660 (by decide),scatter_outside Q vs s 4403 (by decide),
  scatter_outside Q vs s 4339 (by decide),scatter_outside Q vs s 4370 (by decide),
  scatter_outside Q vs s 4629 (by decide),scatter_outside Q vs s 4661 (by decide),
  scatter_outside Q vs s 4760 (by decide)]

theorem condition_of_rewrite (cm : CheckedS Q literalHead)
 (s : State) (m : List Bool) : query (run cm.out m s).basis=false := by
 let vs:=List.replicate Q.length false
 let z:=scatterState Q vs s
 have hz : ∀q∈Q,z.basis q=false :=
  scatter_zero_mem Q s (by decide)
 have eq:=cm.proof.run_eq Q literalHead cm.out z m hz
 have old:=literalHead_condition z m
 have hn : query (run cm.out m z).basis=false := by rw [eq];exact old
 have off:=cm.proof.support Q literalHead cm.out
 have comm:=run_scatter cm.out Q vs s m off.2
 change query (run cm.out m (scatterState Q vs s)).basis=false at hn
 rw [comm,query_scatter] at hn
 exact hn


def compiledHead : Program := ((compileS? Q literalHead).map (fun cm=>cm.out)).getD []
theorem head_success : (compileS? Q literalHead).isSome=true := by decide +kernel

theorem compiled_condition (s : State) (m : List Bool) : query (run compiledHead m s).basis=false := by
 cases h : compileS? Q literalHead with
 | none => have bad:=head_success;simp only [h,Option.isSome_none,Bool.false_eq_true] at bad
 | some cm => simpa only [compiledHead,h,Option.map_some,Option.getD_some] using condition_of_rewrite cm s m

def hosts88 : List Wire := [4672, 4673, 4674, 4675, 4676, 4677, 4678, 4679, 4680, 4681, 4682, 4683, 4684, 4685, 4686, 4687, 4688, 4689, 4690, 4691, 4692, 4694, 4695, 4696, 4756, 4728, 4729, 4730, 4731, 4732, 4733, 4734, 4735, 4736, 4737, 4738, 4739, 4740, 4741, 4742, 4743, 4744, 4745, 4746, 4747, 4748, 4749, 4750, 4751, 4752, 4753, 4754, 4755, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4712, 4714, 4715, 4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4713, 4697, 4698, 4699, 4700, 4701, 4501, 4502, 4503, 4504]
def actualOut : Program := ((compileS? hosts88 BData301.p0).map (fun cm=>cm.out)).getD []
def actualHead : Program := (B84PostLiteralResearch.actualPost++actualOut).take 9080

theorem hosts_eq : hosts88=LowAccCarryDevelop.hosts88 := by decide +kernel

theorem actual_out_eq_literal : actualOut=LowAccMiddleLiteral.output := by
 unfold actualOut
 rw [hosts_eq]
 exact LowAccMiddleLiteral.compiler_output_eq
 theorem actualHead_eq : actualHead=compiledHead := by
 apply ParkAProgramBool.programEq_sound
 unfold actualHead compiledHead
 rw [actual_out_eq_literal]
 unfold literalHead
 rw [B84PostLiteralResearch.post_eq]
 decide +kernel
 theorem actual_condition (s : State) (m : List Bool) : query (run actualHead m s).basis=false := by
 rw [actualHead_eq];exact compiled_condition s m
end ECDSAAdd.Entrant.LowAccIdentityTransfer

namespace ECDSAAdd.Entrant.B89ContextTransfer
open Arithmetic
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots

structure CheckedReplacement (old new : Program) : Prop where
 run_eq : ∀s m,run new m s=run old m s
 toffoli : toffoliCount new+1=toffoliCount old
 measurements : measurementCount new=measurementCount old
 slots : Challenge.gateSlots new=Challenge.gateSlots old+4
 support : wires new⊆wires old
 physical : GatePhysical old→GatePhysical new

theorem of_context (old new pre mid replacement post : Program)
 (oldShape : old=pre++(mid++post)) (newShape : new=pre++(replacement++post))
 (checked : CheckedReplacement mid replacement) : CheckedReplacement old new := by
 refine ⟨?_,?_,?_,?_,?_,?_⟩
 · intro s m
   rw [newShape,oldShape]
   exact (B84ContextResearch.replace_context mid replacement
    (fun s m=>(checked.run_eq s m).symm) checked.measurements.symm pre post s m).symm
 · rw [newShape,oldShape]
   exact B84ContextResearch.context_one_less mid replacement checked.toffoli pre post
 · rw [newShape,oldShape]
   exact (B84ContextResearch.context_measurements mid replacement checked.measurements.symm pre post).symm
 · rw [newShape,oldShape]
   exact B84ContextResearch.context_slots mid replacement checked.slots pre post
 · rw [newShape,oldShape]
   exact B84SupportResearch.context_support mid replacement checked.support pre post
 · intro hp
   rw [oldShape] at hp
   rw [newShape]
   simp only [gatePhysical_append] at hp ⊢
   exact ⟨hp.1,checked.physical hp.2.1,hp.2.2⟩
end ECDSAAdd.Entrant.B89ContextTransfer

namespace ECDSAAdd.Entrant.B89BlockDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
open InverseCarryDevelop ThirdSavedCarryDevelop FourthASavedCarryDevelop ManyACarryDevelop
open B84ReplacementResearch B84WindowResearch
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] FullBTemp.middle BData301.p0
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ZeroSetDevelop.compileS?
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots
abbrev L := LowAccCarryDevelop.L
abbrev c := LowAccCarryDevelop.c
abbrev ga := LowAccCarryDevelop.ga

def output : Program := ((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map (fun cm=>cm.out)).getD []

theorem output_eq_literal : output=LowAccMiddleLiteral.output := by
 unfold output
 exact LowAccMiddleLiteral.compiler_output_eq
def block : Program := B84PostLiteralResearch.actualPost++output
def head : Program := block.take 9080
def tail : Program := block.drop 9081
def optimizedBlock : Program := head++(repair++tail)

theorem hosts_eq : LowAccIdentityTransfer.hosts88=LowAccCarryDevelop.hosts88 := by decide +kernel

theorem head_eq : head=LowAccIdentityTransfer.actualHead := by
 unfold head block output LowAccIdentityTransfer.actualHead LowAccIdentityTransfer.actualOut
 rw [hosts_eq]

theorem condition (s : State) (m : List Bool) : query (run head m s).basis=false := by
 rw [head_eq]
 exact LowAccIdentityTransfer.actual_condition s m

theorem gate_lookup : block[9080]?=some (.CCX 4660 4403 4404) := by
 unfold block
 rw [output_eq_literal,B84PostLiteralResearch.post_eq]
 decide +kernel

attribute [local irreducible] block output head tail

theorem shape : block=head++([.CCX 4660 4403 4404]++tail) := by
 simpa only [head,tail] using
  B84ReplaceGenericResearch.old_shape_of_lookup block 9080 (.CCX 4660 4403 4404) gate_lookup

theorem run_eq (s : State) (m : List Bool) : run block m s=run optimizedBlock m s :=
 (congrArg (fun p=>run p m s) shape).trans (B84ReplaceGenericResearch.after_prefix head tail condition s m)

theorem toffoli_transport (old new pre post : Program)
 (oldShape : old=pre++([.CCX 4660 4403 4404]++post))
 (newShape : new=pre++(repair++post)) : toffoliCount new+1=toffoliCount old := by
 rw [oldShape,newShape]
 exact B84ResourceResearch.one_less_toffoli pre post

theorem toffoli : toffoliCount optimizedBlock+1=toffoliCount block :=
 toffoli_transport block optimizedBlock head tail shape rfl

theorem measurements : measurementCount optimizedBlock=measurementCount block :=
 (B84ResourceResearch.same_measurements head tail).trans (congrArg measurementCount shape.symm)

theorem slots : Challenge.gateSlots optimizedBlock=Challenge.gateSlots block+4 :=
 (B84ResourceResearch.four_more_slots head tail).trans (congrArg (fun p=>Challenge.gateSlots p+4) shape.symm)

theorem repair_in_block : wires repair⊆wires block := by
 have postSub : wires B84PostLiteralResearch.actualPost⊆wires block := by
  unfold block
  rw [wires_append]
  exact Finset.subset_union_left
 intro q hq
 rw [B84RepairSupportResearch.repair_wires] at hq
 simp only [Finset.mem_insert,Finset.mem_singleton] at hq
 rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
 all_goals
  apply postSub
  apply (hasWire_iff B84PostLiteralResearch.actualPost _).mp
  rw [B84PostLiteralResearch.post_eq]
  decide +kernel

theorem support : wires optimizedBlock⊆wires block := by
 have h:=B84SupportResearch.replacement_support head [.CCX 4660 4403 4404] repair tail
  (Eq.mp (congrArg (fun p=>wires repair⊆wires p) shape) repair_in_block)
 exact Eq.mp (congrArg (fun p=>wires optimizedBlock⊆wires p) shape.symm) h

theorem physical (hp : GatePhysical block) : GatePhysical optimizedBlock :=
 B84SupportResearch.replacement_physical head [.CCX 4660 4403 4404] repair tail
  (Eq.mp (congrArg GatePhysical shape) hp) B84RepairSupportResearch.repair_physical

def before : Program := FullBTemp.prefixP L++
 (buildPre ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)++
  cachedSubMany 86 (Acc.tx (FullBTemp.pad L) 139 (Acc.earlyTerm (hiReg L) true 6))
   (Acc.ty (ga.take 139) (Acc.earlyTerm (hiReg L) true 6))
   (Acc.tc (accBank L) 139 (Acc.earlyTerm (hiReg L) true 6)) LowAccCarryDevelop.loans88
   L.core.cin L.core.sumCarry (FullBTemp.hostR L) (FullBTemp.hostP L))
def after : Program := LowAccCarryDevelop.afterLoop

theorem post_eq : buildPost ga (FullBTemp.pad L) (accBank L) L.core.cin (hiReg L)=B84PostLiteralResearch.actualPost := by
 apply ParkAProgramBool.programEq_sound
 rw [B84PostLiteralResearch.post_eq]
 decide +kernel

theorem with_shape (cm : ZeroSetDevelop.CheckedS LowAccCarryDevelop.hosts88 (FullBTemp.middle L c)) :
 LowAccCarryDevelop.bodyWith cm=before++((B84PostLiteralResearch.actualPost++cm.out)++after) := by
 simp only [LowAccCarryDevelop.bodyWith,LowAccCarryDevelop.foldWith,LowAccCarryDevelop.loopWith,
  buildMany,before,after,LowAccCarryDevelop.afterLoop,FullBTemp.prefixP,List.append_assoc,post_eq]

theorem option_context {α β : Type} (result : Option α) (ok : result.isSome=true)
 (transport : α → β) (body : β → Program) (out : α → Program)
 (fallback pre post suffix : Program)
 (shape : ∀ cm, body (transport cm)=pre++((post++out cm)++suffix)) :
 (result.map transport).elim fallback body=
 pre++((post++(result.map out).getD [])++suffix) := by
 cases result with
 | none => simp only [Option.isSome_none,Bool.false_eq_true] at ok
 | some cm => exact shape cm

theorem with_shape_out
 (cm : ZeroSetDevelop.CheckedS LowAccCarryDevelop.hosts88 (FullBTemp.middle L c))
 (out : Program) (eq : cm.out=out) :
 LowAccCarryDevelop.bodyWith cm=before++((B84PostLiteralResearch.actualPost++out)++after) := by
 rw [←eq]
 exact with_shape cm

theorem literal_shape (cm : ZeroSetDevelop.CheckedS LowAccCarryDevelop.hosts88 BData301.p0) :
 LowAccCarryDevelop.bodyWith (LowAccCarryDevelop.fromLiteral cm)=
 before++((B84PostLiteralResearch.actualPost++cm.out)++after) :=
 with_shape_out (LowAccCarryDevelop.fromLiteral cm) cm.out (by unfold LowAccCarryDevelop.fromLiteral; rfl)

theorem option_context_block {α β : Type} (result : Option α) (ok : result.isSome=true)
 (transport : α → β) (body : β → Program) (out : α → Program)
 (fallback pre post suffix blockProgram : Program)
 (blockShape : blockProgram=post++(result.map out).getD [])
 (shape : ∀ cm, body (transport cm)=pre++((post++out cm)++suffix)) :
 (result.map transport).elim fallback body=pre++(blockProgram++suffix) := by
 rw [blockShape]
 exact option_context result ok transport body out fallback pre post suffix shape

theorem actual_shape : (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)=before++(block++after) :=
 option_context_block (ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0)
  LowAccCarryDevelop.success_literal LowAccCarryDevelop.fromLiteral LowAccCarryDevelop.bodyWith
  (fun cm=>cm.out) (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c)
  before B84PostLiteralResearch.actualPost after block (by unfold block output; rfl) literal_shape

end ECDSAAdd.Entrant.B89BlockDevelop

namespace ECDSAAdd.Entrant.B89BodyDevelop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold B89BlockDevelop
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run ZeroSetDevelop.compileS?
attribute [local irreducible] ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots

def optimizedBody : Program := before++(optimizedBlock++after)

theorem checked : B89ContextTransfer.CheckedReplacement (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) optimizedBody :=
 B89ContextTransfer.of_context (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) optimizedBody before block optimizedBlock after actual_shape rfl
  ⟨(fun s m=>(B89BlockDevelop.run_eq s m).symm),B89BlockDevelop.toffoli,B89BlockDevelop.measurements,
   B89BlockDevelop.slots,B89BlockDevelop.support,B89BlockDevelop.physical⟩

theorem run_eq (s : State) (m : List Bool) : run optimizedBody m s=run (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) m s := checked.run_eq s m
theorem toffoli : toffoliCount optimizedBody+1=toffoliCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := checked.toffoli
theorem measurements : measurementCount optimizedBody=measurementCount (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := checked.measurements
theorem slots : Challenge.gateSlots optimizedBody=Challenge.gateSlots (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith)+4 := checked.slots
theorem support : wires optimizedBody⊆wires (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) := checked.support
theorem physical : GatePhysical optimizedBody := checked.physical FullB88OptTemp.actual_physical

theorem resources :
 toffoliCount optimizedBody+89≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 measurementCount optimizedBody=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 Challenge.gateSlots optimizedBody+260≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) := by
 have old:=FullB88OptTemp.actual_resources
 have ht:=checked.toffoli
 have hm:=checked.measurements
 have hs:=checked.slots
 exact ⟨by omega,hm.trans old.2.1,by omega⟩

theorem frame (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue LowAccCarryDevelop.L.core.product base=M^2) (hc : LowAccCarryDevelop.L.PairClean base)
 (hsum : base LowAccCarryDevelop.L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base LowAccCarryDevelop.c=false → M=0)
 (hSource : M=if base LowAccCarryDevelop.c then regValue LowAccCarryDevelop.L.core.high base else 0) :
 Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) optimizedBody
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O)) :=
 B84TripleTransferResearch.of_run_eq optimizedBody (((ZeroSetDevelop.compileS? LowAccCarryDevelop.hosts88 BData301.p0).map LowAccCarryDevelop.fromLiteral).elim (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) LowAccCarryDevelop.bodyWith) checked.run_eq
  (SquareFrame LowAccCarryDevelop.L.core.out base O)
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O))
  (FullB88OptTemp.actual_frame base M hM hP hc hsum O hO hg hSource)
end ECDSAAdd.Entrant.B89BodyDevelop

namespace ECDSAAdd.Entrant.FullB89OptTemp
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ZeroSetDevelop.compileS? ECDSAAdd.toffoliCount ECDSAAdd.measurementCount ECDSAAdd.Challenge.gateSlots

theorem actual_resources :
 toffoliCount B89BodyDevelop.optimizedBody+89≤toffoliCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 measurementCount B89BodyDevelop.optimizedBody=measurementCount (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) ∧
 Challenge.gateSlots B89BodyDevelop.optimizedBody+260≤Challenge.gateSlots (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) :=
 B89BodyDevelop.resources

theorem actual_subset : wires B89BodyDevelop.optimizedBody⊆wires (ParkCarry10Develop.body LowAccCarryDevelop.L LowAccCarryDevelop.c) :=
 B89BodyDevelop.support.trans FullB88OptTemp.actual_subset

theorem actual_physical : GatePhysical B89BodyDevelop.optimizedBody := B89BodyDevelop.physical

theorem actual_frame (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue LowAccCarryDevelop.L.core.product base=M^2) (hc : LowAccCarryDevelop.L.PairClean base)
 (hsum : base LowAccCarryDevelop.L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base LowAccCarryDevelop.c=false → M=0)
 (hSource : M=if base LowAccCarryDevelop.c then regValue LowAccCarryDevelop.L.core.high base else 0) :
 Triple (SquareFrame LowAccCarryDevelop.L.core.out base O) B89BodyDevelop.optimizedBody
  (SquareFrame LowAccCarryDevelop.L.core.out base (bO4 (M^2) (base LowAccCarryDevelop.c) O)) :=
 B89BodyDevelop.frame base M hM hP hc hsum O hO hg hSource

def selectedBody (K : CuccaroStreamedSquareWideLayout) (g : Wire) : Program :=
 match FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse _ => FullB88OptTemp.selectedBody K g
 | isTrue _ => if g=LowAccCarryDevelop.c then B89BodyDevelop.optimizedBody else FullB88OptTemp.selectedBody K g

theorem selected_body_transport (K K' : CuccaroStreamedSquareWideLayout) (g g' : Wire)
 (he : K=K') (hg : g=g') : selectedBody K g=selectedBody K' g' := by
 cases he
 cases hg
 rfl

def hostedSelectedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 selectedBody (ParkCarryDevelop.hostLayout L rho) c

theorem selected_subset (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 wires (selectedBody K g)⊆wires (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact FullB88OptTemp.selected_subset K hw g
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_subset
  · exact FullB88OptTemp.selected_subset K hw g

theorem selected_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (c : Wire) : wires (selectedBody L c)⊆(c::L.wires).toFinset :=
 (selected_subset L hw c).trans (ParkCarry10Develop.body_support L hw hn c)

theorem selected_physical (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths)
 (g : Wire) (nd : (g::K.wires).Nodup) : GatePhysical (selectedBody K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact FullB88OptTemp.selected_physical K hw g nd
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g;exact actual_physical
  · exact FullB88OptTemp.selected_physical K hw g nd

theorem selected_frame (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (hn : K.wires.Nodup)
 (g : Wire) (hcw : g∉K.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
 (hP : regValue K.core.product base=M^2) (hc : K.PairClean base)
 (hsum : base K.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
 (hg : base g=false → M=0) (hSource : M=if base g then regValue K.core.high base else 0) :
 Triple (SquareFrame K.core.out base O) (selectedBody K g)
  (SquareFrame K.core.out base (bO4 (M^2) (base g) O)) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hne => exact FullB88OptTemp.selected_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource
 | isTrue hl =>
  dsimp only
  split
  · rename_i hgc;subst K;subst g;exact actual_frame base M hM hP hc hsum O hO hg hSource
  · exact FullB88OptTemp.selected_frame K hw hn g hcw base M hM hP hc hsum O hO hg hSource

theorem selected_resources (K : CuccaroStreamedSquareWideLayout) (hw : K.Widths) (g : Wire) :
 toffoliCount (selectedBody K g)≤toffoliCount (ParkCarry10Develop.body K g) ∧
 measurementCount (selectedBody K g)=measurementCount (ParkCarry10Develop.body K g) ∧
 Challenge.gateSlots (selectedBody K g)≤Challenge.gateSlots (ParkCarry10Develop.body K g) := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq K LowAccCarryDevelop.L with
 | isFalse hn => exact FullB88OptTemp.selected_resources K hw g
 | isTrue hl =>
  dsimp only
  split
  · rename_i hg;subst K;subst g
    have h:=actual_resources
    exact ⟨by omega,h.2.1,by omega⟩
  · exact FullB88OptTemp.selected_resources K hw g

theorem hostedSelectedBody_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire)
 (c : Wire) (fixed : rho L.core.sumCarry=L.core.sumCarry) :
 hostedSelectedBody L rho c=selectedBody L c :=
 congrArg (fun K=>selectedBody K c) (ParkCarryDevelop.host_eq L rho fixed)

theorem hosted_resources (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedSelectedBody L rho c)≤toffoliCount (ParkCarry10Develop.hostedBody L rho c) ∧
 measurementCount (hostedSelectedBody L rho c)=measurementCount (ParkCarry10Develop.hostedBody L rho c) ∧
 Challenge.gateSlots (hostedSelectedBody L rho c)≤Challenge.gateSlots (ParkCarry10Develop.hostedBody L rho c) :=
 selected_resources (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_subset (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (rho : Equiv.Perm Wire) (c : Wire) :
 wires (hostedSelectedBody L rho c)⊆wires (ParkCarry10Develop.hostedBody L rho c) :=
 selected_subset (ParkCarryDevelop.hostLayout L rho) (ParkCarryDevelop.host_widths L hw rho) c

theorem hosted_fold_support (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths)
 (hn : L.wires.Nodup) (ext : List Wire) (c : Wire) (hlen : 300≤ext.length)
 (away : ∀q∈ext,q∉L.wires) :
 wires (hostedSelectedBody L (LowZero18Square.foldPerm L ext) c)⊆(c::L.wires).toFinset := by
 rw [hostedSelectedBody_eq L _ c (ParkCarryDevelop.fold_fixes_sumCarry L hw hn ext hlen away)]
 exact selected_support L hw hn c

abbrev actualLayout := FullB88OptTemp.actualLayout
abbrev actualControl := FullB88OptTemp.actualControl
abbrev actualExt := FullB88OptTemp.actualExt
abbrev actualFoldPerm := FullB88OptTemp.actualFoldPerm

theorem selected_actual : selectedBody LowAccCarryDevelop.L LowAccCarryDevelop.c=B89BodyDevelop.optimizedBody := by
 unfold selectedBody
 cases he : FastGuardResearch.wideEq LowAccCarryDevelop.L LowAccCarryDevelop.L with
 | isFalse hn => exact False.elim (hn rfl)
 | isTrue hl => exact if_pos rfl

theorem ranked_selected_exact : hostedSelectedBody actualLayout actualFoldPerm actualControl=B89BodyDevelop.optimizedBody := by
 have he : ParkCarryDevelop.hostLayout actualLayout actualFoldPerm=actualLayout :=
  FullBOptTemp.actualHostedLayout_eq
 exact (congrArg (fun K=>selectedBody K actualControl) he).trans
  ((selected_body_transport actualLayout LowAccCarryDevelop.L actualControl LowAccCarryDevelop.c rfl rfl).trans selected_actual)


theorem ranked_certified_gain :
 toffoliCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)+89≤4762 ∧
 measurementCount (hostedSelectedBody actualLayout actualFoldPerm actualControl)=5924 := by
 rw [ranked_selected_exact]
 have h:=actual_resources
 have old:=ParkCarry10Develop.body_counts LowAccCarryDevelop.L LowAccCarryDevelop.layout_widths LowAccCarryDevelop.c
 exact ⟨h.1.trans old.1.le,h.2.1.trans old.2⟩

end ECDSAAdd.Entrant.FullB89OptTemp
