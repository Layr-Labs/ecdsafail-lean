import ECDSAAdd.Submission.Entrant.ParkCarry9

-- Reuse the fourth cached carry with a cheaper low-bit host.

section
-- LowBitCarryLoan
open ECDSAAdd ECDSAAdd.Arithmetic
namespace LowBitCarryLoan
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def loan0 (g src u q : Wire) : Program := [.measureX q [] [.Z u,.CZ g src]]
def restore0 (g src u q : Wire) : Program := [.CCX g src q,.CX u q]
def value (s : BasisState) (g src u : Wire) : Bool := s u ^^ (s g && s src)

theorem loan0_run (g src u q : Wire) (nd:[g,src,u,q].Nodup) (s : State) (m : List Bool)
 (h:s.basis q=value s.basis g src u) :
 run (loan0 g src u q) m s=⟨s.phase,writeBit s.basis q false⟩ := by
 have ng:g≠q :=FourthCarryLoan.get_ne _ nd 0 3 (by simp) (by simp) (by decide)
 have ns:src≠q :=FourthCarryLoan.get_ne _ nd 1 3 (by simp) (by simp) (by decide)
 have nu:u≠q :=FourthCarryLoan.get_ne _ nd 2 3 (by simp) (by simp) (by decide)
 cases m with
 | nil => simp [loan0,run,measureAndCorrect,correct]
 | cons b ms =>
  cases b <;> cases hg:s.basis g <;> cases hs:s.basis src <;> cases hu:s.basis u <;>
   simp [loan0,run,measureAndCorrect,correct,h,value,writeBit,Function.update_apply,
    ng,ns,nu,hg,hs,hu]

theorem restore0_run (g src u q : Wire) (nd:[g,src,u,q].Nodup) (s : State) (m : List Bool) :
 run (restore0 g src u q) m s=⟨s.phase,writeBit s.basis q (s.basis q ^^ value s.basis g src u)⟩ := by
 have ng:g≠q :=FourthCarryLoan.get_ne _ nd 0 3 (by simp) (by simp) (by decide)
 have ns:src≠q :=FourthCarryLoan.get_ne _ nd 1 3 (by simp) (by simp) (by decide)
 have nu:u≠q :=FourthCarryLoan.get_ne _ nd 2 3 (by simp) (by simp) (by decide)
 change (⟨s.phase,_⟩:State)=⟨s.phase,_⟩
 apply congrArg (State.mk s.phase)
 funext w
 by_cases h:w=q
 · subst w
   cases hg:s.basis g <;> cases hs:s.basis src <;> cases hu:s.basis u <;> cases hq:s.basis q <;>
    simp [restore0,run,value,writeBit,Function.update_apply,ng,ns,nu,hg,hs,hu,hq]
 · simp [restore0,run,writeBit,Function.update_apply,h]

theorem counts (g src u q : Wire) :
 toffoliCount (loan0 g src u q)=0 ∧ measurementCount (loan0 g src u q)=1 ∧
 Challenge.gateSlots (loan0 g src u q)=3 ∧ toffoliCount (restore0 g src u q)=1 ∧
 measurementCount (restore0 g src u q)=0 ∧ Challenge.gateSlots (restore0 g src u q)=2 := by
 simp [loan0,restore0,toffoliCount,measurementCount,Challenge.gateSlots,Challenge.instructionSlots]
#print axioms loan0_run
#print axioms restore0_run
#print axioms counts
end LowBitCarryLoan

end -- isolated Carry10 component

section
-- LowBitCarryEnds
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def prepare4L (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) : Program :=
 prepare3 g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 ++
 (LowBitCarryLoan.loan0 g v0 u0 e0 ++ prime2 u3 r3 h2 e0)
def finish4L (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) : Program :=
 clear2 u3 r3 h2 e0 ++
 (LowBitCarryLoan.restore0 g v0 u0 e0 ++ finish3 g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2)

theorem geometry15_12 (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) :
 [g,v1,u0,u1,u2,r0,r1,r2,e0,cache,h1,h2].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h:=List.nodup_iff_count_le_one.mp nd q
 simp only [List.count_cons,List.count_nil]at h ⊢
 omega

theorem geometry15_4 (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) :
 [g,v0,u0,e0].Nodup := by
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have h:=List.nodup_iff_count_le_one.mp nd q
 simp only [List.count_cons,List.count_nil]at h ⊢
 omega

theorem prepare4L_run (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) (s:State) (m:List Bool)
 (hz:s.basis cache=false)
 (hl1:s.basis h1=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0 && s.basis e0)))
 (hl2:s.basis h2=loanValue2 s.basis g v1 u0 u1 u2 e0 h1)
 (hl0:s.basis e0=LowBitCarryLoan.value s.basis g v0 u0) :
 let k0:=s.basis u0 && !s.basis r0
 let k1:=carryBit (s.basis u1) (!s.basis r1) k0
 let k2:=carryBit (s.basis u2) (!s.basis r2) k1
 let k3:=carryBit (s.basis u3) (!s.basis r3) k2
 run (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2) m s=
  ⟨s.phase,writeBit (writeBit (writeBit (writeBit s.basis cache k0) h1 k1) h2 k2) e0 k3⟩ := by
 have geom:=nd
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have nd12:=geometry15_12 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 have nd4:=geometry15_4 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 let k0:=s.basis u0 && !s.basis r0
 let k1:=carryBit (s.basis u1) (!s.basis r1) k0
 let k2:=carryBit (s.basis u2) (!s.basis r2) k1
 let k3:=carryBit (s.basis u3) (!s.basis r3) k2
 let S1:State:=⟨s.phase,writeBit (writeBit (writeBit s.basis cache k0) h1 k1) h2 k2⟩
 let S2:State:=⟨s.phase,writeBit S1.basis e0 false⟩
 have p:∀r,run (prepare3 g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2) r s=S1 := by
  intro r
  exact prepare3_run g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 nd12 s r hz hl1 hl2
 have q:∀r,run (LowBitCarryLoan.loan0 g v0 u0 e0) r S1=S2 := by
  intro r
  apply LowBitCarryLoan.loan0_run g v0 u0 e0 nd4 S1 r
  simpa [S1,LowBitCarryLoan.value,writeBit,Function.update_apply,
   show e0≠cache by tauto,show e0≠h1 by tauto,show e0≠h2 by tauto,
   show g≠cache by tauto,show g≠h1 by tauto,show g≠h2 by tauto,
   show v0≠cache by tauto,show v0≠h1 by tauto,show v0≠h2 by tauto,
   show u0≠cache by tauto,show u0≠h1 by tauto,show u0≠h2 by tauto] using hl0
 have z:∀r,run (prime2 u3 r3 h2 e0) r S2=
  ⟨s.phase,writeBit (writeBit (writeBit (writeBit s.basis cache k0) h1 k1) h2 k2) e0 k3⟩ := by
  intro r
  rw [prime2_run u3 r3 h2 e0 (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) (by tauto) S2 r]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases h:w=e0
  · subst w
    simp [S2,S1,k3,writeBit,Function.update_apply,
     show u3≠cache by tauto,show u3≠h1 by tauto,show u3≠h2 by tauto,show u3≠e0 by tauto,
     show r3≠cache by tauto,show r3≠h1 by tauto,show r3≠h2 by tauto,show r3≠e0 by tauto,
     show h2≠cache by tauto,show h2≠h1 by tauto,show h2≠e0 by tauto]
  · simp [S2,S1,writeBit,Function.update_apply,h]
 dsimp only
 rw [prepare4L,run_append,p,run_append,q,z]

theorem finish4L_run (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) (s:State) (m:List Bool)
 (hk0:s.basis cache=(s.basis u0 && !s.basis r0))
 (hk1:s.basis h1=carryBit (s.basis u1) (!s.basis r1) (s.basis cache))
 (hk2:s.basis h2=carryBit (s.basis u2) (!s.basis r2) (s.basis h1))
 (hk3:s.basis e0=carryBit (s.basis u3) (!s.basis r3) (s.basis h2)) :
 let b0:=writeBit s.basis e0 (LowBitCarryLoan.value s.basis g v0 u0)
 let t:=writeBit (writeBit (writeBit b0 h2 false) h1
  (b0 u1 ^^ b0 u0 ^^ (b0 u0 && b0 e0))) cache false
 let t2:=writeBit t h2 (loanValue2 t g v1 u0 u1 u2 e0 h1)
 run (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2) m s=⟨s.phase,t2⟩ := by
 have geom:=nd
 simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have nd12:=geometry15_12 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 have nd4:=geometry15_4 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 let S0:State:=⟨s.phase,writeBit s.basis e0 false⟩
 let b0:=writeBit s.basis e0 (LowBitCarryLoan.value s.basis g v0 u0)
 let S1:State:=⟨s.phase,b0⟩
 let t:=writeBit (writeBit (writeBit b0 h2 false) h1
  (b0 u1 ^^ b0 u0 ^^ (b0 u0 && b0 e0))) cache false
 let t2:=writeBit t h2 (loanValue2 t g v1 u0 u1 u2 e0 h1)
 have p:∀r,run (clear2 u3 r3 h2 e0) r s=S0 := by
  intro r
  exact clear2_run u3 r3 h2 e0 (by tauto) (by tauto) (by tauto) s r hk3
 have q:∀r,run (LowBitCarryLoan.restore0 g v0 u0 e0) r S0=S1 := by
  intro r
  rw [LowBitCarryLoan.restore0_run g v0 u0 e0 nd4 S0 r]
  apply congrArg (State.mk s.phase)
  funext w
  by_cases h:w=e0
  · subst w
    simp [S0,S1,b0,LowBitCarryLoan.value,writeBit,Function.update_apply,
     show u0≠e0 by tauto,show g≠e0 by tauto,show v0≠e0 by tauto]
  · simp [S0,S1,b0,writeBit,Function.update_apply,h]
 have z:∀r,run (finish3 g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2) r S1=⟨s.phase,t2⟩ := by
  intro r
  rw [finish3_run g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 nd12 S1 r]
  · simpa [S1,b0,writeBit,Function.update_apply,show cache≠e0 by tauto,
     show u0≠e0 by tauto,show r0≠e0 by tauto] using hk0
  · simpa [S1,b0,writeBit,Function.update_apply,show h1≠e0 by tauto,
     show u1≠e0 by tauto,show r1≠e0 by tauto,show cache≠e0 by tauto] using hk1
  · simpa [S1,b0,writeBit,Function.update_apply,show h2≠e0 by tauto,
     show u2≠e0 by tauto,show r2≠e0 by tauto,show h1≠e0 by tauto] using hk2
 dsimp only
 rw [finish4L,run_append,p,run_append,q,z]
#print axioms prepare4L_run
#print axioms finish4L_run
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryGeometry
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem geometry15 (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (g : Wire) (hg : g ∉ L.wires) :
 [g,bit1 L.core.high,L.core.high.headD 0,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,
  cacheWire L,hostWire L,host2Wire L].Nodup := by
 have geo := mGeo L hw hn
 apply List.nodup_iff_count_le_one.mpr
 intro q
 have uc := head4_count (mU L) (by rw [geo.u]; decide) q
 have rc := head4_count (mR L) (by rw [geo.r]; decide) q
 have ec := head3_count ((eReg L).take 129) (by simp [eReg_length L hw]) q
 have hhead : ((eReg L).take 129).headD 0 = (eReg L).headD 0 := head_take_pos _ _ (by decide)
 have hbit : bit1 ((eReg L).take 129) = hostWire L := bit1_take _ _ (by decide)
 have hbit2 : bit2 ((eReg L).take 129) = host2Wire L := bit2_take _ _ (by decide)
 rw [hhead,hbit,hbit2] at ec
 have ed := congrArg (List.count q) (cache_decomp L hw)
 have ud : (mU L).count q ≤ (hiReg L).count q := (List.drop_sublist _ _).count_le q
 have rd : (mR L).count q ≤ L.core.work.count q :=
  ((List.take_sublist _ _).trans (List.drop_sublist _ _)).count_le q
 have hy : 3 ≤ L.core.high.length := by simp [CuccaroStreamedSquareLayout.high,hw.core.y]
 have hv := head3_count L.core.high hy q
 have vy : L.core.high.count q ≤ L.core.y.count q := by
  apply List.Sublist.count_le
  exact (List.take_sublist _ _).trans (List.drop_sublist _ _)
 have vc : ([bit1 L.core.high,L.core.high.headD 0] : List Wire).count q ≤ L.core.y.count q := by
  simp only [List.count_cons,List.count_nil] at hv ⊢
  omega
 have ps := productSplit L q
 have es := eReg_count L q
 have lc := List.nodup_iff_count_le_one.mp (List.nodup_cons.mpr ⟨hg,hn⟩) q
 simp only [CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires,foldPad,
  List.count_cons,List.count_append,List.count_nil] at lc uc rc ec ed vc ⊢
 omega

theorem e0_ne_key (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 (eReg L).headD 0≠eU L := by
 have shape:=(eShape L hw).1
 have len:(eRlow L).length=128:=by simp[eRlow,hw.core.product]
 have hm:(eReg L).headD 0∈eRlow L:=by
  rw [shape]
  cases hr:eRlow L with
  | nil => simp [hr] at len
  | cons a rest => simp
 have nd:=eReg_nodup L hn
 rw [shape]at nd
 exact (List.nodup_append.mp nd).2.2 _ hm _ (by simp)
#print axioms geometry15
#print axioms e0_ne_key
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryNumbers
open ECDSAAdd ECDSAAdd.Entrant ECDSAAdd.Entrant.SecondCarryLoan ECDSAAdd.Entrant.ThirdCarryLoanDevelop
namespace LowBitCarryNumbers
set_option maxHeartbeats 8000000

theorem loan0_from_mod2 (g : Bool) (S U E : Nat)
 (hE:E%2=((if g then S else 0)^2+U)%2) :
 digit E 0=(digit U 0 ^^ (g && digit S 0)) := by
 have hs:S%2=0 ∨ S%2=1:=by omega
 have hu:U%2=0 ∨ U%2=1:=by omega
 cases g <;> rcases hs with hs|hs <;> rcases hu with hu|hu <;>
  simp_all [digit,Nat.add_mod,Nat.pow_mod]
#print axioms loan0_from_mod2
end LowBitCarryNumbers

end -- isolated Carry10 component

section
-- LowBitCarryPrimitiveResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.RecordedQuantum
namespace LowBitCarryLoan
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem physical (g src u q : Wire) (nd:[g,src,u,q].Nodup) :
 GatePhysical (loan0 g src u q) ∧ GatePhysical (restore0 g src u q) := by
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at nd
 simp [loan0,restore0,GatePhysical,PhysicalInstr,ProperGate]
 tauto

theorem support (g src u q : Wire) :
 wires (loan0 g src u q)⊆[g,src,u,q].toFinset ∧
 wires (restore0 g src u q)⊆[g,src,u,q].toFinset := by
 constructor <;> intro r h <;>
  simp [loan0,restore0,wires,Instr.wires,correctionWires]at h ⊢ <;> tauto
#print axioms physical
#print axioms support
end LowBitCarryLoan

end -- isolated Carry10 component

section
-- LowBitCarryEndsResources
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop ECDSAAdd.RecordedQuantum
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem prepare4L_counts (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) :
 toffoliCount (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=4 ∧
 measurementCount (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=3 ∧
 Challenge.gateSlots (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=41 := by
 refine ⟨rfl,rfl,?_⟩
 simp[prepare4L,LowBitCarryLoan.loan0,prepare3,loan2,SecondCarryLoan.prepare,loan,prime,prime2,majority,
  Challenge.gateSlots,Challenge.instructionSlots]

theorem finish4L_counts (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) :
 toffoliCount (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=4 ∧
 measurementCount (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=4 ∧
 Challenge.gateSlots (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)=34 := by
 refine ⟨rfl,rfl,?_⟩
 simp[finish4L,LowBitCarryLoan.restore0,finish3,restore2,SecondCarryLoan.finish,clear,clear2,restore,
  Challenge.gateSlots,Challenge.instructionSlots]

theorem ends4L_physical (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire)
 (nd:[g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].Nodup) :
 GatePhysical (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2) ∧
 GatePhysical (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2) := by
 have nd12:=geometry15_12 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 have nd4:=geometry15_4 g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 nd
 have nd4': [u3,r3,h2,e0].Nodup := by
  apply List.nodup_iff_count_le_one.mpr
  intro q
  have h:=List.nodup_iff_count_le_one.mp nd q
  simp only[List.count_cons,List.count_nil]at h ⊢
  omega
 have a:=LowBitCarryLoan.physical g v0 u0 e0 nd4
 have b:=ends3_physical g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2 nd12
 have p:GatePhysical (prime2 u3 r3 h2 e0) ∧ GatePhysical (clear2 u3 r3 h2 e0) := by
  simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at nd4'
  simp[prime2,majority,clear2,GatePhysical,PhysicalInstr,ProperGate]
  tauto
 simp only[prepare4L,finish4L,gatePhysical_append]
 exact ⟨⟨b.1,a.1,p.1⟩,p.2,a.2,b.2⟩

theorem ends4L_support (g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2 : Wire) :
 wires (prepare4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)⊆
 [g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].toFinset ∧
 wires (finish4L g v1 v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache h1 h2)⊆
 [g,v1,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,h1,h2].toFinset := by
 have a:=LowBitCarryLoan.support g v0 u0 e0
 have b:=ends3_support g v1 u0 u1 u2 r0 r1 r2 e0 cache h1 h2
 have p:wires (prime2 u3 r3 h2 e0)⊆[u3,r3,h2,e0].toFinset ∧
   wires (clear2 u3 r3 h2 e0)⊆[u3,r3,h2,e0].toFinset := by
  constructor <;> intro q h <;>
   simp[prime2,majority,clear2,ECDSAAdd.wires,Instr.wires,correctionWires]at h ⊢ <;> tauto
 constructor <;> intro q h
 · simp only[prepare4L,wires_append,Finset.mem_union]at h
   rcases h with h|h|h
   · have z:=b.1 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
   · have z:=a.1 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
   · have z:=p.1 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
 · simp only[finish4L,wires_append,Finset.mem_union]at h
   rcases h with h|h|h
   · have z:=p.2 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
   · have z:=a.2 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
   · have z:=b.2 h;simp only[List.mem_toFinset,List.mem_cons,List.mem_singleton]at z ⊢;tauto
#print axioms prepare4L_counts
#print axioms finish4L_counts
#print axioms ends4L_physical
#print axioms ends4L_support
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryFull
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

def wMidFullCCC0 (L : CuccaroStreamedSquareWideLayout) (c : Wire) : Program :=
 prepare4L c (bit1 L.core.high) (L.core.high.headD 0) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L)) ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L) ++
 ((wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0) ++ (wCoreK L ++ wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0))) ++
 finish4L c (bit1 L.core.high) (L.core.high.headD 0) ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L)) ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L))

theorem wMidFullCCC0_step (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup)
 (c:Wire) (hcw:c∉L.wires) (base:BasisState) (hc:L.PairClean base) (O E b1:Nat)
 (hb1:regValue (hiReg L) base=b1) (hb1lt:b1<2^128) (hO:O<SquareReduction.p)
 (H l K:Nat) (hH:H<2^96) (hl:l<2^32) (hK:K≤1) (hE:E=2^32*H+l+2^128*K)
 (hLoan:(E/2%2==1)=((b1/2^96/2%2==1) ^^ (b1/2^96%2==1) ^^
   ((b1/2^96%2==1)&&(E%2==1))))
 (hLoan2:digit E 2= (digit (b1/2^96) 2 ^^
   (base (bit1 L.core.high)&&base c) ^^ (base (bit1 L.core.high)&&digit E 0) ^^
   (base (bit1 L.core.high)&&digit (b1/2^96) 0) ^^
   (digit (b1/2^96) 1&&digit E 1) ^^ digit (b1/2^96) 1))
 (hLoan0 : digit E 0 = (digit (b1/2^96) 0 ^^ (base c && base (L.core.high.headD 0)))) :
 Triple (BState L base O E (4294968272*b1)) (wMidFullCCC0 L c)
 (BState L base (((b1/2^96+4294968273*(4294968272*b1/2^128-b1/2^96))+4294968272*2^32*K+
   2^128*((4294968272*b1)%2^128)+(SquareReduction.p-1-O))%SquareReduction.p) E (4294968272*b1)) := by
 intro s m h
 let u0:Wire:=(mU L).headD 0
 let u1:Wire:=bit1 (mU L)
 let u2:Wire:=bit2 (mU L)
 let u3:Wire:=bit3 (mU L)
 let r0:Wire:=(mR L).headD 0
 let r1:Wire:=bit1 (mR L)
 let r2:Wire:=bit2 (mR L)
 let r3:Wire:=bit3 (mR L)
 let e0:Wire:=(eReg L).headD 0
 let v:Wire:=bit1 L.core.high
 let v0:Wire:=L.core.high.headD 0
 let cache:Wire:=cacheWire L
 let host:Wire:=hostWire L
 let host2:Wire:=host2Wire L
 let u:=b1/2^96
 let d:=4294968272*b1/2^128-u
 let k0:Bool:=(u%2==1)&&(d%2==1)
 let k1:Bool:=carryLow2 u d
 let k2:Bool:=carryLow3 u d
 let k3:Bool:=carryLow4 u d
 have nd:[c,v,v0,u0,u1,u2,u3,r0,r1,r2,r3,e0,cache,host,host2].Nodup:=geometry15 L hw hn c hcw
 have geom:=nd
 simp only[List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or,or_false]at geom
 have n0_11:c≠e0:=FourthCarryLoan.get_ne _ nd 0 11 (by simp) (by simp) (by decide)
 have n0_12:c≠cache:=FourthCarryLoan.get_ne _ nd 0 12 (by simp) (by simp) (by decide)
 have n0_13:c≠host:=FourthCarryLoan.get_ne _ nd 0 13 (by simp) (by simp) (by decide)
 have n0_14:c≠host2:=FourthCarryLoan.get_ne _ nd 0 14 (by simp) (by simp) (by decide)
 have n1_11:v≠e0:=FourthCarryLoan.get_ne _ nd 1 11 (by simp) (by simp) (by decide)
 have n1_12:v≠cache:=FourthCarryLoan.get_ne _ nd 1 12 (by simp) (by simp) (by decide)
 have n1_13:v≠host:=FourthCarryLoan.get_ne _ nd 1 13 (by simp) (by simp) (by decide)
 have n1_14:v≠host2:=FourthCarryLoan.get_ne _ nd 1 14 (by simp) (by simp) (by decide)
 have n2_11:v0≠e0:=FourthCarryLoan.get_ne _ nd 2 11 (by simp) (by simp) (by decide)
 have n2_12:v0≠cache:=FourthCarryLoan.get_ne _ nd 2 12 (by simp) (by simp) (by decide)
 have n2_13:v0≠host:=FourthCarryLoan.get_ne _ nd 2 13 (by simp) (by simp) (by decide)
 have n2_14:v0≠host2:=FourthCarryLoan.get_ne _ nd 2 14 (by simp) (by simp) (by decide)
 have n3_11:u0≠e0:=FourthCarryLoan.get_ne _ nd 3 11 (by simp) (by simp) (by decide)
 have n3_12:u0≠cache:=FourthCarryLoan.get_ne _ nd 3 12 (by simp) (by simp) (by decide)
 have n3_13:u0≠host:=FourthCarryLoan.get_ne _ nd 3 13 (by simp) (by simp) (by decide)
 have n3_14:u0≠host2:=FourthCarryLoan.get_ne _ nd 3 14 (by simp) (by simp) (by decide)
 have n4_11:u1≠e0:=FourthCarryLoan.get_ne _ nd 4 11 (by simp) (by simp) (by decide)
 have n4_12:u1≠cache:=FourthCarryLoan.get_ne _ nd 4 12 (by simp) (by simp) (by decide)
 have n4_13:u1≠host:=FourthCarryLoan.get_ne _ nd 4 13 (by simp) (by simp) (by decide)
 have n4_14:u1≠host2:=FourthCarryLoan.get_ne _ nd 4 14 (by simp) (by simp) (by decide)
 have n5_11:u2≠e0:=FourthCarryLoan.get_ne _ nd 5 11 (by simp) (by simp) (by decide)
 have n5_12:u2≠cache:=FourthCarryLoan.get_ne _ nd 5 12 (by simp) (by simp) (by decide)
 have n5_13:u2≠host:=FourthCarryLoan.get_ne _ nd 5 13 (by simp) (by simp) (by decide)
 have n5_14:u2≠host2:=FourthCarryLoan.get_ne _ nd 5 14 (by simp) (by simp) (by decide)
 have n6_11:u3≠e0:=FourthCarryLoan.get_ne _ nd 6 11 (by simp) (by simp) (by decide)
 have n6_12:u3≠cache:=FourthCarryLoan.get_ne _ nd 6 12 (by simp) (by simp) (by decide)
 have n6_13:u3≠host:=FourthCarryLoan.get_ne _ nd 6 13 (by simp) (by simp) (by decide)
 have n6_14:u3≠host2:=FourthCarryLoan.get_ne _ nd 6 14 (by simp) (by simp) (by decide)
 have n7_11:r0≠e0:=FourthCarryLoan.get_ne _ nd 7 11 (by simp) (by simp) (by decide)
 have n7_12:r0≠cache:=FourthCarryLoan.get_ne _ nd 7 12 (by simp) (by simp) (by decide)
 have n7_13:r0≠host:=FourthCarryLoan.get_ne _ nd 7 13 (by simp) (by simp) (by decide)
 have n7_14:r0≠host2:=FourthCarryLoan.get_ne _ nd 7 14 (by simp) (by simp) (by decide)
 have n8_11:r1≠e0:=FourthCarryLoan.get_ne _ nd 8 11 (by simp) (by simp) (by decide)
 have n8_12:r1≠cache:=FourthCarryLoan.get_ne _ nd 8 12 (by simp) (by simp) (by decide)
 have n8_13:r1≠host:=FourthCarryLoan.get_ne _ nd 8 13 (by simp) (by simp) (by decide)
 have n8_14:r1≠host2:=FourthCarryLoan.get_ne _ nd 8 14 (by simp) (by simp) (by decide)
 have n9_11:r2≠e0:=FourthCarryLoan.get_ne _ nd 9 11 (by simp) (by simp) (by decide)
 have n9_12:r2≠cache:=FourthCarryLoan.get_ne _ nd 9 12 (by simp) (by simp) (by decide)
 have n9_13:r2≠host:=FourthCarryLoan.get_ne _ nd 9 13 (by simp) (by simp) (by decide)
 have n9_14:r2≠host2:=FourthCarryLoan.get_ne _ nd 9 14 (by simp) (by simp) (by decide)
 have n10_11:r3≠e0:=FourthCarryLoan.get_ne _ nd 10 11 (by simp) (by simp) (by decide)
 have n10_12:r3≠cache:=FourthCarryLoan.get_ne _ nd 10 12 (by simp) (by simp) (by decide)
 have n10_13:r3≠host:=FourthCarryLoan.get_ne _ nd 10 13 (by simp) (by simp) (by decide)
 have n10_14:r3≠host2:=FourthCarryLoan.get_ne _ nd 10 14 (by simp) (by simp) (by decide)
 have n11_12:e0≠cache:=FourthCarryLoan.get_ne _ nd 11 12 (by simp) (by simp) (by decide)
 have n11_13:e0≠host:=FourthCarryLoan.get_ne _ nd 11 13 (by simp) (by simp) (by decide)
 have n11_14:e0≠host2:=FourthCarryLoan.get_ne _ nd 11 14 (by simp) (by simp) (by decide)
 have n12_11:cache≠e0:=FourthCarryLoan.get_ne _ nd 12 11 (by simp) (by simp) (by decide)
 have n12_13:cache≠host:=FourthCarryLoan.get_ne _ nd 12 13 (by simp) (by simp) (by decide)
 have n12_14:cache≠host2:=FourthCarryLoan.get_ne _ nd 12 14 (by simp) (by simp) (by decide)
 have n13_11:host≠e0:=FourthCarryLoan.get_ne _ nd 13 11 (by simp) (by simp) (by decide)
 have n13_12:host≠cache:=FourthCarryLoan.get_ne _ nd 13 12 (by simp) (by simp) (by decide)
 have n13_14:host≠host2:=FourthCarryLoan.get_ne _ nd 13 14 (by simp) (by simp) (by decide)
 have n14_11:host2≠e0:=FourthCarryLoan.get_ne _ nd 14 11 (by simp) (by simp) (by decide)
 have n14_12:host2≠cache:=FourthCarryLoan.get_ne _ nd 14 12 (by simp) (by simp) (by decide)
 have n14_13:host2≠host:=FourthCarryLoan.get_ne _ nd 14 13 (by simp) (by simp) (by decide)
 have ce:cache∈eReg L:=cache_mem L hw
 have he:host∈eReg L:=host_mem L hw
 have he2:host2∈eReg L:=host2_mem L hw
 have he0:e0∈eReg L:=head_mem _ (by simp [eReg_length L hw])
 have ca:=external_away L c hcw
 have vy:v∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take
  (bit1_mem L.core.high (by simp[CuccaroStreamedSquareLayout.high,hw.core.y,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13])))
 have va:=source_away L hn v vy
 have vy0:v0∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take
  (head_mem L.core.high (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])))
 have va0:=source_away L hn v0 vy0
 have sg:s.basis c=base c:=h.2.2.2 c ca.1 ca.2.1 ca.2.2
 have sv:s.basis v=base v:=h.2.2.2 v va.1 va.2.1 va.2.2
 have sv0 : s.basis v0 = base v0 := h.2.2.2 v0 va0.1 va0.2.1 va0.2.2
 have hz:s.basis cache=false:=e_cache_zero L hw s.basis E h.2.1 (by rw[hE];omega)
 have b0:=bstate_heads L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b1s:=bstate_heads2 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b2:=bstate_heads3 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have b3:=bstate_heads4 L hw hn base s.basis hc O E b1 hb1 hb1lt h
 have es:s.basis e0=(E%2==1):=by
  dsimp[e0,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13];rw[head_parity (eReg L) s.basis (by simp[eReg_length L hw,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]),h.2.1]
 have hs:s.basis host=(E/2%2==1):=by
  dsimp[host,hostWire,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13];rw[bit1_parity (eReg L) s.basis (by simp[eReg_length L hw,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]),h.2.1]
 have hs2:s.basis host2=digit E 2:=by
  dsimp[host2,host2Wire,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13];rw[bit2_parity (eReg L) s.basis (by simp[eReg_length L hw,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]),h.2.1]
 have ready:s.basis host=(s.basis u1 ^^ s.basis u0 ^^ (s.basis u0&&s.basis e0)):=by
  rw[hs,b0.1,b1s.1,es];exact hLoan
 have ready2:s.basis host2=loanValue2 s.basis c v u0 u1 u2 e0 host:=by
  rw[hs2]
  unfold loanValue2
  rw[b2.1,b0.1,b1s.1,es,hs,sg,sv]
  simpa only[digit,pow_zero,pow_one,Nat.div_one,v]using hLoan2
 have ready0:s.basis e0=LowBitCarryLoan.value s.basis c v0 u0:=by
  rw[es]
  unfold LowBitCarryLoan.value
  rw[b0.1,sg,sv0]
  simpa only[digit,pow_zero,Nat.div_one,v0]using hLoan0
 have carry0:(s.basis u0&&!s.basis r0)=k0:=by
  rw[b0.1,b0.2];simpa only[Nat.one_mul]using carry_parity u d 1 (by decide)
 have carry1:carryBit (s.basis u1) (!s.basis r1) k0=k1:=by
  rw[b1s.1,b1s.2];simpa only[Nat.one_mul]using sub_second u d 1 (by decide)
 have carry2:carryBit (s.basis u2) (!s.basis r2) k1=k2:=by
  rw[b2.1,b2.2];simpa only[Nat.one_mul]using sub_third u d 1 (by decide)
 have carry3 : carryBit (s.basis u3) (!s.basis r3) k2 = k3 := by
  rw [b3.1,b3.2]; simpa only [Nat.one_mul] using sub_fourth u d 1 (by decide)
 let t:BasisState:=writeBit (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2) e0 k3
 let EP:Nat:=regValue (eReg L) t
 have prepared:∀mm,run (prepare4L c v v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2) mm s=⟨s.phase,t⟩:=by
  intro mm
  rw[prepare4L_run c v v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2 nd s mm hz ready ready2 ready0,carry0,carry1,carry2,carry3]
 have hb0:=bstate_write_e L hn cache ce base s.basis O E _ h k0
 have hb2:=bstate_write_e L hn host he base (writeBit s.basis cache k0) O
  (regValue (eReg L) (writeBit s.basis cache k0)) _ hb0 k1
 have hb3:=bstate_write_e L hn host2 he2 base (writeBit (writeBit s.basis cache k0) host k1) O
  (regValue (eReg L) (writeBit (writeBit s.basis cache k0) host k1)) _ hb2 k2
 have hb4 := bstate_write_e L hn e0 he0 base
  (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2) O
  (regValue (eReg L) (writeBit (writeBit (writeBit s.basis cache k0) host k1) host2 k2)) _ hb3 k3
 have inp:BState L base O EP (4294968272*b1) t ∧ t cache=k0 ∧ t host=k1 ∧ t host2=k2 ∧ t e0=k3 ∧
  (if t (eU L) then 1 else 0)=K:=by
  refine ⟨hb4,?_,?_,?_,?_,?_⟩
  · simp[t,writeBit,Function.update_apply,show cache≠host from FourthCarryLoan.get_ne _ nd 12 13 (by simp) (by simp) (by decide),show cache≠host2 from FourthCarryLoan.get_ne _ nd 12 14 (by simp) (by simp) (by decide),n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  · simp[t,writeBit,Function.update_apply,show host≠host2 from FourthCarryLoan.get_ne _ nd 13 14 (by simp) (by simp) (by decide),n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  · simp[t,writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  · simp[t,writeBit,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  · have hk:=bstate_key L hw s.basis E H l K h.2.1 hH hl hK hE
    simpa[t,writeBit,Function.update_apply,show eU L≠cache from (cache_ne_k L hw hn).symm,
     show eU L≠host from (host_ne_key L hw hn).symm,show eU L≠host2 from (host2_ne_key L hw hn).symm,show eU L≠e0 from (e0_ne_key L hw hn).symm]using hk
 let mid:=wFwdCCCC L cache host host2 e0++(wCoreK L++wInvCCCC L cache host host2 e0)
 let rest:=m.drop (measurementCount (prepare4L c v v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2))
 let mmid:=rest.take (measurementCount mid)
 rw[wMidFullCCC0,run_append,prepared,run_append]
 have hm:=wMidCCCC_step L hw hn cache ce host he host2 he2 e0 he0 base hc O EP b1 hb1 hb1lt hO K hK
  (⟨s.phase,t⟩:State) mmid inp
 generalize hr:run mid mmid (⟨s.phase,t⟩:State)=r at hm ⊢
 have br0:=bstate_heads L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br1:=bstate_heads2 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br2:=bstate_heads3 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have br3:=bstate_heads4 L hw hn base r.basis hc _ EP b1 hb1 hb1lt hm.2.1
 have er:∀q∈eReg L,r.basis q=t q:=(regValue_eq_iff _ _ _).mp hm.2.1.2.1
 have rU0:r.basis u0=s.basis u0:=br0.1.trans b0.1.symm
 have rU1:r.basis u1=s.basis u1:=br1.1.trans b1s.1.symm
 have rU2:r.basis u2=s.basis u2:=br2.1.trans b2.1.symm
 have rR0:r.basis r0=s.basis r0:=br0.2.trans b0.2.symm
 have rR1:r.basis r1=s.basis r1:=br1.2.trans b1s.2.symm
 have rR2:r.basis r2=s.basis r2:=br2.2.trans b2.2.symm
 have rU3:r.basis u3=s.basis u3:=br3.1.trans b3.1.symm
 have rR3:r.basis r3=s.basis r3:=br3.2.trans b3.2.symm
 have rV0:r.basis v0=s.basis v0:=(hm.2.1.2.2.2 v0 va0.1 va0.2.1 va0.2.2).trans sv0.symm
 have rG:r.basis c=s.basis c:=(hm.2.1.2.2.2 c ca.1 ca.2.1 ca.2.2).trans sg.symm
 have rV:r.basis v=s.basis v:=(hm.2.1.2.2.2 v va.1 va.2.1 va.2.2).trans sv.symm
 have rk:r.basis cache=(r.basis u0&&!r.basis r0):=by
  rw[rU0,rR0,carry0];exact hm.2.2.1
 have rk1:r.basis host=carryBit (r.basis u1) (!r.basis r1) (r.basis cache):=by
  rw[rU1,rR1,hm.2.2.1,carry1];exact hm.2.2.2.1
 have rk2:r.basis host2=carryBit (r.basis u2) (!r.basis r2) (r.basis host):=by
  rw[rU2,rR2,hm.2.2.2.1,carry2];exact hm.2.2.2.2.1
 have rk3:r.basis e0=carryBit (r.basis u3) (!r.basis r3) (r.basis host2):=by
  rw[rU3,rR3,hm.2.2.2.2.1,carry3];exact hm.2.2.2.2.2.1
 have restored0:LowBitCarryLoan.value r.basis c v0 u0=s.basis e0:=by
  unfold LowBitCarryLoan.value
  rw[rG,rV0,rU0]
  exact ready0.symm
 rw[finish4L_run c v v0 u0 u1 u2 u3 r0 r1 r2 r3 e0 cache host host2 nd r _ rk rk1 rk2 rk3]
 dsimp only
 rw[restored0]
 let b0':=writeBit r.basis e0 (s.basis e0)
 have restored1:(b0' u1 ^^ b0' u0 ^^ (b0' u0&&b0' e0))=s.basis host:=by
  simp only[b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13,ite_false,ite_true,rU0,rU1]
  exact ready.symm
 rw[restored1]
 let t0:=writeBit (writeBit (writeBit b0' host2 false) host (s.basis host)) cache false
 have restored2:loanValue2 t0 c v u0 u1 u2 e0 host=s.basis host2:=by
  simp only[loanValue2,t0,b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13,ite_false,ite_true,rG,rV,rU0,rU1,rU2]
  exact ready2.symm
 refine ⟨hm.1,?_⟩
 have hf0:=bstate_write_e L hn e0 he0 base r.basis _ EP _ hm.2.1 (s.basis e0)
 have hf1:=bstate_write_e L hn host2 he2 base b0' _ (regValue (eReg L) b0') _ hf0 false
 have hf2:=bstate_write_e L hn host he base (writeBit b0' host2 false) _
  (regValue (eReg L) (writeBit b0' host2 false)) _ hf1 (s.basis host)
 have hf3:=bstate_write_e L hn cache ce base (writeBit (writeBit b0' host2 false) host (s.basis host)) _
  (regValue (eReg L) (writeBit (writeBit b0' host2 false) host (s.basis host))) _ hf2 false
 have hf4:=bstate_write_e L hn host2 he2 base t0 _ (regValue (eReg L) t0) _ hf3 (loanValue2 t0 c v u0 u1 u2 e0 host)
 have ev:regValue (eReg L) (writeBit t0 host2 (loanValue2 t0 c v u0 u1 u2 e0 host))=E:=by
  rw[restored2]
  apply Eq.trans _ h.2.1
  apply regValue_congr
  intro q hq
  by_cases q0:q=e0
  · subst q;simp[t0,b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  by_cases q2:q=host2
  · subst q;simp[writeBit]
  by_cases q1:q=host
  · subst q;simp[t0,b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13]
  by_cases qc:q=cache
  · subst q;simp[t0,b0',writeBit,Function.update_apply,n0_11,n0_12,n0_13,n0_14,n1_11,n1_12,n1_13,n1_14,n2_11,n2_12,n2_13,n2_14,n3_11,n3_12,n3_13,n3_14,n4_11,n4_12,n4_13,n4_14,n5_11,n5_12,n5_13,n5_14,n6_11,n6_12,n6_13,n6_14,n7_11,n7_12,n7_13,n7_14,n8_11,n8_12,n8_13,n8_14,n9_11,n9_12,n9_13,n9_14,n10_11,n10_12,n10_13,n10_14,n11_12,n11_13,n11_14,n12_11,n12_13,n12_14,n13_11,n13_12,n13_14,n14_11,n14_12,n14_13,hz]
  · simp only[t0,b0',writeBit,Function.update_apply,q0,q2,q1,qc,ite_false]
    rw[er q hq]
    simp[t,writeBit,Function.update_apply,q0,q2,q1,qc]
 simpa only[ev]using hf4
#print axioms wMidFullCCC0_step
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryOldE
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
theorem e0_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 (eReg L).headD 0∈eReg L:=head_mem _ (by simp[eReg_length L hw])

theorem armsCCC0_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 wires (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)))⊆oldE L ∧
 wires (wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)))⊆oldE L:=by
 have hh:((eReg L).headD 0)∈oldE L:=oldE_mem L hw _ (Or.inr (Or.inr (Or.inr (Or.inl (e0_mem L hw)))))
 have f:=(fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).support
 have i:=(invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).support
 constructor
 · intro q h;rcases Finset.mem_insert.mp (f h)with e|h
   · exact e ▸ hh
   · exact (armsCCC_oldE L hw).1 h
 · intro q h;rcases Finset.mem_insert.mp (i h)with e|h
   · exact e ▸ hh
   · exact (armsCCC_oldE L hw).2 h

theorem ends4L_oldE (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (g v v2:Wire):
 wires (prepare4L g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L))⊆insert g (insert v (insert v2 (oldE L))) ∧
 wires (finish4L g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L))⊆insert g (insert v (insert v2 (oldE L))):=by
 have lens:=mLens L hw
 have uMem (q:Wire) (h:q∈mU L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inl (List.mem_of_mem_drop h)))
 have rMem (q:Wire) (h:q∈mR L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inr (Or.inl (List.mem_of_mem_take h))))
 have eMem (q:Wire) (h:q∈eReg L):q∈oldE L:=oldE_mem L hw q (Or.inr (Or.inr (Or.inr (Or.inl h))))
 have hu0:=uMem _ (head_mem _ (by rw[lens.u];decide))
 have hu1:=uMem _ (bit1_mem _ (by rw[lens.u];decide))
 have hu2:=uMem _ (bit2_mem _ (by rw[lens.u];decide))
 have hu3:=uMem _ (bit3_mem _ (by rw[lens.u];decide))
 have hr0:=rMem _ (head_mem _ (by rw[lens.r];decide))
 have hr1:=rMem _ (bit1_mem _ (by rw[lens.r];decide))
 have hr2:=rMem _ (bit2_mem _ (by rw[lens.r];decide))
 have hr3:=rMem _ (bit3_mem _ (by rw[lens.r];decide))
 have he0:=eMem _ (head_mem _ (by simp[eReg_length L hw]))
 have hcache:=eMem _ (cache_mem L hw)
 have hh1:=eMem _ (host_mem L hw)
 have hh2:=eMem _ (host2_mem L hw)
 have carrier:([g,v,v2,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
    (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,
    cacheWire L,hostWire L,host2Wire L]:List Wire).toFinset⊆insert g (insert v (insert v2 (oldE L))):=by
  intro q h
  simp only[List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
   simp only[Finset.mem_insert] <;> tauto
 have cap:=ends4L_support g v v2 ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
   ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
   (cacheWire L) (hostWire L) (host2Wire L)
 exact ⟨cap.1.trans carrier,cap.2.trans carrier⟩

theorem e0_not_mem (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (hn:L.wires.Nodup):
 ¬WinArith.Mem (mR L) (mS L) (mZ L) (mC L) (mU L) L.core.cin (((eReg L).headD 0)):=by
 have ce:=e0_mem L hw
 have cp:=List.count_pos_iff.mpr (eReg_product L _ ce)
 have lc:=layoutCount L hn (((eReg L).headD 0))
 intro hm
 rcases hm with hi|hu|hr|hs|hz|hc
 · have cinPos:0<[L.core.productHigh,L.core.outHigh,L.core.workHigh,L.core.cin,L.core.normFlag,
     L.core.modFlag,L.core.sumCarry].count (((eReg L).headD 0)):=List.count_pos_iff.mpr (by rw[hi];simp)
   omega
 · exact (eReg_away L hn _ ce).2.2 (List.mem_of_mem_drop hu)
 · have :=List.count_pos_iff.mpr (mR_work L _ hr);omega
 · have :=List.count_pos_iff.mpr (mS_pad L _ hs);omega
 · have :=List.count_pos_iff.mpr (mZ_pad L _ hz);omega
 · have :=List.count_pos_iff.mpr (mC_pad L _ hc);omega

#print axioms armsCCC0_oldE
#print axioms ends4L_oldE
#print axioms e0_not_mem
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryMiddleCounts
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires

theorem midCCC0_patch (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths):
 Patch ((eReg L).headD 0) 4
  (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0)++
   (wCoreK L++wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0)))
  (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)++
   (wCoreK L++wInvCCC L (cacheWire L) (hostWire L) (host2Wire L))):=
 (fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0) (eU L)).app
  ((Patch.refl _ (wCoreK L)).app
   (invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) ((eReg L).headD 0) (eU L)))

theorem middle_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 toffoliCount (wMidFullCCC0 L c)+2 = toffoliCount (wMidFullCCC L c) ∧
 measurementCount (wMidFullCCC0 L c) = measurementCount (wMidFullCCC L c)+2 ∧
 Challenge.gateSlots (wMidFullCCC0 L c)+1 = Challenge.gateSlots (wMidFullCCC L c) := by
 have h := midCCC0_patch L hw
 have ht := h.t; have hm := h.m; have hs := h.slots
 simp only [toffoliCount_append,measurementCount_append,Challenge.gateSlots_append] at ht hm hs
 have prepT (a b c d e f g h i j k l m n o : Wire) : toffoliCount (prepare4L a b c d e f g h i j k l m n o) = 4 := (prepare4L_counts a b c d e f g h i j k l m n o).1
 have prepM (a b c d e f g h i j k l m n o : Wire) : measurementCount (prepare4L a b c d e f g h i j k l m n o) = 3 := (prepare4L_counts a b c d e f g h i j k l m n o).2.1
 have prepS (a b c d e f g h i j k l m n o : Wire) : Challenge.gateSlots (prepare4L a b c d e f g h i j k l m n o) = 41 := (prepare4L_counts a b c d e f g h i j k l m n o).2.2
 have finT (a b c d e f g h i j k l m n o : Wire) : toffoliCount (finish4L a b c d e f g h i j k l m n o) = 4 := (finish4L_counts a b c d e f g h i j k l m n o).1
 have finM (a b c d e f g h i j k l m n o : Wire) : measurementCount (finish4L a b c d e f g h i j k l m n o) = 4 := (finish4L_counts a b c d e f g h i j k l m n o).2.1
 have finS (a b c d e f g h i j k l m n o : Wire) : Challenge.gateSlots (finish4L a b c d e f g h i j k l m n o) = 34 := (finish4L_counts a b c d e f g h i j k l m n o).2.2
 have oldPT (a b c d e f g h i j k l : Wire) : toffoliCount (prepare3 a b c d e f g h i j k l) = 3 := rfl
 have oldPM (a b c d e f g h i j k l : Wire) : measurementCount (prepare3 a b c d e f g h i j k l) = 2 := rfl
 have oldPS (a b c d e f g h i j k l : Wire) : Challenge.gateSlots (prepare3 a b c d e f g h i j k l) = 30 := by simp [prepare3,loan2,SecondCarryLoan.prepare,prime,loan,prime2,majority,Challenge.gateSlots,Challenge.instructionSlots]
 have oldFT (a b c d e f g h i j k l : Wire) : toffoliCount (finish3 a b c d e f g h i j k l) = 3 := rfl
 have oldFM (a b c d e f g h i j k l : Wire) : measurementCount (finish3 a b c d e f g h i j k l) = 3 := rfl
 have oldFS (a b c d e f g h i j k l : Wire) : Challenge.gateSlots (finish3 a b c d e f g h i j k l) = 26 := by simp [finish3,SecondCarryLoan.finish,clear2,clear,restore,restore2,Challenge.gateSlots,Challenge.instructionSlots]
 simp only [wMidFullCCC0,wMidFullCCC,toffoliCount_append,measurementCount_append,Challenge.gateSlots_append,
  prepT,prepM,prepS,finT,finM,finS,oldPT,oldPM,oldPS,oldFT,oldFM,oldFS]
 exact ⟨by omega,by omega,by omega⟩
#print axioms middle_counts
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- LowBitCarryPhysical
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.LowBitCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop ControlLoan1589BFFold ECDSAAdd.Arithmetic.CuccaroStreamedSquareWideLayout
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem middle_physical (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hc : c ∉ L.wires) : GatePhysical (wMidFullCCC0 L c) := by
 have hp := ThirdCarryLoanDevelop.middle_physical L hw hn c hc
 simp only [wMidFullCCC,gatePhysical_append] at hp
 have geo := geometry15 L hw hn c hc
 have nc : ((eReg L).headD 0) ≠ cacheWire L := FourthCarryLoan.get_ne _ geo 11 12 (by simp) (by simp) (by decide)
 have n1 : ((eReg L).headD 0) ≠ hostWire L := FourthCarryLoan.get_ne _ geo 11 13 (by simp) (by simp) (by decide)
 have n2 : ((eReg L).headD 0) ≠ host2Wire L := FourthCarryLoan.get_ne _ geo 11 14 (by simp) (by simp) (by decide)
 have af : ((eReg L).headD 0) ∉ wires (wFwdCCC L (cacheWire L) (hostWire L) (host2Wire L)) := by
  intro h
  rcases Finset.mem_insert.mp ((fwdCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support h) with he|h
  · exact n2 he
  rcases Finset.mem_insert.mp ((fwdCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support h) with he|h
  · exact n1 he
  rcases Finset.mem_insert.mp ((fwdK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h) with he|h
  · exact nc he
  rcases WinArith.tFwdK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact e0_not_mem L hw hn hm
  · exact e0_ne_key L hw hn he
 have ai : ((eReg L).headD 0) ∉ wires (wInvCCC L (cacheWire L) (hostWire L) (host2Wire L)) := by
  intro h
  rcases Finset.mem_insert.mp ((invCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (eU L)).support h) with he|h
  · exact n2 he
  rcases Finset.mem_insert.mp ((invCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (eU L)).support h) with he|h
  · exact n1 he
  rcases Finset.mem_insert.mp ((invK_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (eU L)).support h) with he|h
  · exact nc he
  rcases WinArith.tInvK_mem (mLens L hw) (eU L) _ h with hm|he
  · exact e0_not_mem L hw hn hm
  · exact e0_ne_key L hw hn he
 have pf := (fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).phys af hp.2.1.1
 have pi := (invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).phys ai hp.2.1.2.2
 have ends := ends4L_physical c (bit1 L.core.high) (L.core.high.headD 0)
  ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L))
  ((eReg L).headD 0) (cacheWire L) (hostWire L) (host2Wire L) geo
 simp only [wMidFullCCC0,gatePhysical_append]
 exact ⟨ends.1,⟨pf,hp.2.1.2.1,pi⟩,ends.2⟩
#print axioms middle_physical
end ECDSAAdd.Entrant.LowBitCarryDevelop

end -- isolated Carry10 component

section
-- ParkCarry10Core
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry10Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop LowBitCarryDevelop ParkCarry7Develop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

theorem mid_sumCarry_free (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
 (c : Wire) (hc : c ∉ L.wires) : L.core.sumCarry ∉ wires (wMidFullCCC0 L c) := by
 have oe := ParkCarry7Develop.oldE_sumCarry_free L hw hn c hc
 have ng : L.core.sumCarry ≠ c := by
  intro h; apply hc
  simp [←h,CuccaroStreamedSquareWideLayout.wires,CuccaroStreamedSquareLayout.wires]
 have nv : L.core.sumCarry ≠ bit1 L.core.high := by
  intro h
  apply ParkCarryDevelop.sumCarry_away L hn
  have vy := ParkCarry8Develop.sourceHigh_in_y L hw
  rw [←h] at vy
  simp [ParkCarryDevelop.restWires,vy]
 have nv0:L.core.sumCarry≠L.core.high.headD 0:=by
  intro h
  apply ParkCarryDevelop.sumCarry_away L hn
  have vy:L.core.high.headD 0∈L.core.y:=List.mem_of_mem_drop (List.mem_of_mem_take
   (head_mem _ (by simp[CuccaroStreamedSquareLayout.high,hw.core.y])))
  rw[←h]at vy
  simp[ParkCarryDevelop.restWires,vy]
 have ends := ends4L_oldE L hw c (bit1 L.core.high) (L.core.high.headD 0)
 have arms := armsCCC0_oldE L hw
 have co : L.core.sumCarry ∉ wires (wCoreK L) := by
  have off := (b_wloop_sumCarry_free L hw hn c hc).2.1
  simp only [wires_append,Finset.mem_union,not_or] at off
  exact off.2.1
 have erase {P : Program} (sub : wires P ⊆ insert c (insert (bit1 L.core.high) (insert (L.core.high.headD 0) (oldE L)))) :
   L.core.sumCarry ∉ wires P := by
  intro h
  rcases Finset.mem_insert.mp (sub h) with e|h
  · exact ng e
  rcases Finset.mem_insert.mp h with e|h
  · exact nv e
  rcases Finset.mem_insert.mp h with e|h
  · exact nv0 e
  · exact oe h
 intro h
 simp only [wMidFullCCC0,wires_append,Finset.mem_union] at h
 rcases h with h|((h|(h|h))|h)
 · exact erase ends.1 h
 · exact oe (arms.1 h)
 · exact co h
 · exact oe (arms.2 h)
 · exact erase ends.2 h

def fold (L:CuccaroStreamedSquareWideLayout) (c:Wire):Program:=
 eAddLo L++(buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
  (wMidFullCCC0 L c++(unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry++
   (ParkCarryDevelop.program (eU L) L.core.sumCarry++eSubK L))))
def rebuild (L:CuccaroStreamedSquareWideLayout):Program:=eAddB L++(restore L++padM L 744)
def body (L:CuccaroStreamedSquareWideLayout)(c:Wire):Program:=
 measuredFoldQTq L (negP L)++(measuredFoldQTq L (rot128F L)++(fold L c++(eFoldTq L c++rebuild L)))

theorem body_frame (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (hn : L.wires.Nodup)
    (c : Wire) (hcw : c∉L.wires) (base : BasisState) (M : Nat) (hM : M<2^128)
    (hP : regValue L.core.product base=M^2) (hc : L.PairClean base) (hsum:base L.core.sumCarry=false) (O : Nat) (hO : O<SquareReduction.p)
    (hg : base c=false → M=0) (hSource:M=if base c then regValue L.core.high base else 0) :
    Triple (SquareFrame L.core.out base O) (body L c) (SquareFrame L.core.out base (bO4 (M^2) (base c) O)) := by
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
  have views := accA_views L hw base M hM hP
  have v1 : L.MeasuredFoldView base (negP L) := views (.inl (negP L)) (by simp [accAMix])
  have v2 : L.MeasuredFoldView base (rot128F L) := views (.inl (rot128F L)) (by simp [accAMix])
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
  have hcK:L.PairClean baseK := base_clean L hn base hc kap
  have productOff:L.core.sumCarry∉L.core.product := by
    intro h;apply sumCarry_away L hn;simp [restWires,h]
  have highOff:L.core.sumCarry∉hiReg L := by
    intro h;exact productOff (List.mem_of_mem_take (List.mem_of_mem_drop h))
  have hb1K:regValue (hiReg L) baseK=b1 := by
    dsimp only [baseK]
    rw [reg_update_off _ _ _ _ highOff]
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
  have off:=b_wloop_sumCarry_free L hw hn c hcw
  have loop:=cached_wloop_bstate_step L hw hn base hc hsum O2 (2^32*H+l'+2^128*K) O3
    (wMidFullCCC0 L c) wmBase off.1 (mid_sumCarry_free L hw hn c hcw) off.2.2
  have kc:=park_step L hw hn base hsum O3 (2^32*H+l') 0 (by omega) kap
  rw [kapNat] at kc
  have w3 := eSubK_step L hw hn baseK hcK O3 (2^32*H + l') 0 b1 (by omega) hb1K
  have tw : Triple (BState L base O2 b0 0) (fold L c) (BState L baseK O3 E1 0) :=
    by simpa only [fold,List.append_assoc] using k1.seq (loop.seq (kc.seq w3))
  -- eFoldTq
  have f1 := eFlip_step L hw hn baseK c hcw O3 E1 0
  have f2 := eCore_stepTq L hw hn baseK hcK O3 (flipE g E1) hO3
  have f3 := eFlip_step L hw hn baseK c hcw O4 (flipE g E1) 0
  rw [gc] at f1 f3
  rw [flipE_flipE] at f3
  have tf : Triple (BState L baseK O3 E1 0) (eFoldTq L c) (BState L baseK O4 E1 0) :=
    f1.seq (f2.seq f3)
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
  have r3:=restore_step L hw hn baseK hcK O4 0 H l' (b0%2^32) hH hl'
    (Nat.mod_lt _ (by positivity)) bit32 total
  have bb:2^32*H+b0%2^32=b0 := by dsimp [H];omega
  rw [resetBase,bb] at r3
  have rp := padM_step L hw hn base hc O4 b0 0 744
  have tr : Triple (BState L baseK O4 E1 0) (rebuild L) (BState L base O4 b0 0) :=
    r2.seq (r3.seq rp)
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
    (tf.seq tr)) conv0))
  rw [key] at all
  exact all

#print axioms mid_sumCarry_free
#print axioms body_frame
end ECDSAAdd.Entrant.ParkCarry10Develop

end -- isolated Carry10 component

section
-- ParkCarry10Metrics
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry10Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop LowBitCarryDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
theorem body_counts (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 toffoliCount (body L c)=4762 ∧ measurementCount (body L c)=5924:=by
 have base:=ParkCarry8Develop.body_counts L hw c
 have mid:=LowBitCarryDevelop.middle_counts L hw c
 have p:=padM_counts L 744
 have q:=padM_counts L 746
 simp only[body,fold,rebuild,ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,
  toffoliCount_append,measurementCount_append]at base ⊢
 exact ⟨by omega,by omega⟩

theorem body_slots (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire):
 Challenge.gateSlots (body L c)+3=Challenge.gateSlots (ParkCarry8Develop.body L c):=by
 have mid:=(LowBitCarryDevelop.middle_counts L hw c).2.2
 have p:=padM_slots L 744
 have q:=padM_slots L 746
 simp only[body,fold,rebuild,ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,
  Challenge.gateSlots_append]
 omega

theorem body_physical (L:CuccaroStreamedSquareWideLayout) (hw:L.Widths) (c:Wire)
 (hn:(c::L.wires).Nodup):GatePhysical (body L c):=by
 have hp:=ParkCarry8Develop.body_physical L hw c hn
 have nd:=(List.nodup_cons.mp hn).2
 have mid:=LowBitCarryDevelop.middle_physical L hw nd c (List.nodup_cons.mp hn).1
 have pad:=padM_physical L 744
 simp only[ParkCarry8Develop.body,ParkCarry8Develop.fold,ParkCarry8Develop.rebuild,gatePhysical_append]at hp
 simp only[body,fold,rebuild,gatePhysical_append]
 tauto

#print axioms body_counts
#print axioms body_slots
#print axioms body_physical
end ECDSAAdd.Entrant.ParkCarry10Develop

end -- isolated Carry10 component

section
-- ParkCarry10Hosting
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.ParkCarry10Develop
open Arithmetic Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold ParkCarryDevelop InverseCarryDevelop
attribute [local irreducible] ECDSAAdd.run ECDSAAdd.wires
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def hostedBody (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire) : Program :=
 body (hostLayout L rho) c

theorem hosted_eq (L : CuccaroStreamedSquareWideLayout) (rho : Equiv.Perm Wire) (c : Wire)
 (h : rho L.core.sumCarry = L.core.sumCarry) : hostedBody L rho c = body L c := by
 rw [hostedBody,ParkCarryDevelop.host_eq L rho h]

theorem hosted_counts (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
 toffoliCount (hostedBody L rho c) = 4762 ∧ measurementCount (hostedBody L rho c) = 5924 :=
 body_counts (hostLayout L rho) (host_widths L hw rho) c

theorem hosted_slots (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (rho : Equiv.Perm Wire) (c : Wire) :
 Challenge.gateSlots (hostedBody L rho c) = Challenge.gateSlots (body L c) := by
 have old := ParkCarry8Develop.hosted_slots L hw rho c
 have v := ParkCarry8Develop.bodyV_slots (hostLayout L rho) c (rho.symm (SecondCarryLoan.bit1 L.core.high))
 change Challenge.gateSlots (ParkCarry8Develop.bodyV (hostLayout L rho) c (rho.symm (SecondCarryLoan.bit1 L.core.high))) =
  Challenge.gateSlots (ParkCarry8Develop.body L c) at old
 have a := body_slots (hostLayout L rho) (host_widths L hw rho) c
 have b := body_slots L hw c
 change Challenge.gateSlots (body (hostLayout L rho) c) = Challenge.gateSlots (body L c)
 omega
#print axioms hosted_eq
#print axioms hosted_counts
#print axioms hosted_slots
end ECDSAAdd.Entrant.ParkCarry10Develop

end -- isolated Carry10 component

section
-- Carry10BodyRefined
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Entrant
namespace ECDSAAdd.Entrant.Carry10BodyRefined
open Arithmetic.CuccaroStreamedSquareWideLayout ControlLoan1589BFFold InverseCarryDevelop
open CarryWindowCache SecondCarryLoan ThirdCarryLoanDevelop FourthCarryLoanDevelop LowBitCarryDevelop Carry9BodySubset
attribute [local irreducible] ECDSAAdd.wires ECDSAAdd.run
set_option maxHeartbeats 8000000
set_option maxRecDepth 30000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem body_refined (L : CuccaroStreamedSquareWideLayout) (hw : L.Widths) (c : Wire) :
 wires (ParkCarry10Develop.body L c)⊆insert (L.core.high.headD 0) (wires (ParkCarry8Develop.body L c)) := by
 let v := L.core.high.headD 0
 have same {P : Program} (hp : wires P⊆wires (ParkCarry8Develop.body L c)) :
  wires P⊆insert v (wires (ParkCarry8Develop.body L c)) := fun _ h=>Finset.mem_insert_of_mem (hp h)
 have roles:=old_prepare L c
 have extras:=new_roles L hw c
 have carrier : [c,bit1 L.core.high,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L].toFinset
  ⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  intro q h
  simp only [List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with e|e|e|e|e|e|e|e|e|e|e|e|e|e|e
  all_goals subst q
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.1
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem extras.2.1
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
  · exact Finset.mem_insert_of_mem (roles (by simp))
 have ends:=ends4L_support c (bit1 L.core.high) v ((mU L).headD 0) (bit1 (mU L)) (bit2 (mU L)) (bit3 (mU L))
  ((mR L).headD 0) (bit1 (mR L)) (bit2 (mR L)) (bit3 (mR L)) ((eReg L).headD 0)
  (cacheWire L) (hostWire L) (host2Wire L)
 have endEmbed {P : Program} (hp : wires P⊆[c,bit1 L.core.high,v,(mU L).headD 0,bit1 (mU L),bit2 (mU L),bit3 (mU L),
  (mR L).headD 0,bit1 (mR L),bit2 (mR L),bit3 (mR L),(eReg L).headD 0,cacheWire L,hostWire L,host2Wire L].toFinset) :
  wires P⊆insert v (wires (ParkCarry8Develop.body L c)) := hp.trans carrier
 have arms :
  wires (wFwdCCCC L (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)))⊆insert v (wires (ParkCarry8Develop.body L c)) ∧
  wires (wInvCCCC L (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)))⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  have f:=(fwdCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).support
  have i:=(invCCCC_patch (cin:=L.core.cin) (mLens L hw) (cacheWire L) (hostWire L) (host2Wire L) (((eReg L).headD 0)) (eU L)).support
  constructor
  · intro q h
    rcases Finset.mem_insert.mp (f h) with e|h
    · subst q;exact Finset.mem_insert_of_mem (roles (by simp))
    · exact same (Carry9OldParts.old_fwd L c) h
  · intro q h
    rcases Finset.mem_insert.mp (i h) with e|h
    · subst q;exact Finset.mem_insert_of_mem (roles (by simp))
    · exact same (Carry9OldParts.old_inv L c) h
 have mid : wires (wMidFullCCC0 L c)⊆insert v (wires (ParkCarry8Develop.body L c)) := by
  rw [wMidFullCCC0,wires_append]
  refine Finset.union_subset_iff.mpr ⟨endEmbed ends.1,?_⟩
  rw [wires_append]
  refine Finset.union_subset_iff.mpr ⟨?_,endEmbed ends.2⟩
  rw [wires_append]
  refine Finset.union_subset_iff.mpr ⟨arms.1,?_⟩
  rw [wires_append]
  exact Finset.union_subset_iff.mpr ⟨same (Carry9OldParts.old_core L c),arms.2⟩
 have pad : wires (padM L 744)⊆wires (padM L 746) := by
  have hp : padM L 746=padM L 744++padM L 2 := by
   change List.replicate (744+2) (Instr.measureX (eKw L) [] [])=
    List.replicate 744 (Instr.measureX (eKw L) [] [])++List.replicate 2 (Instr.measureX (eKw L) [] [])
   rw [List.replicate_add]
  rw [hp,wires_append]
  exact Finset.subset_union_left
 intro q h
 simp only [ParkCarry10Develop.body,ParkCarry10Develop.fold,ParkCarry10Develop.rebuild,
  wires_append,Finset.mem_union,or_assoc] at h
 rcases h with h|h|h|h|h|h|h|h|h|h|h|h
 · exact same (P:=measuredFoldQTq L (negP L)) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=measuredFoldQTq L (rot128F L)) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddLo L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=buildCached (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact mid h
 · exact same (P:=unbuildConsumed (accReg L) (accZ L) (accBank L) L.core.cin (hiReg L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.program (eU L) L.core.sumCarry)
    (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eSubK L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.fold,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eFoldTq L c) (by intro q h;simp only [ParkCarry8Develop.body,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=eAddB L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=ParkCarryDevelop.restore L) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) h
 · exact same (P:=padM L 746) (by intro q h;simp only [ParkCarry8Develop.body,ParkCarry8Develop.rebuild,wires_append,Finset.mem_union];tauto) (pad h)

#print axioms body_refined
end ECDSAAdd.Entrant.Carry10BodyRefined

end -- isolated Carry10 component
