import ECDSAAdd.Submission.Entrant.MappedTopZero
import ECDSAAdd.Arithmetic.NativeFirstDirectProgram
open ECDSAAdd ECDSAAdd.Arithmetic ECDSAAdd.Challenge
namespace ECDSAAdd.Entrant.HAddTopZero
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

def zbit : MappedBit := {wire := none, flip := false}
def pbit (p : Wire) : MappedBit := {wire := some p, flip := false}
def oldTop (p y c Y z : Wire) : Program :=
  MappedTopZero.mLeaf zbit (pbit p) y c Y z
def newTop (p y c Y : Wire) : Program :=
  [.CX p Y, .measureX Y [] [.CZ y c], .CX c y]
def ready (p y c Y : Wire) (b : BasisState) : Prop :=
  (b Y ^^ b p ^^ (b y && b c)) = false

theorem top_eq (p y c Y z : Wire) (nd : [p,y,c,Y,z].Nodup) (s : State)
  (m n : List Bool) (hz : s.basis z=false) (hr : ready p y c Y s.basis) :
  run (oldTop p y c Y z) m s = run (newTop p y c Y) n s := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hpy,hpc,hpY,hpz⟩,⟨hyc,hyY,hyz⟩,⟨hcY,hcz⟩,hYz⟩ := nd
  have hzY : z ≠ Y := Ne.symm hYz
  cases s with
  | mk ph b =>
    cases hp : b p <;> cases hy : b y <;> cases hc : b c <;>
      cases hY : b Y <;> cases hm : m.headD false <;> cases hn : n.headD false <;>
      simp_all [ready,oldTop,newTop,MappedTopZero.mLeaf,zbit,pbit,mappedMajority,
        mappedEraseCarry,mappedSum,run,measureAndCorrect,correct,writeBit,Function.update,
        hp,hy,hc,hY,hz,hm,hn,hzY,Bool.xor_assoc,ne_comm]
    all_goals try simp_all only [show (z=Y)=False from propext (iff_false_intro (Ne.symm hYz)), decide_false, Bool.xor_false, Bool.false_xor, true_and]
    all_goals funext q
    all_goals by_cases hqz : q=z <;> by_cases hqY : q=Y <;> by_cases hqy : q=y <;> simp_all [Function.update]

theorem old_high (p y c Y z : Wire) (nd : [p,y,c,Y,z].Nodup) (s : State) (m : List Bool)
    (clean : s.basis z=false) :
    (run (oldTop p y c Y z) m s).basis Y = (s.basis Y ^^ s.basis p ^^ (s.basis y && s.basis c)) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  obtain ⟨⟨hpy,hpc,hpY,hpz⟩,⟨hyc,hyY,hyz⟩,⟨hcY,hcz⟩,hYz⟩ := nd
  cases s with
  | mk ph b =>
    cases hp : b p <;> cases hy : b y <;> cases hc : b c <;> cases hY : b Y <;>
      cases hm : m.headD false <;>
      simp_all [oldTop,MappedTopZero.mLeaf,zbit,pbit,mappedMajority,mappedEraseCarry,
        mappedSum,run,measureAndCorrect,correct,writeBit,Function.update,ne_comm]
    all_goals try simp_all only [show (z=Y)=False from propext (iff_false_intro (Ne.symm hYz)), decide_false]

private theorem cat (p q : Program) (m : List Bool) (s : State) :
    run (p++q) m s=run q (m.drop (measurementCount p)) (run p m s) := by
  rw [run_append,run_take]

theorem whole_top (P R : Program) (p y c Y z : Wire) (nd : [p,y,c,Y,z].Nodup)
    (s : State) (m : List Bool)
    (clean : s.basis z=false) (hzP : z∉wires P) (hYR : Y∉wires R)
    (top : (run (P++oldTop p y c Y z++R) [] s).basis Y=false) :
    run (P++oldTop p y c Y z++R) m s=run (P++newTop p y c Y++R) m s := by
  let t:=run P m s
  let t0:=run P [] s
  have tc : t.basis z=false := (run_preserves_outside P m s z hzP).trans clean
  have tc0 : t0.basis z=false := (run_preserves_outside P [] s z hzP).trans clean
  have top0 : (run (oldTop p y c Y z) [] t0).basis Y=false := by
    have h:=top
    simp only [cat,List.drop_nil] at h
    rw [run_preserves_outside R [] _ Y hYR] at h
    exact h
  have pb : t.basis=t0.basis := run_basis_records P s s m [] rfl
  have rdy : ready p y c Y t.basis := by
    unfold ready
    rw [pb,←old_high p y c Y z nd t0 [] tc0]
    exact top0
  have eqn:=top_eq p y c Y z nd t (m.drop (measurementCount P))
    (m.drop (measurementCount P)) tc rdy
  have co : measurementCount (oldTop p y c Y z)=1 := by rfl
  have cn : measurementCount (newTop p y c Y)=1 := by rfl
  simpa only [cat,measurementCount_append,co,cn,List.drop_drop,Nat.add_comm,t] using
    congrArg (run R ((m.drop (measurementCount P)).drop 1)) eqn

open MappedTopZero AdderSpineBridgeResearch RecordedQuantum

def oldT (D : List MappedBit) (w : Nat → Wire) : Program :=
  mappedAdd D (wireBlock w 4 253) (wireBlock w 1540 252) (w 1797)
def topP (D : List MappedBit) (w : Nat → Wire) : Program :=
  mPrefix (D.take 251) (wireBlock w 4 251) (wireBlock w 1540 251) (w 1797)
def topR (D : List MappedBit) (w : Nat → Wire) : Program :=
  mSuffix (D.take 251) (wireBlock w 4 251) (wireBlock w 1540 251) (w 1797)
def topT (D : List MappedBit) (w : Nat → Wire) (p : Wire) : Program :=
  topP D w++newTop p (w 255) (w 1790) (w 256)++topR D w

theorem oldT_split (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=253) (hdrop : D.drop 251=[zbit,pbit p]) :
    oldT D w=topP D w++oldTop p (w 255) (w 1790) (w 256) (w 1791)++topR D w := by
  have dT : D=D.take 251++[zbit,pbit p] := by rw [←hdrop,List.take_append_drop]
  have yT : wireBlock w 4 253=wireBlock w 4 251++[w 255,w 256] := by
    rw [←wireBlock_append w 4 251 2]; rfl
  have cT : wireBlock w 1540 252=wireBlock w 1540 251++[w 1791] := by
    rw [←wireBlock_append w 1540 251 1]; rfl
  have lc : lastCarry (wireBlock w 1540 251) (w 1797)=w 1790 := by
    rw [←wireBlock_append w 1540 250 1,lastCarry_cat]; rfl
  have l1 : (D.take 251).length=(wireBlock w 4 251).length := by simp [wireBlock_length,hlen]
  have l2 : (D.take 251).length=(wireBlock w 1540 251).length := by simp [wireBlock_length,hlen]
  rw [oldT,dT,yT,cT,madd_split _ _ _ _ _ _ _ _ _ l1 l2,lc]
  simp [topP,topR,oldTop,List.take_append,hlen,List.append_assoc]

theorem top_counts (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=253) (hdrop : D.drop 251=[zbit,pbit p]) :
    toffoliCount (topT D w p)+1=toffoliCount (oldT D w) ∧
      measurementCount (topT D w p)=measurementCount (oldT D w) ∧
      gateSlots (topT D w p)+2=gateSlots (oldT D w) := by
  rw [oldT_split D w p hlen hdrop,topT]
  simp only [toffoliCount_append,measurementCount_append,gateSlots_append]
  simp [oldTop,newTop,MappedTopZero.mLeaf,zbit,pbit,mappedMajority,mappedSum,mappedEraseCarry,
    toffoliCount,measurementCount,gateSlots,instructionSlots]
  omega

theorem newTop_wires (p y c Y z : Wire) : wires (newTop p y c Y)⊆wires (oldTop p y c Y z) := by
  intro q hq
  simp [newTop,oldTop,MappedTopZero.mLeaf,zbit,pbit,mappedMajority,mappedSum,mappedEraseCarry,
    wires_append,wires,Instr.wires,correctionWires] at hq ⊢
  tauto

theorem newTop_physical (p y c Y : Wire) (nd : [p,y,c,Y].Nodup) : GatePhysical (newTop p y c Y) := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd
  simp_all [newTop,GatePhysical,PhysicalInstr,ProperGate,ne_comm]

theorem top_wires (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=253) (hdrop : D.drop 251=[zbit,pbit p]) :
    wires (topT D w p)⊆wires (oldT D w) := by
  rw [oldT_split D w p hlen hdrop,topT]
  simp only [wires_append]
  exact Finset.union_subset_union
    (Finset.union_subset_union (Finset.Subset.refl _) (newTop_wires _ _ _ _ _))
    (Finset.Subset.refl _)

theorem top_physical (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=253) (hdrop : D.drop 251=[zbit,pbit p])
    (nd : [p,w 255,w 1790,w 256].Nodup) (h : GatePhysical (oldT D w)) :
    GatePhysical (topT D w p) := by
  rw [oldT_split D w p hlen hdrop] at h
  rw [topT]
  simp only [gatePhysical_append] at h ⊢
  exact ⟨⟨h.1.1,newTop_physical _ _ _ _ nd⟩,h.2⟩

theorem top_run (D : List MappedBit) (w : Nat → Wire) (p : Wire)
    (hlen : D.length=253) (hdrop : D.drop 251=[zbit,pbit p])
    (hDw : ∀ q∈mappedWires D,q=p)
    (inj : ∀ i j,i<1798 → j<1798 → w i=w j → i=j)
    (hpi : p=w 1028)
    (s : State) (m : List Bool) (clean : s.basis (w 1791)=false)
    (top : (run (oldT D w) [] s).basis (w 256)=false) :
    run (topT D w p) m s=run (oldT D w) m s := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (h : i≠j) : w i≠w j :=
    fun e => h (inj i j hi hj e)
  have hp (i : Nat) (hi : i<1798) (h : i≠1028) : p≠w i := by
    rw [hpi]; exact ne 1028 i (by omega) hi (Ne.symm h)
  have nd : [p,w 255,w 1790,w 256,w 1791].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    refine ⟨⟨hp 255 (by omega) (by omega),hp 1790 (by omega) (by omega),hp 256 (by omega) (by omega),hp 1791 (by omega) (by omega)⟩,
      ⟨ne _ _ (by omega) (by omega) (by omega),ne _ _ (by omega) (by omega) (by omega),
        ne _ _ (by omega) (by omega) (by omega)⟩,
      ⟨ne _ _ (by omega) (by omega) (by omega),ne _ _ (by omega) (by omega) (by omega)⟩,
      ne _ _ (by omega) (by omega) (by omega)⟩
  have bitsW (q : Wire) (hq : q∈mappedWires (D.take 251)) : q=p := by
    apply hDw
    simp only [mappedWires,List.mem_flatMap] at hq ⊢
    obtain ⟨b,hb,hqb⟩ := hq
    exact ⟨b,List.mem_of_mem_take hb,hqb⟩
  have hzP : w 1791∉wires (topP D w) := by
    intro h
    have h' := List.mem_toFinset.mp (mPrefix_support _ _ _ _ h)
    simp only [List.mem_cons,List.mem_append] at h'
    rcases h' with e|(e|e)|e
    · exact ne _ _ (by omega) (by omega) (by omega) e
    · exact hp 1791 (by omega) (by omega) (bitsW _ e).symm
    · obtain ⟨i,h1,h2,h3⟩ := mem_block w 4 251 _ e
      exact absurd (inj i 1791 (by omega) (by omega) h3) (by omega)
    · obtain ⟨i,h1,h2,h3⟩ := mem_block w 1540 251 _ e
      exact absurd (inj i 1791 (by omega) (by omega) h3) (by omega)
  have hYR : w 256∉wires (topR D w) := by
    intro h
    have h' := List.mem_toFinset.mp (mSuffix_support _ _ _ _ h)
    simp only [List.mem_cons,List.mem_append] at h'
    rcases h' with e|(e|e)|e
    · exact ne _ _ (by omega) (by omega) (by omega) e
    · exact hp 256 (by omega) (by omega) (bitsW _ e).symm
    · obtain ⟨i,h1,h2,h3⟩ := mem_block w 4 251 _ e
      exact absurd (inj i 256 (by omega) (by omega) h3) (by omega)
    · obtain ⟨i,h1,h2,h3⟩ := mem_block w 1540 251 _ e
      exact absurd (inj i 256 (by omega) (by omega) h3) (by omega)
  have top' : (run (topP D w++oldTop p (w 255) (w 1790) (w 256) (w 1791)++topR D w) [] s).basis (w 256)=false := by
    rw [←oldT_split D w p hlen hdrop]; exact top
  rw [oldT_split D w p hlen hdrop,topT]
  exact (whole_top (topP D w) (topR D w) p (w 255) (w 1790) (w 256) (w 1791) nd s m clean hzP hYR top').symm

open NativeFirstDirect

theorem hBits_drop (w : Nat → Wire) : (hBits w true).drop 251=[zbit,pbit (w 1028)] := by
  have e : (List.range 253).drop 251 = [251,252] := by decide
  have t1 : (2^256-hConstant).testBit (251+3) = false := by unfold hConstant ECDSAAdd.p; decide
  have t2 : (2^256-hConstant).testBit (252+3) = true := by unfold hConstant ECDSAAdd.p; decide
  rw [hBits, ← List.map_drop, e]
  simp only [List.map_cons,List.map_nil, ↓reduceIte,Bool.false_eq_true,t1,t2,zbit,pbit]

theorem hBits_wires (w : Nat → Wire) (q : Wire) (hq : q∈mappedWires (hBits w true)) : q=w 1028 := by
  simp only [mappedWires,hBits,List.mem_flatMap,List.mem_map] at hq
  obtain ⟨b,⟨i,hi,rfl⟩,hb⟩ := hq
  split_ifs at hb <;> simpa using hb


def hAddTop (w : Nat → Wire) : Program := topT (hBits w true) w (w 1028)

theorem oldT_hAdd (w : Nat → Wire) : oldT (hBits w true) w=hAdd w true := rfl

theorem hAddTop_counts (w : Nat → Wire) :
    toffoliCount (hAddTop w)=251 ∧ measurementCount (hAddTop w)=252 ∧
    gateSlots (hAddTop w)+2=gateSlots (hAdd w true) := by
  have a:=top_counts (hBits w true) w (w 1028) (hBits_length w true) (hBits_drop w)
  have b:=hAdd_counts w true
  simp only [oldT_hAdd] at a
  simp only [hAddTop]
  omega

theorem hAddTop_wires (w : Nat → Wire) : wires (hAddTop w)⊆wires (hAdd w true) := by
  simpa only [hAddTop,oldT_hAdd] using top_wires (hBits w true) w (w 1028) (hBits_length w true) (hBits_drop w)

theorem hAddTop_physical (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (h : GatePhysical (hAdd w true)) : GatePhysical (hAddTop w) := by
  have ne (i j : Nat) (hi : i<1798) (hj : j<1798) (e : i≠j) : w i≠w j := by
    intro q
    apply e
    exact skywalkPool_index_inj w hn i j hi hj q
  have nd : [w 1028,w 255,w 1790,w 256].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
      not_or,not_false_eq_true,and_true]
    exact ⟨⟨ne _ _ (by omega) (by omega) (by omega),ne _ _ (by omega) (by omega) (by omega),
      ne _ _ (by omega) (by omega) (by omega)⟩,
      ⟨ne _ _ (by omega) (by omega) (by omega),ne _ _ (by omega) (by omega) (by omega)⟩,
      ne _ _ (by omega) (by omega) (by omega)⟩
  exact top_physical (hBits w true) w (w 1028) (hBits_length w true) (hBits_drop w) nd h

attribute [local irreducible] run wires hAdd topT oldT

theorem hAddTop_run (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (clean : s.basis (w 1791)=false)
    (top : (run (hAdd w true) [] s).basis (w 256)=false) :
    run (hAddTop w) m s=run (hAdd w true) m s := by
  have inj (i j : Nat) (hi : i<1798) (hj : j<1798) (e : w i=w j) : i=j :=
    skywalkPool_index_inj w hn i j hi hj e
  have top' : (run (oldT (hBits w true) w) [] s).basis (w 256)=false := by
    rw [oldT_hAdd]; exact top
  have r := top_run (hBits w true) w (w 1028) (hBits_length w true) (hBits_drop w)
    (hBits_wires w) inj rfl s m clean top'
  simpa only [hAddTop,oldT_hAdd] using r
end ECDSAAdd.Entrant.HAddTopZero
