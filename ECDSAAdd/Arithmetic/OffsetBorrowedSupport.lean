import ECDSAAdd.Arithmetic.OffsetBorrowedControlledPort
import ECDSAAdd.Arithmetic.DirectSkywalkFieldSupport
import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportInteger
import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportUnary
import ECDSAAdd.Arithmetic.BorrowedSkywalkCompactSupportReplay
import ECDSAAdd.Arithmetic.BalancedInverseTranscriptKernelSupport
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetSupport
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.OffsetBorrowedSupport
open Secp256k1 BorrowedSkywalkCompactSupport
attribute [local irreducible] BalancedCircuit.coreProgram BalancedCircuit.program
attribute [local irreducible] BalancedInverse.program OffsetBorrowedField.program
attribute [local irreducible] OffsetBorrowedInverse.program BalancedCleanupOffset.program
attribute [local irreducible] wireBlock majority eraseCarry mappedMajority mappedSum mappedEraseCarry
attribute [local irreducible] dblInPlace halfInPlace copyRegister swapRegisters transcriptSelectWindow
attribute [local irreducible] literalSkywalkSeed literalSkywalkUnseed narrowSkywalkRoutedLoop narrowSkywalkRoutedUnloop

/-- Induction over actual emitted heads includes every measured correction. -/
theorem chainSupport (bits : List MappedBit) (xs ys cs ds : List Wire)
    (ci cb t : Wire) (W : Finset Wire)
    (hbits : ∀q∈mappedWires bits,q∈W) (hx : ∀q∈xs,q∈W) (hy : ∀q∈ys,q∈W)
    (hc : ∀q∈cs,q∈W) (hd : ∀q∈ds,q∈W) (hci : ci∈W) (hcb : cb∈W) (ht : t∈W) :
    wires (BalancedCleanupOffset.chain bits xs ys cs ds ci cb t)⊆W := by
  induction bits generalizing xs ys cs ds ci cb with
  | nil =>
    cases xs <;> cases ys <;> cases cs <;> cases ds <;>
      simp [BalancedCleanupOffset.chain,flipBelow_wires,wires,Finset.subset_iff,hcb,ht]
  | cons b bits ih =>
    cases xs with
    | nil => simp [BalancedCleanupOffset.chain,wires]
    | cons a xs =>
      cases ys with
      | nil => simp [BalancedCleanupOffset.chain,wires]
      | cons y ys =>
        cases cs with
        | nil => simp [BalancedCleanupOffset.chain,wires]
        | cons c cs =>
          cases ds with
          | nil => simp [BalancedCleanupOffset.chain,wires]
          | cons d ds =>
            have ha := hx a (by simp)
            have hyy := hy y (by simp)
            have hcc := hc c (by simp)
            have hdd := hd d (by simp)
            have source (q : Wire) (hq : q∈b.wire.toList) : q∈W :=
              hbits q (List.mem_append_left _ hq)
            have headPool : (b.wire.toList++[y,ci,c]).toFinset⊆W := by
              intro q hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
              rcases hq with hq|rfl|rfl|rfl
              · exact source q hq
              · exact hyy
              · exact hci
              · exact hcc
            have sum : (b.wire.toList++[y,ci]).toFinset⊆W := by
              intro q hq
              apply headPool
              simpa only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] using
                (show q∈b.wire.toList ∨ q=y ∨ q=ci ∨ q=c from by
                  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
                  tauto)
            have recurse := ih xs ys cs ds c d
              (fun q hq => hbits q (List.mem_append_right _ hq))
              (fun q hq => hx q (List.mem_cons_of_mem _ hq))
              (fun q hq => hy q (List.mem_cons_of_mem _ hq))
              (fun q hq => hc q (List.mem_cons_of_mem _ hq))
              (fun q hq => hd q (List.mem_cons_of_mem _ hq)) hcc hdd
            have small : wires (majority a y cb d)⊆W ∧ wires (eraseCarry a y cb d)⊆W ∧
                wires [.X y]⊆W := by
              simp [majority,eraseCarry,wires,Instr.wires,correctionWires,Finset.subset_iff,
                ha,hyy,hcb,hdd]
            have bit := mappedBit_wires b y ci c
            simp only [BalancedCleanupOffset.chain,wires_append,Finset.union_subset_iff,and_assoc]
            exact ⟨bit.1.trans headPool,bit.2.2.trans sum,small.2.2,small.1,recurse,
              small.2.1,small.2.2,bit.2.2.trans sum,bit.2.1.trans headPool⟩

private theorem coreSub (L : BalancedCircuit.Layout) :
    wires (BalancedCircuit.coreProgram L)⊆wires (BalancedCircuit.program L) := by
  intro q hq
  simp only [BalancedCircuit.program_eq_core,wires_append,Finset.mem_union]
  exact Or.inl (Or.inl hq)

private theorem tailSub (L : BalancedCircuit.Layout) :
    wires (OffsetBorrowedInverse.tail L)⊆wires (BalancedInverse.program L) := by
  have eq : BalancedInverse.program L=[.CX L.ymsb L.sourceGuard]++
      BalancedInverse.recoverParity L++OffsetBorrowedInverse.tail L := by
    simp only [BalancedInverse.program,OffsetBorrowedInverse.tail,List.append_assoc]
  intro q hq
  simp only [eq,wires_append,Finset.mem_union]
  exact Or.inr hq

theorem offsetSupport (L : BalancedCleanupOffset.Layout) (hw : L.Widths) :
    wires (BalancedCleanupOffset.program L)⊆L.wires.toFinset := by
  let W := L.wires.toFinset
  have member (q : Wire) : q∈W ↔
      q∈[L.sourceGuard,L.cout,L.minus,L.plus,L.parity,L.sign,L.lower,L.one,L.rmsb,L.ymsb,L.r0] ∨
      q∈L.rtail ∨ q∈L.ylow ∨ q∈L.carry ∨ q∈L.offsetCarry := by
    simp [W,BalancedCleanupOffset.Layout.wires,BalancedCircuit.Layout.wires,
      BalancedCleanup.Layout.wires,or_assoc]
  have data (q : Wire) (h : q∈L.y++L.r++L.carry++L.offsetCarry) : q∈W := by
    simp only [BalancedCleanup.Layout.y,BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,
      List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rw [member]
    simp only [List.mem_cons,List.not_mem_nil,or_false]
    tauto
  have own : L.toCircuit.toLayout.wires.toFinset⊆W := by
    intro q hq
    simp only [W,BalancedCleanupOffset.Layout.wires,BalancedCircuit.Layout.wires,
      List.mem_toFinset,List.mem_append] at ⊢
    exact Or.inl (Or.inr (List.mem_toFinset.mp hq))
  have sgSub : wires (BalancedCleanup.prepareSign L.toCircuit.toLayout)⊆
      wires (BalancedCleanup.program L.toCircuit.toLayout) := by
    rw [BalancedCleanup.program,wires_append]
    exact Finset.subset_union_left
  have sg := sgSub.trans ((BalancedCleanup.support L.toCircuit.toLayout hw.1).trans own)
  have vw : wires (BalancedCleanupOffset.view L)⊆W := by
    intro q hq
    have h := BalancedCleanupOffset.view_support L hw hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at h
    rcases h with rfl|rfl|h|h
    · simp [member]
    · simp [member]
    · exact data q (by simp [h])
    · exact data q (by simp [h])
  have ch := chainSupport (BalancedCleanupOffset.offsetBits L) L.y L.r L.offsetCarry L.carry
    L.one L.cout L.parity W
    (fun q hq => by rw [BalancedCleanupOffset.offsetSources L q hq]; simp [member])
    (fun q hq => data q (by simp [hq])) (fun q hq => data q (by simp [hq]))
    (fun q hq => data q (by simp [hq])) (fun q hq => data q (by simp [hq]))
    (by simp [member]) (by simp [member]) (by simp [member])
  have c : wires [.X L.cout]⊆W := by simp [wires,Instr.wires,Finset.subset_iff,member]
  simp only [BalancedCleanupOffset.program,wires_append,wires_reverse,Finset.union_subset_iff,and_assoc]
  exact ⟨sg,vw,c,ch,c,vw,sg⟩


theorem offsetSites (w : Nat → Wire) (sign : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hs : sign∈W) :
    (OffsetCleanupBorrowedCaller.layout w sign).wires.toFinset⊆W := by
  have native := kernelSites w sign W hW hs
  have small (i : Nat) (hi : i < 1798) : w i∈W :=
    hW (List.mem_toFinset.mpr (index_mem w i (Or.inl hi)))
  have bank := blockSites w 512 253 W hW (by intro i _ hi; exact Or.inl (by omega))
  intro q hq
  have h := List.mem_toFinset.mp hq
  change q∈([w 765,w 1026,w 0,w 1]++(balancedSharedPorts w sign).toLayout.wires)++
    OffsetCleanupBorrowedCaller.carry w at h
  simp only [List.mem_append] at h
  rcases h with (h|h)|h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl
    all_goals exact small _ (by omega)
  · exact native (List.mem_toFinset.mpr (List.mem_append_right _ h))
  · simp only [OffsetCleanupBorrowedCaller.carry,List.mem_append] at h
    rcases h with h|h
    · exact bank (List.mem_toFinset.mpr h)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl
      all_goals exact small _ (by omega)

private theorem cxSupport (L : BalancedCircuit.Layout) :
    wires [.CX L.ymsb L.sourceGuard]⊆L.wires.toFinset := by
  simp [wires,Instr.wires,Finset.subset_iff,BalancedCircuit.Layout.wires,
    BalancedCleanup.Layout.wires]

theorem fieldPrograms (w : Nat → Wire) (sign : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hs : sign∈W) :
    wires (OffsetBorrowedField.program w sign)⊆W ∧
    wires (OffsetBorrowedInverse.program w sign)⊆W := by
  let L := balancedSharedPorts w sign
  have native := kernelSites w sign W hW hs
  have core := (coreSub L).trans ((balancedSharedPorts_support w sign).trans native)
  have tail := (tailSub L).trans
    ((BalancedInverse.support L (balancedSharedPorts_widths w sign)).trans native)
  have off := (BalancedCleanupOffsetZero.support _ (OffsetCleanupBorrowedCaller.widths w sign)).trans
    (offsetSites w sign W hW hs)
  have forwardOff := (TerminalParityOffset.support_old _ (OffsetCleanupBorrowedCaller.widths w sign)).trans off
  have cx := (cxSupport L).trans native
  simp only [OffsetBorrowedField.program,OffsetBorrowedInverse.program,
    OffsetBorrowedInverse.recoverParity,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨core,forwardOff,cx,cx,off,tail⟩

private theorem swapSupport (L : BalancedCircuit.Layout) (eff : Wire) (W : Finset Wire)
    (hw : L.Widths) (own : L.wires.toFinset⊆W) (he : eff∈W) :
    wires (swapRegisters eff L.r L.y)⊆W := by
  have widths := BalancedCleanup.widths L.toLayout hw
  have sw := swapRegisters_wires eff L.r L.y (widths.2.1.trans widths.2.2.1.symm)
  intro q hq
  have h := sw hq
  simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h
  rcases h with rfl|h|h
  · exact he
  all_goals
    apply own
    simp only [BalancedCircuit.Layout.wires,BalancedCleanup.Layout.wires,
      BalancedCleanup.Layout.r,BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,
      List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto

theorem bodies (w : Nat → Wire) (sign eff : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hs : sign∈W) (he : eff∈W) :
    wires (OffsetBorrowedCanonical.body w sign eff)⊆W ∧
    wires (OffsetBorrowedInverseCanonical.body w sign eff)⊆W := by
  have field := fieldPrograms w sign W hW hs
  have sw := swapSupport (balancedSharedPorts w sign) eff W (balancedSharedPorts_widths w sign)
    (kernelSites w sign W hW hs) he
  have xx : wires [.X sign]⊆W := by simp [wires,Instr.wires,Finset.subset_iff,hs]
  simp only [OffsetBorrowedCanonical.body,OffsetBorrowedInverseCanonical.body,
    OffsetBorrowedInverseCanonical.double,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨xx,field.1,xx,sw,sw,xx,field.2,xx⟩

theorem replays (w : Nat → Wire) (b sign eff : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hb : b∈W) (hs : sign∈W) (he : eff∈W)
    (ls : List MixedTranscriptLetter) (ht : ∀l∈ls,l.1.1∈W ∧ l.1.2∈W) :
    wires (OffsetBorrowedCanonical.replay w b sign eff ls)⊆W ∧
    wires (OffsetBorrowedInverseCanonical.replay w b sign eff ls)⊆W := by
  have body := bodies w sign eff W hW hs he
  induction ls with
  | nil => simp [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,wires]
  | cons l ls ih =>
    have record := ht l (by simp)
    have forward : wires (OffsetBorrowedCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2)⊆W :=
      DirectSupport.selectWindow b l.1.1 sign l.2.1 _ W hb record.1 hs
        (DirectSupport.selectWindow b l.1.2 eff l.2.2 _ W hb record.2 he body.1)
    have inverse : wires (OffsetBorrowedInverseCanonical.cell w b l.1.1 l.1.2 sign eff l.2.1 l.2.2)⊆W :=
      DirectSupport.selectWindow b l.1.1 sign l.2.1 _ W hb record.1 hs
        (DirectSupport.selectWindow b l.1.2 eff l.2.2 _ W hb record.2 he body.2)
    have rest := ih (fun l hl => ht l (List.mem_cons_of_mem _ hl))
    simp only [OffsetBorrowedCanonical.replay,OffsetBorrowedInverseCanonical.replay,
      wires_append,Finset.union_subset_iff]
    exact ⟨⟨forward,rest.1⟩,⟨rest.2,inverse⟩⟩

theorem replayPrograms (w : Nat → Wire) (b sign eff : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hb : b∈W) (hs : sign∈W) (he : eff∈W) :
    wires (offsetBorrowedSharedReplayProgram w b sign eff)⊆W ∧
    wires (offsetBorrowedInverseSharedReplayProgram w b sign eff)⊆W := by
  have c := converters w W hW
  have r := replays w b sign eff W hW hb hs he _ (tapeSupport w W hW)
  simp only [offsetBorrowedSharedReplayProgram,offsetBorrowedInverseSharedReplayProgram,
    wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨c.1.1,c.1.2,r.1,c.2.1,c.2.2,c.1.1,c.1.2,r.2,c.2.1,c.2.2⟩

theorem endpoints (w : Nat → Wire) (b sign eff : Wire) (W : Finset Wire)
    (hW : (compactSharedSites w).toFinset⊆W) (hb : b∈W) (hs : sign∈W) (he : eff∈W) :
    wires (offsetBorrowedSharedFieldDivision w b sign eff)⊆W ∧
    wires (offsetBorrowedInverseSharedFieldMultiplication w b sign eff)⊆W := by
  have u := unary w W hW
  have c := copy w W hW
  have r := replayPrograms w b sign eff W hW hb hs he
  simp only [offsetBorrowedSharedFieldDivision,offsetBorrowedInverseSharedFieldMultiplication,
    wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨u.1,r.1,c,c,r.2,u.2⟩

theorem kernel (divide : Bool) (w : Nat → Wire) (hn : (skywalkSharedWires w).Nodup)
    (b sign eff : Wire) (W : Finset Wire) (hW : (compactSharedSites w).toFinset⊆W)
    (hb : b∈W) (hs : sign∈W) (he : eff∈W) :
    wires (offsetBorrowedDirectArithmetic divide w b sign eff)⊆W := by
  have ints := integerSegments w (skywalkShared_integer_nodup w hn) p W hW
  have fields := endpoints w b sign eff W hW hb hs he
  have field : wires (if divide then offsetBorrowedSharedFieldDivision w b sign eff
      else offsetBorrowedInverseSharedFieldMultiplication w b sign eff)⊆W := by
    cases divide
    · exact fields.2
    · exact fields.1
  simp only [offsetBorrowedDirectArithmetic,wires_append,Finset.union_subset_iff,and_assoc]
  exact ⟨ints.1,ints.2.2.1,ints.2.2.2.2,field,ints.2.2.2.2,ints.2.2.2.1,ints.2.1⟩

end ECDSAAdd.Arithmetic.OffsetBorrowedSupport
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSupport.chainSupport
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSupport.offsetSupport
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSupport.fieldPrograms
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSupport.replayPrograms
#print axioms ECDSAAdd.Arithmetic.OffsetBorrowedSupport.kernel
