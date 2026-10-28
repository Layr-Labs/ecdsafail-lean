import ECDSAAdd.Arithmetic.Paper935.CheckedHistoricalSlot
import ECDSAAdd.Arithmetic.Paper935.RowStageInverse

namespace ECDSAAdd.Arithmetic.Paper935
open ECDSAAdd.RecordedQuantum

theorem counterPositive_physical (one zz pos sign : Wire) (bs : List ZeroBit)
    (hn : (pos::one::zz::bs.flatMap ZeroBit.wires).Nodup)
    (signView : sign∈bs.map ZeroBit.input) :
    GatePhysical (counterPositive one zz pos sign bs) := by
  have cmp := equalConstant_physical one zz bs 0 (List.nodup_cons.mp hn).2
  have posAway := (List.nodup_cons.mp hn).1
  have signIn : sign∈bs.flatMap ZeroBit.wires := by
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp signView
    exact List.mem_flatMap.mpr ⟨b,hb,by simp [ZeroBit.wires]⟩
  have sp : sign≠pos := fun he => posAway (by simp [←he,signIn])
  have zp : zz≠pos := fun he => posAway (by simp [←he])
  have positive : GatePhysical (positiveFlag sign zz pos) := by
    simp [positiveFlag,GatePhysical,PhysicalInstr,ProperGate,sp,zp]
  rw [counterPositive,gatePhysical_append,gatePhysical_append]
  exact ⟨cmp,positive,cmp⟩

theorem HistoryLayout.Valid.physical (H : HistoryLayout) (h : H.Valid) : PhysicalProgram H.program := by
  obtain ⟨hz,hf,hsg,hpos,hfr,hlow,hwork,hpush,hout,hstable⟩ := h
  have counter := counterPositive_physical H.one H.zz H.pos H.sign H.zb (List.nodup_cons.mp hz).2 hsg
  have compare := equalConstant_physical H.one H.output (H.frozen::H.positive::H.low) 0 hf
  have flag : GatePhysical (storeFlag H.one H.zz H.pos H.sign H.output H.zb H.frozen H.positive H.low) := by
    rw [storeFlag,gatePhysical_append,gatePhysical_append]
    exact ⟨counter,compare,counter⟩
  have push : GatePhysical (pushHistory H.output H.port H.record) := by
    exact (physical_embed _).mp (physical_of_proper _ (shiftLeft_proper H.output (H.port::H.record) hpush))
  rw [HistoryLayout.program,storePushForget,physical_append,physical_embed]
  constructor
  · change GatePhysical (storePush H.one H.zz H.pos H.sign H.output H.port H.zb H.frozen H.positive H.low H.record)
    rw [storePush,gatePhysical_append,gatePhysical_append]
    exact ⟨flag,push,flag⟩
  · simp [ECDSAAdd.Arithmetic.Divsteps.forgetBranch,PhysicalProgram,PhysicalInstr]

/-- The instruction check is implied by the ordinary static view validity;
it is not an additional semantic assumption about successful inputs. -/
theorem compileHistory_instruction_check (one zz pos sign output port frozen : Wire)
    (counter coeffBits record work : List Wire) (H : HistoryLayout)
    (h : compileHistory one zz pos sign output port frozen counter coeffBits record work=some H) :
    H.program.all historyInstructionCheck=true := by
  have valid := (compileHistory_contract one zz pos sign output port frozen counter coeffBits record work H h).1
  apply List.all_eq_true.mpr
  intro i hi
  exact (historyInstructionCheck_iff i).mpr (valid.physical H i hi)

end ECDSAAdd.Arithmetic.Paper935
