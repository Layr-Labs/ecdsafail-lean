import ECDSAAdd.Arithmetic.Paper935.PublicSlotStaticTotal
import ECDSAAdd.Arithmetic.Paper935.SlotViewsWidthGeometry
import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotWidthTotal

namespace ECDSAAdd.Arithmetic.Paper935

/-- Actual historical-slot compilation from public widths, layout and capacities. -/
theorem compileHistoricalSlotWidth_static_exists (hw : Nat) (A : Arena) (b : WindowBank) (before addWidth exitWidth : RowWindow)
    (F : SlotRegisters) (record : List Wire) (armed : Bool) (probeWidth offset capacity : Nat)
    (widths : b.Widths before)
    (distinct : (F.wires++record++b.rows.flatMap WindowRow.wires).Nodup)
    (owned : (F.wires++record++b.rows.flatMap WindowRow.wires).toFinset⊆A.live)
    (pairFG : addWidth.f=addWidth.g) (pairV : addWidth.gv=addWidth.fv)
    (gPositive : 0<addWidth.g) (vPositive : 0<addWidth.fv)
    (counterNonempty : F.counter≠[]) (exitPositive : 0<exitWidth.fv)
    (paddingBudget : A.live.card+before.growth addWidth≤935)
    (resizeBudget : (A.live.card+addWidth.payload-before.payload)+addWidth.growth exitWidth≤935)
    (counterBudget : (A.live.card+exitWidth.payload-before.payload)+(2*F.counter.length-1)≤935)
    (probePositive : armed=true → 0<probeWidth)
    (postBudget : armed=true → (A.live.card+exitWidth.payload-before.payload)+
      max (probeWidth+probeChunkCount (exitWidth.g+1) probeWidth) (F.offset.length+1)≤935)
    (offsetFits : armed=true → offset<2^F.offset.length)
    (historyWidth : hw+1≤exitWidth.fv)
    (historyBudget : (A.live.card+exitWidth.payload-before.payload)+(capacity-record.length)+max F.counter.length (hw+2)≤935) :
    ∃ Q,compileCheckedHistoricalSlotWidth hw A b record addWidth exitWidth F armed probeWidth offset capacity=some Q ∧
      Q.slot.front.exitBank.Widths exitWidth ∧
      (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).Nodup ∧
      (F.wires++record++Q.slot.front.exitBank.rows.flatMap WindowRow.wires).toFinset⊆Q.slot.front.exitArena.live ∧
      Q.slot.front.exitArena.live.card+before.payload=A.live.card+exitWidth.payload := by
  obtain ⟨P,compiled,exitWidths,exitDistinct,exitOwned,card⟩ :=
    compilePublicSlot_static_exists A b before addWidth exitWidth F record armed probeWidth offset
      widths distinct owned pairFG pairV gPositive vPositive counterNonempty exitPositive
      paddingBudget resizeBudget counterBudget probePositive postBudget offsetFits
  have views := historyViewsWidth_geometry hw P.front.exitArena F P.front.exitBank record exitDistinct exitOwned
  have wide : hw+2≤P.front.exitBank.fv.wires.length := by
    simp only [WindowRow.wires,List.length_append,List.length_singleton]
    rw [exitWidths.2.2.1]
    omega
  have hc : P.front.exitArena.live.card=A.live.card+exitWidth.payload-before.payload := by omega
  obtain ⟨Q,compiledQ,slot⟩ := compileCheckedHistoricalSlotWidth_exists hw A b record addWidth exitWidth F armed
    probeWidth offset capacity P compiled counterNonempty wide views.1 views.2 (by simpa [hc] using historyBudget)
  exact ⟨Q,compiledQ,by simpa [slot] using exitWidths,by simpa [slot] using exitDistinct,
    by simpa [slot] using exitOwned,by simpa [slot] using card⟩

end ECDSAAdd.Arithmetic.Paper935
