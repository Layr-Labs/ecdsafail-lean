import ECDSAAdd.Arithmetic.PhysicalGateCheck
import ECDSAAdd.Arithmetic.CompactSkywalkReverseProgram
import ECDSAAdd.Arithmetic.CompressedCompactReverseProgram
import ECDSAAdd.Arithmetic.PointSquarePhysical
import ECDSAAdd.Arithmetic.NarrowSkywalkTick
import ECDSAAdd.Arithmetic.MeasuredArithmeticPhysical
namespace ECDSAAdd.Arithmetic
open RecordedQuantum

theorem signComplement_physical (q : Wire) (xs : List Wire) (hq : q ∉ xs) :
    GatePhysical (signComplement q xs) := by
  intro i hi
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
  exact fun he => hq (he ▸ hx)

theorem signedWords_physical (q : Wire) (x y carry : List Wire)
    (hn : (q::x++y++carry).Nodup) :
    GatePhysical (signedAdd q x y carry) ∧ GatePhysical (signedSub q x y carry) := by
  have away : q ∉ x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x away
  have add := addInPlace_physical x y carry q hn
  have nots := notRegister_physical y
  have h : GatePhysical (signedAdd q x y carry) := by
    simpa only [signedAdd,gatePhysical_append] using And.intro (And.intro fan add) fan
  exact ⟨h,by simpa only [signedSub,gatePhysical_append] using And.intro (And.intro nots h) nots⟩

theorem narrowRecords_physical (L : NarrowSignedRecordLayout) (n : Nat)
    (hw : L.Widths n) (hn : L.wires.Nodup) :
    GatePhysical (narrowSignedRecord L n) ∧ GatePhysical (narrowSignedUnrecord L n) := by
  have view := L.views n hw
  have nd := L.short_nodup hn
  have sx : L.sx≠L.q := by
    intro eq
    exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←eq])
  have sy : L.sy≠L.q := by
    intro eq
    exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←eq])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,sx,sy]
  have a := signedWords_physical L.q L.xp L.yp L.carryLow nd
  have f := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowSignedRecord,narrowSignedUnrecord,signedRecord,signedUnrecord,
    view.1,view.2.1,view.2.2.1,view.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨⟨toggle,a.1⟩,toggle⟩,f⟩,⟨f,⟨toggle,a.2⟩,toggle⟩⟩

theorem narrowTicks_physical (L : SkywalkIntegerLayout) (n : Nat) (hv : L.Valid)
    (hn : 0<n) (hle : n≤L.half.length) :
    GatePhysical (narrowSkywalkTick L n) ∧ GatePhysical (narrowSkywalkUntick L n) := by
  have route := L.route_nodup hv
  have swnd : (L.a0::L.ah++L.bh).Nodup := by
    apply List.nodup_iff_count.mpr; intro q
    have h := List.nodup_iff_count.mp route q
    simp only [List.count_cons,List.count_append] at h ⊢; omega
  have ab : L.a0≠L.b0 := by
    intro eq; exact (List.nodup_cons.mp route).1 (by simp [eq])
  have se : L.aSign≠L.ext := by
    intro eq
    have h := List.nodup_iff_count.mp hv.nodup L.ext
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.ah,eq,
      List.count_cons,List.count_append,List.count_nil,beq_self_eq_true,if_true] at h
    omega
  have pa : L.previous≠L.a0 := by
    intro eq
    exact (List.nodup_cons.mp hv.nodup).1 (by simp [eq])
  have sw := swapRegisters_physical L.a0 L.ah L.bh swnd
  have cx : GatePhysical [.CX L.a0 L.b0] := by simp [GatePhysical,PhysicalInstr,ProperGate,ab]
  have half : GatePhysical (skywalkSignedHalf L.aSign L.ext) := by
    simp [skywalkSignedHalf,GatePhysical,PhysicalInstr,ProperGate,se]
  have prev : GatePhysical [.CX L.previous L.a0] := by simp [GatePhysical,PhysicalInstr,ProperGate,pa]
  have recs := narrowRecords_physical (narrowSkywalkRecordLayout L n) n
    (narrowSkywalkRecord_widths L hv n hn hle) (narrowSkywalkRecord_nodup L hv n hn hle)
  simp only [narrowSkywalkTick,narrowSkywalkUntick,skywalkRoute,gatePhysical_append]
  exact ⟨⟨⟨⟨⟨sw,cx⟩,half⟩,recs.1⟩,prev⟩,⟨⟨⟨⟨prev,recs.2⟩,half⟩,cx⟩,sw⟩⟩

theorem compactSigns_physical (L : CompactSkywalkSignReleaseLayout) (hv : L.Valid) :
    GatePhysical (compactSkywalkSignRelease L) ∧ GatePhysical (compactSkywalkSignExpand L) :=
  ⟨signComplement_physical L.sign L.released (L.signAway hv),
   signComplement_physical L.sign L.released (L.signAway hv)⟩

theorem compactTicks_physical (w : Nat → Wire) (i : Nat) (hi : i<512)
    (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (compactSkywalkTick w i) ∧ GatePhysical (compactSkywalkReverseTick w i) := by
  have bounds := compactSkywalkTick_width_bounds i hi
  have n := narrowTicks_physical (compactSkywalkTickLayout w i) (compactSkywalkTickPostWidth i)
    (compactSkywalkTick_valid w i hi hn) (by omega)
    (by rw [compactSkywalkTick_half w i hi,wireBlock_length]; omega)
  have val := compactSkywalkTick_release_valid w i hi hn
  have a := compactSigns_physical (compactSkywalkTickARelease w i) val.1
  have b := compactSigns_physical (compactSkywalkTickBRelease w i) val.2
  simp only [compactSkywalkTick,compactSkywalkTickCleanup,compactSkywalkReverseTick,
    compactSkywalkReverseExpand,gatePhysical_append]
  exact ⟨⟨n.1,a.1,b.1⟩,⟨⟨b.2,a.2⟩,n.2⟩⟩

theorem codecPack_physical : GatePhysical TranscriptCodec3.pack := by
  apply physicalGateCheck_correct
  decide

theorem codecUnpack_physical : GatePhysical TranscriptCodec3.unpack := by
  apply physicalGateCheck_correct
  decide

theorem transcriptCodec_physical (w : Fin 6 → Wire) :
    GatePhysical (TranscriptCodec3.encode w) ∧ GatePhysical (TranscriptCodec3.decode w) := by
  exact ⟨gatePhysical_rename _ (TranscriptCodec3.placement w).injective _ codecPack_physical,
    gatePhysical_rename _ (TranscriptCodec3.placement w).injective _ codecUnpack_physical⟩

theorem compressedLoops_physical (w : Nat → Wire) (i n : Nat) (hi : i+n≤512)
    (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (compressedCompactForward w i n) ∧ GatePhysical (compressedCompactReverse w i n) := by
  induction n generalizing i with
  | zero => simp [compressedCompactForward,compressedCompactReverse,GatePhysical]
  | succ n ih =>
    have tick := compactTicks_physical w i (by omega) hn
    have tail := ih (i+1) (by omega)
    have codec := transcriptCodec_physical (compressedHistoryMap w (i-3))
    have pack : GatePhysical (compressedPackAfter w i) := by
      unfold compressedPackAfter
      split
      · exact codec.1
      · simp [GatePhysical]
    have unpack : GatePhysical (compressedDecodeBefore w i) := by
      unfold compressedDecodeBefore
      split
      · exact codec.2
      · simp [GatePhysical]
    simp only [compressedCompactForward,compressedCompactReverse,gatePhysical_append]
    exact ⟨⟨⟨tick.1,pack⟩,tail.1⟩,⟨⟨tail.2,unpack⟩,tick.2⟩⟩
end ECDSAAdd.Arithmetic
