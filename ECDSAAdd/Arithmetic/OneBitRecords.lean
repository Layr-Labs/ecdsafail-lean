import ECDSAAdd.Arithmetic.OneBitLoopResources

namespace ECDSAAdd.Arithmetic

def oneBitRecordLoop (L : KaliskiRoundLayout) (i : Nat) (rs : List RoundRecord) : Program :=
  match rs with
  | [] => []
  | r::_ => oneBitLoop L r.swap i (rs.map RoundRecord.subtract)

def oneBitRecordUnloop (L : KaliskiRoundLayout) (i : Nat) (rs : List RoundRecord) : Program :=
  match rs with
  | [] => []
  | r::_ => oneBitUnloop L r.swap i (rs.map RoundRecord.subtract)

def OneBitRecordsValues (rs : List RoundRecord) (cs : List (Bool×Bool)) (s : BasisState) : Prop :=
  (∀ r∈rs, s r.swap=false) ∧ OneBitTapeValues (rs.map RoundRecord.subtract) cs s

theorem OneBitRecordsValues.congr (rs : List RoundRecord) (cs : List (Bool×Bool)) (s t : BasisState)
    (h : OneBitRecordsValues rs cs s) (he : ∀ w, w∈rs.flatMap RoundRecord.wires → t w=s w) :
    OneBitRecordsValues rs cs t := by
  refine ⟨fun r hr => (he r.swap (by simp [List.mem_flatMap,RoundRecord.wires]; exact ⟨r,hr,Or.inl rfl⟩)).trans (h.1 r hr),?_⟩
  apply OneBitTapeValues.congr _ _ _ _ h.2
  intro w hw
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hw
  exact he _ (by simp [List.mem_flatMap,RoundRecord.wires]; exact ⟨r,hr,Or.inr rfl⟩)

private theorem recordNodup (L : KaliskiRoundLayout) (r : RoundRecord) (rs : List RoundRecord)
    (hnd : (L.tapeWires (r::rs)).Nodup) :
    ((rs.map RoundRecord.swap) ++ L.oneBitTapeWires r.swap ((r::rs).map RoundRecord.subtract)).Nodup := by
  have hp : (rs.map RoundRecord.swap ++ (r::rs).map RoundRecord.subtract).Perm
      (r.subtract::rs.flatMap RoundRecord.wires) := by
    clear hnd
    induction rs with
    | nil => exact List.Perm.refl _
    | cons x xs ih =>
      apply List.perm_iff_count.mpr
      intro w
      have hh := ih.count_eq w
      simp [RoundRecord.wires,List.count_cons] at hh ⊢
      omega
  apply List.nodup_iff_count.mpr
  intro w
  have h := List.nodup_iff_count.mp hnd w
  have hh := hp.count_eq w
  simp [KaliskiRoundLayout.oneBitTapeWires,KaliskiRoundLayout.tapeWires,RoundRecord.wires,List.count_cons] at h hh ⊢
  omega

/-- 旧分配中的其余swap保留为零；实际循环只使用第一根swap。 -/
theorem oneBitRecordLoop_correct (L : KaliskiRoundLayout) (rs : List RoundRecord) (i p a : Nat) (z : KState)
    (hnd : (L.tapeWires rs).Nodup) (hw : L.counter.width=10) (hd : 2≤L.data.width)
    (hlen : i+rs.length≤512) (hk : KRoundCount i z) (hinv : KInvariant p a z) (hodd : p%2=1)
    (hp : p<2^L.low.length) (hu : z.u<2^L.low.length) (hv : z.v<2^L.low.length) :
    Triple (fun st => LoopState L z st ∧ OneBitRecordsValues rs (List.replicate rs.length (false,false)) st)
      (oneBitRecordLoop L i rs)
      (fun st => LoopState (loopEndLayout L rs.length) ((kaliskiStep^[rs.length]) z) st ∧ OneBitRecordsValues rs (kaliskiCodes rs.length z) st) ∧
    Triple (fun st => LoopState (loopEndLayout L rs.length) ((kaliskiStep^[rs.length]) z) st ∧ OneBitRecordsValues rs (kaliskiCodes rs.length z) st)
      (oneBitRecordUnloop L i rs)
      (fun st => LoopState L z st ∧ OneBitRecordsValues rs (List.replicate rs.length (false,false)) st) := by
  cases rs with
  | nil => constructor <;> intro s m h <;> exact ⟨rfl,h⟩
  | cons r rs =>
    have hn := recordNodup L r rs hnd
    have hn' := (List.nodup_append'.mp hn).2.1
    have hc := oneBitLoop_correct L r.swap ((r::rs).map RoundRecord.subtract) i p a z hn' hw hd
      (by simpa using hlen) hk hinv hodd hp hu hv
    have hwires := oneBitLoop_wires_subset L r.swap ((r::rs).map RoundRecord.subtract) i hw hd
    have frame (circ : Program) (hs : wires circ ⊆ (L.oneBitTapeWires r.swap ((r::rs).map RoundRecord.subtract)).toFinset)
        (s t : BasisState) (he : ∀ w, w∉wires circ → s w=t w)
        (h : ∀ x∈rs, s x.swap=false) : ∀ x∈rs,t x.swap=false := by
      intro x hx
      apply (he x.swap ?_).symm.trans (h x hx)
      intro hm
      exact List.disjoint_left.mp (List.nodup_append'.mp hn).2.2 (List.mem_map.mpr ⟨x,hx,rfl⟩)
        (List.mem_toFinset.mp (hs hm))
    have hf := hc.1.frame (frame _ hwires.1)
    have hb := hc.2.frame (frame _ hwires.2)
    simp only [List.length_map] at hf hb
    constructor
    · exact hf.conseq
        (fun s h => ⟨⟨⟨h.1,h.2.1 r (by simp)⟩,h.2.2⟩,fun x hx => h.2.1 x (by simp [hx])⟩)
        (fun s h => ⟨h.1.1.1,⟨fun x hx => by rcases List.mem_cons.mp hx with rfl | hx; exact h.1.1.2; exact h.2 x hx,h.1.2⟩⟩)
    · exact hb.conseq
        (fun s h => ⟨⟨⟨h.1,h.2.1 r (by simp)⟩,h.2.2⟩,fun x hx => h.2.1 x (by simp [hx])⟩)
        (fun s h => ⟨h.1.1.1,⟨fun x hx => by rcases List.mem_cons.mp hx with rfl | hx; exact h.1.1.2; exact h.2 x hx,h.1.2⟩⟩)

def oneBitRecordWires : List RoundRecord → List Wire
  | [] => []
  | r::rs => r.swap::(r::rs).map RoundRecord.subtract

theorem oneBitRecordWires_range (f : Nat → RoundRecord) (n : Nat) :
    oneBitRecordWires ((List.range (n+1)).map f) =
      (f 0).swap :: (List.range (n+1)).map (fun i => (f i).subtract) := by
  rw [List.range_succ_eq_map]
  simp [oneBitRecordWires,List.map_map]

theorem oneBitRecordWires_sublist (rs : List RoundRecord) :
    (oneBitRecordWires rs).Sublist (rs.flatMap RoundRecord.wires) := by
  have hs (xs : List RoundRecord) : (xs.map RoundRecord.subtract).Sublist (xs.flatMap RoundRecord.wires) := by
    induction xs with
    | nil => exact List.Sublist.refl _
    | cons x xs ih => exact List.Sublist.cons x.swap (List.Sublist.cons₂ x.subtract ih)
  cases rs with
  | nil => exact List.Sublist.refl _
  | cons r rs => exact List.Sublist.cons₂ r.swap (List.Sublist.cons₂ r.subtract (hs rs))

def KaliskiRoundLayout.usedRecordTapeWires (L : KaliskiRoundLayout) (rs : List RoundRecord) : List Wire :=
  oneBitRecordWires rs ++ L.usedSharedWires

theorem KaliskiRoundLayout.usedRecordTapeWires_sublist (L : KaliskiRoundLayout) (rs : List RoundRecord) :
    (L.usedRecordTapeWires rs).Sublist (L.tapeWires rs) :=
  (oneBitRecordWires_sublist rs).append ((L.data.usedWires_sublist.append_left _).append_right _)

theorem oneBitRecordLoop_wires (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hw : L.counter.width=10) (hd : 2≤L.data.width) :
    wires (oneBitRecordLoop L i rs)=(if rs.isEmpty then ∅ else (L.usedRecordTapeWires rs).toFinset) ∧
    wires (oneBitRecordUnloop L i rs)=(if rs.isEmpty then ∅ else (L.usedRecordTapeWires rs).toFinset) := by
  cases rs with
  | nil => simp [oneBitRecordLoop,oneBitRecordUnloop,wires]
  | cons r rs => simpa [oneBitRecordLoop,oneBitRecordUnloop,KaliskiRoundLayout.usedRecordTapeWires,
      oneBitRecordWires,KaliskiRoundLayout.usedOneBitTapeWires] using
      oneBitLoop_wires L r.swap ((r::rs).map RoundRecord.subtract) i hw hd

theorem oneBitRecordLoop_counts (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hnd : (L.tapeWires rs).Nodup) (hw : L.counter.width=10) :
    toffoliCount (oneBitRecordLoop L i rs)=rs.length*(12*L.data.width+31) ∧
    measurementCount (oneBitRecordLoop L i rs)=rs.length*(6*L.data.width+29) ∧
    toffoliCount (oneBitRecordUnloop L i rs)=rs.length*(12*L.data.width+32) ∧
    measurementCount (oneBitRecordUnloop L i rs)=rs.length*(6*L.data.width+28) := by
  cases rs with
  | nil => simp [oneBitRecordLoop,oneBitRecordUnloop,toffoliCount,measurementCount]
  | cons r rs => simpa [oneBitRecordLoop,oneBitRecordUnloop] using
      oneBitLoop_counts L r.swap ((r::rs).map RoundRecord.subtract) i ((List.nodup_append'.mp (recordNodup L r rs hnd)).2.1) hw

theorem oneBitRecordLoop_qubits (L : KaliskiRoundLayout) (rs : List RoundRecord) (i : Nat)
    (hnd : (L.tapeWires rs).Nodup) (hw : L.counter.width=10) (hd : 2≤L.data.width) (hne : rs≠[]) :
    qubitCount (oneBitRecordLoop L i rs)=7*L.data.width+46+rs.length+1 ∧
    qubitCount (oneBitRecordUnloop L i rs)=7*L.data.width+46+rs.length+1 := by
  cases rs with
  | nil => exact (hne rfl).elim
  | cons r rs => simpa [oneBitRecordLoop,oneBitRecordUnloop] using
      oneBitLoop_qubits L r.swap ((r::rs).map RoundRecord.subtract) i ((List.nodup_append'.mp (recordNodup L r rs hnd)).2.1) hw hd (by simp)

theorem OneBitRecordsValues.zero_iff (rs : List RoundRecord) (s : BasisState) :
    OneBitRecordsValues rs (List.replicate rs.length (false,false)) s ↔
      regValue (rs.flatMap RoundRecord.wires) s=0 := by
  induction rs with
  | nil => simp [OneBitRecordsValues,OneBitTapeValues,regValue]
  | cons r rs ih =>
    simp only [OneBitRecordsValues,List.length_cons,List.replicate_succ,List.map_cons,
      OneBitTapeValues,List.flatMap_cons,RoundRecord.wires] at *
    simp only [List.mem_cons,forall_eq_or_imp] 
    simp only [regValue_zero] at *
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_imp,forall_and] at *
    simp only [forall_eq] at *
    tauto

end ECDSAAdd.Arithmetic
