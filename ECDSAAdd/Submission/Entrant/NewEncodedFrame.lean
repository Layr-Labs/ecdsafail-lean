import ECDSAAdd.Submission.Entrant.ParityCodec5NewBase
import ECDSAAdd.Submission.Entrant.TraceParity5

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.NewHistory5
open Arithmetic Secp256k1 BalancedField OffsetBorrowedCanonical CompressedFieldSupport MappedCompressed
abbrev historyId := History5.historyId
abbrev historyMap := History5.historyMap
abbrev historyMap_injective := History5.historyMap_injective
abbrev historyId_bound := History5.historyId_bound
abbrev historyId_region := History5.historyId_region
abbrev history_active_away := History5.history_active_away
abbrev history_words_away := History5.history_words_away
abbrev frame_history_legal := History5.frame_history_legal

abbrev RawLegal := History5.RawLegal
abbrev packDue := History5.packDue
abbrev packDue_true := History5.packDue_true

def encode (w : Nat → Wire) (start : Nat) : Program := ParityCodec5New.encodeAt (historyMap w start)
def decode (w : Nat → Wire) (start : Nat) : Program := ParityCodec5New.decodeAt (historyMap w start)
def packAfter (w : Nat → Wire) (i : Nat) : Program := if packDue i then encode w (i-5) else []
def decodeBefore (w : Nat → Wire) (i : Nat) : Program := if packDue i then decode w (i-5) else []
def encodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => encodePrefix w n++packAfter w n
def decodePrefix (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => decodeBefore w n++decodePrefix w n
def allEncode (w : Nat → Wire) : Nat → Program
  | 0 => []
  | n+1 => allEncode w n++encode w (5*n)
def decodeRange (w : Nat → Wire) (i : Nat) : Nat → Program
  | 0 => []
  | n+1 => decodeRange w (i+1) n++decodeBefore w i

def CompressedCompactStage5 (w : Nat → Wire) (x p i : Nat) (bits : BasisState) : Prop :=
  ∃raw : State,
    W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i raw.basis ∧
    bits=(run (encodePrefix w i) [] raw).basis

def EncodedFieldFrame5 (w : Nat → Wire) (sign : Wire) (origin : BasisState)
    (X Y : Fp) (s : State) : Prop :=
  ∃raw : State,raw.phase=s.phase ∧
    PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y origin
      (centerWord X) (centerWord Y) raw.basis ∧ s=run (allEncode w 102) [] raw

def EncodedCanonicalFrame5 (origin : BasisState) (X Y : Fp) (s : State) : Prop :=
  ∃raw : State,raw.phase=s.phase ∧
    PairFrame (skywalkSharedField base).z (skywalkSharedField base).a origin
      X.val Y.val raw.basis ∧ s=run (allEncode base 102) [] raw

def groupReadSites (w : Nat → Wire) (b sign eff : Wire) (start : Nat) : Finset Wire :=
  (sharedSites w sign).toFinset ∪ {b,eff} ∪ wires (encode w start)
def otherEncode (w : Nat → Wire) (j : Nat) : Nat → Program
  | 0 => []
  | n+1 => if n=j then otherEncode w j n else otherEncode w j n++encode w (5*n)

theorem encode_counts (w : Nat → Wire) (start : Nat) :
    toffoliCount (encode w start)=9 ∧ measurementCount (encode w start)=4 :=
  ⟨(ParityCodec5New.countsAt _).1,(ParityCodec5New.countsAt _).2.1⟩
theorem decode_counts (w : Nat → Wire) (start : Nat) :
    toffoliCount (decode w start)=11 ∧ measurementCount (decode w start)=2 :=
  (ParityCodec5New.countsAt _).2.2

theorem encode_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    (run (encode w start) m s).phase=s.phase :=
  ParityCodec5New.encodeAt_phase _ (historyMap_injective w hn start hs) s m legal

theorem encode_correct (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    (run (encode w start) m s).phase=s.phase ∧
      (run (encode w start) m s).basis (historyMap w start 5)=false ∧
      (run (encode w start) m s).basis (historyMap w start 9)=false :=
  ParityCodec5New.encodeAt_correct _ (historyMap_injective w hn start hs) s m legal

theorem encode_support_eq (w : Nat → Wire) (start : Nat) :
    wires (encode w start)=wires (History5.encode w start) :=
  (ParityCodec5New.mapped_support_eq _).1
theorem decode_support_eq (w : Nat → Wire) (start : Nat) :
    wires (decode w start)=wires (History5.decode w start) :=
  (ParityCodec5New.mapped_support_eq _).2

theorem history_site_mem (w : Nat → Wire) (start : Nat) (q : Fin 10) :
    historyMap w start q∈wires (encode w start) := ParityCodec5New.site_mem _ q

theorem allEncode_support_eq (w : Nat → Wire) (n : Nat) :
    wires (allEncode w n)=wires (History5.allEncode w n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allEncode,History5.allEncode,wires_append,ih,encode_support_eq]

theorem history_gate_mem (w : Nat → Wire) (start : Nat) (p : Program)
    (hp : p=encode w start ∨ p=decode w start) (q : Wire) (hq : q∈wires p) :
    ∃i : Fin 10,q=historyMap w start i := by
  rcases hp with rfl|rfl
  · rw [encode_support_eq] at hq
    exact History5.history_gate_mem w start _ (Or.inl rfl) q hq
  · rw [decode_support_eq] at hq
    exact History5.history_gate_mem w start _ (Or.inr rfl) q hq

theorem windows_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (a b : Nat) (ha : a+5≤512) (hb : b+5≤512) (hab : a+5≤b) :
    Disjoint (wires (encode w a)) (wires (encode w b)) := by
  rw [encode_support_eq,encode_support_eq]
  exact History5.windows_disjoint w hn a b ha hb hab

theorem allEncode_history_support (w : Nat → Wire) (n : Nat) (bound : 5*n≤512) :
    wires (allEncode w n)⊆(wireBlock w 0 512++wireBlock w 1028 512).toFinset := by
  rw [allEncode_support_eq]
  exact History5.allEncode_history_support w n bound

theorem allEncode_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (outside : n≤j) (jb : 5*j+5≤512) :
    Disjoint (wires (allEncode w n)) (wires (encode w (5*j))) := by
  rw [allEncode_support_eq,encode_support_eq]
  exact History5.allEncode_disjoint w hn n j bound outside jb

theorem allEncode_zero_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (bound : 5*n≤512) (s : State) :
    (run (allEncode w n) [] s).phase=s.phase := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [allEncode,run_append]
    simp only [List.take_nil,List.drop_nil]
    exact (ParityCodec5New.encodeAt_zero_phase _ (historyMap_injective w hn _ (by omega)) _).trans
      (ih (by omega))

theorem allEncode_phase (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n : Nat) (bound : 5*n≤512) (s : State) (m : List Bool) (legal : RawLegal w n s.basis) :
    (run (allEncode w n) m s).phase=s.phase := by
  induction n generalizing m with
  | zero => simp only [allEncode,run]
  | succ n ih =>
    let before := run (allEncode w n) (m.take (measurementCount (allEncode w n))) s
    have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
    have same (q : Fin 10) : before.basis (historyMap w (5*n) q)=s.basis (historyMap w (5*n) q) :=
      run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp dis used (history_site_mem w (5*n) q))
    have dom : MeasuredCodec5.legalAt (historyMap w (5*n)) before.basis := by
      apply (MeasuredCodec5.legalAt_iff _ _).mpr
      intro i
      rw [same,same]
      exact (MeasuredCodec5.legalAt_iff _ _).mp (legal n (by omega)) i
    rw [allEncode,run_append]
    exact (encode_phase w hn (5*n) (by omega) before _ dom).trans
      (ih (by omega) _ (fun j hj => legal j (by omega)))

attribute [local irreducible] run wires

theorem otherEncode_outside (w : Nat → Wire) (n j : Nat) (h : n≤j) :
    otherEncode w j n=allEncode w n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [otherEncode,if_neg (by omega),ih (by omega),allEncode]

theorem otherEncode_member (w : Nat → Wire) (n j : Nat) (q : Wire)
    (h : q∈wires (otherEncode w j n)) : ∃k,k<n ∧ k≠j ∧ q∈wires (encode w (5*k)) := by
  induction n with
  | zero => simp [otherEncode,wires] at h
  | succ n ih =>
    by_cases same : n=j
    · simp only [otherEncode,if_pos same] at h
      obtain ⟨k,hk,hj,member⟩ := ih h
      exact ⟨k,by omega,hj,member⟩
    · simp only [otherEncode,if_neg same,wires_append,Finset.mem_union] at h
      rcases h with h|h
      · obtain ⟨k,hk,hj,member⟩ := ih h
        exact ⟨k,by omega,hj,member⟩
      · exact ⟨n,by omega,same,h⟩

theorem otherEncode_disjoint (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) :
    Disjoint (wires (otherEncode w j n)) (wires (encode w (5*j))) := by
  apply Finset.disjoint_left.mpr
  intro q hq hc
  obtain ⟨k,hk,ne,member⟩ := otherEncode_member w n j q hq
  have sep : 5*k+5≤5*j ∨ 5*j+5≤5*k := by omega
  rcases sep with h|h
  · exact Finset.disjoint_left.mp (windows_disjoint w hn _ _ (by omega) (by omega) h) member hc
  · exact Finset.disjoint_left.mp (windows_disjoint w hn _ _ (by omega) (by omega) h) hc member

theorem allEncode_factor (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (s : State) :
    run (allEncode w n) [] s=run (otherEncode w j n) [] (run (encode w (5*j)) [] s) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    by_cases same : j=n
    · subst j
      have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
      rw [allEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [otherEncode,if_pos rfl,otherEncode_outside w n n (Nat.le_refl _)]
      exact (run_disjoint_commute (allEncode w n) (encode w (5*n)) dis [] [] s).symm
    · have prior := ih j (by omega) (by omega)
      have right : run (otherEncode w j (n+1)) [] (run (encode w (5*j)) [] s)=
          run (encode w (5*n)) [] (run (otherEncode w j n) [] (run (encode w (5*j)) [] s)) := by
        rw [otherEncode,if_neg (Ne.symm same),run_append]
        simp only [List.take_nil,List.drop_nil]
      rw [allEncode,run_append]
      simp only [List.take_nil,List.drop_nil]
      rw [prior,right]

theorem otherEncode_body_disjoint (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hb : b∉skywalkPoolWires w) (hsign : sign∉skywalkPoolWires w) (heff : eff∉skywalkPoolWires w)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (body : Program)
    (support : wires body⊆groupReadSites w b sign eff (5*j)) :
    Disjoint (wires (otherEncode w j n)) (wires body) := by
  have pool := skywalkShared_integer_nodup w hn
  have groups := otherEncode_disjoint w pool n j bound hj
  apply Finset.disjoint_left.mpr
  intro q hq used
  obtain ⟨k,hk,ne,member⟩ := otherEncode_member w n j q hq
  obtain ⟨r,rfl⟩ := history_gate_mem w (5*k) _ (Or.inl rfl) q member
  have own : historyMap w (5*k) r∈skywalkPoolWires w := by
    apply List.mem_map.mpr
    refine ⟨historyId (5*k) r,?_,rfl⟩
    simp only [List.mem_range'_1]
    have boundId : historyId (5*k) r<1798 := historyId_bound (5*k) (by omega) r
    omega
  have away := history_active_away w sign hn hsign (5*k) (by omega) r
  have read := support used
  simp only [groupReadSites,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at read
  rcases read with (read|read)|read
  · exact away (List.mem_toFinset.mp read)
  · rcases read with eq|eq
    · exact hb (eq ▸ own)
    · exact heff (eq ▸ own)
  · exact Finset.disjoint_left.mp groups hq read

theorem window_transport_other (w : Nat → Wire) (start : Nat)
    (hn : (skywalkPoolWires w).Nodup) (hs : start+5≤512) (other body : Program)
    (he : Disjoint (wires other) (wires (encode w start)))
    (hb : Disjoint (wires other) (wires body)) (s : State) (mO m0 m1 m2 m3 : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    run (encode w start) m3 (run body m2 (run (decode w start) m1
      (run other mO (run (encode w start) m0 s))))=
      run other mO (run (encode w start) m3 (run body m2 s)) := by
  have otherLegal : MeasuredCodec5.legalAt (historyMap w start) (run other mO s).basis := by
    apply (MeasuredCodec5.legalAt_iff _ _).mpr
    have same (q : Fin 10) : (run other mO s).basis (historyMap w start q)=s.basis (historyMap w start q) :=
      run_preserves_outside _ _ _ _ (fun used => Finset.disjoint_left.mp he used (history_site_mem w start q))
    intro i
    rw [same,same]
    exact (MeasuredCodec5.legalAt_iff _ _).mp legal i
  rw [run_disjoint_commute other (encode w start) he mO m0 s]
  rw [show run (decode w start) m1 (run (encode w start) m0 (run other mO s))=run other mO s from
    ParityCodec5New.roundtripAt _ (historyMap_injective w hn start hs) _ m0 m1 otherLegal]
  rw [←run_disjoint_commute other body hb mO m2 s]
  exact (run_disjoint_commute other (encode w start) he mO m3 (run body m2 s)).symm


private theorem zero_records (p : Program) (hm : measurementCount p=0)
    (s : State) (m n : List Bool) : run p m s=run p n s := by
  rw [←run_take p m s,←run_take p n s,hm]
  simp only [List.take_zero]

theorem encoded_window_step (w : Nat → Wire) (b sign eff : Wire)
    (hn : (skywalkSharedWires w).Nodup)
    (hp : ∀q∈[b,sign,eff],q∉skywalkPoolWires w)
    (j : Nat) (hj : j<102) (origin : BasisState) (X Y A B : Fp) (body : Program)
    (support : wires body⊆groupReadSites w b sign eff (5*j))
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame5 w sign origin X Y s)
    (legal : RawLegal w 102 origin) :
    let out := run (decode w (5*j)++body++encode w (5*j)) m s
    out.phase=s.phase ∧ EncodedFieldFrame5 w sign origin A B out := by
  obtain ⟨raw,phase,frame,eq⟩ := input
  have pool := skywalkShared_integer_nodup w hn
  have leg := frame_history_legal w sign hn (hp sign (by simp)) 102 (by decide)
    origin raw.basis _ _ legal frame
  have factor := allEncode_factor w pool 102 j (by decide) hj raw
  have hE := otherEncode_disjoint w pool 102 j (by decide) hj
  have hB := otherEncode_body_disjoint w b sign eff hn
    (hp b (by simp)) (hp sign (by simp)) (hp eff (by simp)) 102 j (by decide) hj body support
  let mb := m.drop 2
  let rawOut := run body mb raw
  have result := correct raw mb frame
  have outLeg := frame_history_legal w sign hn (hp sign (by simp)) 102 (by decide)
    origin rawOut.basis _ _ legal result.2
  have transport := window_transport_other w (5*j) pool (by omega)
    (otherEncode w j 102) body hE hB raw [] [] (m.take 2) mb (mb.drop (measurementCount body)) (leg j hj)
  have records : run (encode w (5*j)) (mb.drop (measurementCount body)) rawOut=
      run (encode w (5*j)) [] rawOut :=
    ParityCodec5New.encodeAt_independent _ (historyMap_injective w pool _ (by omega)) _ _ _ (outLeg j hj)
  rw [records] at transport
  have back := allEncode_factor w pool 102 j (by decide) hj rawOut
  rw [←back] at transport
  have actual : run (decode w (5*j)++body++encode w (5*j)) m s=run (allEncode w 102) [] rawOut := by
    rw [eq,factor]
    simp only [List.append_assoc]
    rw [run_append,(decode_counts w (5*j)).2,run_append,run_take]
    exact transport
  dsimp only
  rw [actual]
  have encPhase := allEncode_zero_phase w pool 102 (by decide) rawOut
  exact ⟨encPhase.trans (result.1.trans phase),rawOut,encPhase.symm,result.2,rfl⟩


theorem encoded_disjoint_step (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkPoolWires w).Nodup) (origin : BasisState) (X Y A B : Fp) (body : Program)
    (dis : Disjoint (wires (allEncode w 102)) (wires body))
    (correct : Triple (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
      origin (centerWord X) (centerWord Y)) body
      (PairFrame (balancedSharedPorts w sign).r (balancedSharedPorts w sign).y
        origin (centerWord A) (centerWord B)))
    (s : State) (m : List Bool) (input : EncodedFieldFrame5 w sign origin X Y s) :
    (run body m s).phase=s.phase ∧ EncodedFieldFrame5 w sign origin A B (run body m s) := by
  obtain ⟨raw,phase,frame,encoded⟩ := input
  let rawOut := run body m raw
  have result := correct raw m frame
  have actual : run body m s=run (allEncode w 102) [] rawOut := by
    rw [encoded]
    exact (run_disjoint_commute (allEncode w 102) body dis [] m raw).symm
  rw [actual]
  have ep := allEncode_zero_phase w hn 102 (by decide) rawOut
  exact ⟨ep.trans (result.1.trans phase),rawOut,ep.symm,result.2,rfl⟩


theorem allEncode_hole (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (s : State) (m : List Bool)
    (legal : RawLegal w n s.basis) (port : Fin 10) (hole : port=5 ∨ port=9) :
    (run (allEncode w n) m s).basis (historyMap w (5*j) port)=false := by
  induction n generalizing j m with
  | zero => omega
  | succ n ih =>
    let before := run (allEncode w n) (m.take (measurementCount (allEncode w n))) s
    by_cases current : j=n
    · subst j
      have dis := allEncode_disjoint w hn n n (by omega) (Nat.le_refl _) (by omega)
      have same (q : Fin 10) : before.basis (historyMap w (5*n) q)=s.basis (historyMap w (5*n) q) := by
        apply run_preserves_outside
        intro used
        exact Finset.disjoint_left.mp dis used (history_site_mem w (5*n) q)
      have domain : MeasuredCodec5.legalAt (historyMap w (5*n)) before.basis := by
        apply (MeasuredCodec5.legalAt_iff _ _).mpr
        intro i
        rw [same,same]
        exact (MeasuredCodec5.legalAt_iff _ _).mp (legal n (by omega)) i
      have result := encode_correct w hn (5*n) (by omega) before
        (m.drop (measurementCount (allEncode w n))) domain
      rw [allEncode,run_append]
      rcases hole with rfl|rfl
      · exact result.2.1
      · exact result.2.2
    · have older : j<n := by omega
      have prior := ih j (by omega) older (m.take (measurementCount (allEncode w n)))
        (fun k hk => legal k (by omega))
      have dis := windows_disjoint w hn (5*j) (5*n) (by omega) (by omega) (by omega)
      have keep := run_preserves_outside (encode w (5*n))
        (m.drop (measurementCount (allEncode w n))) before (historyMap w (5*j) port)
        (fun used => Finset.disjoint_left.mp dis (history_site_mem w (5*j) port) used)
      rw [allEncode,run_append]
      exact keep.trans prior


theorem allEncode_holes_zero (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (legal : RawLegal w 102 s.basis)
    (k : Nat) (hk : k<204) : (run (allEncode w 102) m s).basis (w (Placement5.H k))=false := by
  let port : Fin 10 := if k%2=0 then 5 else 9
  have hp : port=5 ∨ port=9 := by unfold port; split <;> simp
  have same : w (Placement5.H k)=historyMap w (5*(k/2)) port := by
    change w (Placement5.H k)=w (historyId (5*(k/2)) port)
    congr 1
    unfold Placement5.H historyId History5.historyId port
    split_ifs <;> omega
  rw [same]
  exact allEncode_hole w hn 102 (k/2) (by decide) (by omega) s m legal port hp

theorem encoded_work_zero (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (origin : BasisState) (env : Env w origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame5 w sign origin X Y s)
    (q : Nat) (hq : Placement5.workRegion q) : s.basis (w q)=false := by
  obtain ⟨raw,_,rawFrame,encoded⟩ := frame
  have rawEnv := pair_env w sign hn origin raw.basis _ _ env rawFrame
  have zero := OffsetCleanupBorrowedCaller.maskBit_zero w raw.basis rawEnv.1 q
    (by unfold Placement5.workRegion at hq; omega) (by unfold Placement5.workRegion at hq; omega)
  have support := allEncode_history_support w 102 (by decide)
  have away : w q∉wires (allEncode w 102) := by
    intro used
    have member := List.mem_toFinset.mp (support used)
    rcases List.mem_append.mp member with member|member
    all_goals
      obtain ⟨k,hk,eq⟩ := List.mem_map.mp member
      simp only [List.mem_range'_1] at hk
      have same := skywalkShared_index_inj w hn k q (by omega)
        (by unfold Placement5.workRegion at hq; omega) eq
      unfold Placement5.workRegion at hq
      omega
  rw [encoded]
  exact (run_preserves_outside (allEncode w 102) [] raw _ away).trans zero

theorem encoded_zero_region (w : Nat → Wire) (sign : Wire)
    (hn : (skywalkSharedWires w).Nodup) (ho : sign∉skywalkPoolWires w)
    (origin : BasisState) (env : Env w origin) (legal : RawLegal w 102 origin)
    (X Y : Fp) (s : State) (frame : EncodedFieldFrame5 w sign origin X Y s) :
    ∀q,Placement5.zeroRegion q → s.basis (w q)=false := by
  intro q hq
  rcases hq with work|hole
  · exact encoded_work_zero w sign hn origin env X Y s frame q work
  · have recover := Placement5.hole_recover q hole
    obtain ⟨raw,_,rawFrame,encoded⟩ := frame
    have rawLegal := frame_history_legal w sign hn ho 102 (by decide) origin raw.basis _ _ legal rawFrame
    rw [encoded,←recover.2]
    exact allEncode_holes_zero w (skywalkShared_integer_nodup w hn) raw [] rawLegal _ recover.1


theorem encoded_canonical_unique (origin : BasisState) (X Y : Fp) (s t : State)
    (hs : EncodedCanonicalFrame5 origin X Y s) (ht : EncodedCanonicalFrame5 origin X Y t)
    (phase : s.phase=t.phase) : s=t := by
  obtain ⟨a,ha,fa,ea⟩ := hs
  obtain ⟨b,hb,fb,eb⟩ := ht
  have raw : a=b := by
    apply State.extensionality
    · exact ha.trans (phase.trans hb.symm)
    · exact PairFrame.unique _ _ origin _ _ _ _ fa fb
  rw [ea,eb,raw]

theorem groupReadSites_eq (w : Nat → Wire) (b sign eff : Wire) (start : Nat) :
    groupReadSites w b sign eff start=History5.groupReadSites w b sign eff start := by
  unfold groupReadSites History5.groupReadSites
  rw [encode_support_eq]

theorem otherEncode_support_eq (w : Nat → Wire) (j n : Nat) :
    wires (otherEncode w j n)=wires (History5.otherEncode w j n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n=j
    · simpa only [otherEncode,History5.otherEncode,h,if_true] using ih
    · simp only [otherEncode,History5.otherEncode,h,if_false,wires_append,ih,encode_support_eq]

def payloadPort (i : Fin 8) : Fin 10 :=
  ⟨if i.val<5 then i.val else i.val+1,by split <;> omega⟩

def payloadWire (w : Nat → Wire) (i : Nat) : Wire :=
  historyMap w (5*(i/8)) (payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)

theorem payloadWire_packet (w : Nat → Wire) (j i : Nat) (hi : i<8) :
    payloadWire w (8*j+i)=historyMap w (5*j) (payloadPort ⟨i,hi⟩) := by
  have hd : (8*j+i)/8=j := by omega
  have hm : (8*j+i)%8=i := by omega
  simp only [payloadWire,hd,hm]

theorem encode_packet_parity (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (start : Nat) (hs : start+5≤512) (s : State) (m : List Bool)
    (legal : MeasuredCodec5.legalAt (historyMap w start) s.basis) :
    TraceParity5.xorRange 8 (fun i => (run (encode w start) m s).basis
      (historyMap w start (payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩)))=
    TraceParity5.xorRange 5 (fun i => s.basis (w (1028+start+i))) := by
  have localParity := ParityCodec5New.encodeAt_parity (historyMap w start)
    (historyMap_injective w hn start hs) s m legal
  simpa [TraceParity5.xorRange,payloadPort,historyMap,History5.historyMap,
    historyId,History5.historyId,Bool.xor_assoc,Nat.add_assoc,encode] using localParity.symm

theorem allEncode_packet_parity (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n j : Nat) (bound : 5*n≤512) (hj : j<n) (raw : State)
    (legal : RawLegal w n raw.basis) :
    TraceParity5.xorRange 8 (fun i => (run (allEncode w n) [] raw).basis
      (payloadWire w (8*j+i)))=
    TraceParity5.xorRange 5 (fun i => raw.basis (w (1028+5*j+i))) := by
  have factor := allEncode_factor w hn n j bound hj raw
  have dis := otherEncode_disjoint w hn n j bound hj
  have same (q : Fin 10) : (run (allEncode w n) [] raw).basis (historyMap w (5*j) q)=
      (run (encode w (5*j)) [] raw).basis (historyMap w (5*j) q) := by
    rw [factor]
    exact run_preserves_outside _ _ _ _
      (fun used => Finset.disjoint_left.mp dis used (history_site_mem w (5*j) q))
  calc
    TraceParity5.xorRange 8 (fun i => (run (allEncode w n) [] raw).basis (payloadWire w (8*j+i)))=
        TraceParity5.xorRange 8 (fun i => (run (encode w (5*j)) [] raw).basis
          (historyMap w (5*j) (payloadPort ⟨i%8,Nat.mod_lt _ (by decide)⟩))) := by
      apply TraceParity5.xorRange_congr
      intro i hi
      rw [payloadWire_packet w j i hi]
      simpa only [Nat.mod_eq_of_lt hi] using same (payloadPort ⟨i,hi⟩)
    _ = _ := encode_packet_parity w hn (5*j) (by omega) raw [] (legal j hj)

theorem allEncode_tailS (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (n t : Nat) (_bound : 5*n≤512) (ht : 5*n≤t) (ht512 : t<512)
    (s : State) (m : List Bool) :
    (run (allEncode w n) m s).basis (w (1028+t))=s.basis (w (1028+t)) := by
  apply run_preserves_outside
  intro used
  rw [allEncode_support_eq] at used
  obtain ⟨j,hj,member⟩ := History5.allEncode_member w n _ used
  obtain ⟨q,hq⟩ := History5.history_gate_mem w (5*j) _ (Or.inl rfl) _ member
  have ids := skywalkPool_index_inj w hn (1028+t) (History5.historyId (5*j) q)
    (by omega) (History5.historyId_bound (5*j) (by omega) q) hq
  have hq10 := q.isLt
  unfold History5.historyId at ids
  split_ifs at ids <;> omega

theorem encoded_host_relation (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x : Nat) (hx0 : 0<x) (hx : x<ECDSAAdd.p) (raw s : State)
    (stage : W.CompactSkywalkStage w
      (SkywalkRails.encode false false (x:Int) (ECDSAAdd.p:Int)) 512 raw.basis)
    (encoded : s.basis=(run (allEncode w 102) [] raw).basis) :
    s.basis (w 1538)=TraceParity5.xorRange 816 (fun i => s.basis (payloadWire w i)) := by
  have hp0 : 0<ECDSAAdd.p := p_prime.pos
  have hpodd : ECDSAAdd.p%2=1 := by norm_num [ECDSAAdd.p]
  have legal : RawLegal w 102 raw.basis := by
    intro j hj
    exact W.stage_group_legal w hn x ECDSAAdd.p 512 (5*j) hp0 hpodd (by omega) (by decide) raw.basis stage
  have fields := (W.compactSkywalkStage_fields_iff w _ 512 (by decide) hn raw.basis).mp stage
  have rawS (i : Nat) (hi : i<512) : raw.basis (w (1028+i))=TraceParity5.rawS x i := by
    rw [(fields.2.2.2.1 i hi).2]
    simp only [TraceParity5.rawS,SkywalkTrace.trace_getD_code 512 _ i hi]
  have packets : ∀j,j<102 →
      TraceParity5.xorRange 8 (fun i => s.basis (payloadWire w (8*j+i)))=
      TraceParity5.xorRange 5 (fun i => TraceParity5.rawS x (5*j+i)) := by
    intro j hj
    rw [encoded,allEncode_packet_parity w hn 102 j (by decide) hj raw legal]
    apply TraceParity5.xorRange_congr
    intro i hi
    simpa only [Nat.add_assoc] using rawS (5*j+i) (by omega)
  have whole := TraceParity5.encoded_payload_parity x hx0 hx (fun i => s.basis (payloadWire w i)) packets
  have tail := allEncode_tailS w hn 102 510 (by decide) (by decide) (by decide) raw []
  change (run (allEncode w 102) [] raw).basis (w 1538)=raw.basis (w 1538) at tail
  calc
    s.basis (w 1538)=raw.basis (w 1538) := by rw [encoded]; exact tail
    _ = TraceParity5.rawS x 510 := rawS 510 (by decide)
    _ = TraceParity5.xorRange 816 (fun i => s.basis (payloadWire w i)) := whole.symm

end ECDSAAdd.Entrant.NewHistory5
