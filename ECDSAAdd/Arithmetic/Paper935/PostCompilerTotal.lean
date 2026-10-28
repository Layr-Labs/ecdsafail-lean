import ECDSAAdd.Arithmetic.Paper935.ProbeCompilerPorts

namespace ECDSAAdd.Arithmetic.Paper935

private theorem zeroWork_mem (xs ws : List Wire) (b : ZeroBit)
    (hb : b∈List.zipWith ZeroBit.mk xs ws) : b.work∈ws := by
  induction xs generalizing ws with
  | nil => simp at hb
  | cons x xs ih =>
    cases ws with
    | nil => simp at hb
    | cons w ws =>
      simp only [List.zipWith_cons_cons,List.mem_cons] at hb
      rcases hb with rfl|hb
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ws hb)

/-- The actual post-stage candidate is valid from globally separated persistent
inputs and a shared work pool large enough for both sequential detectors. -/
theorem postCandidate_valid (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat)
    (positive : 0<width)
    (distinct : ([one,zf,frozen,fire,active]++inputs++record++work).Nodup)
    (space : postPoolSize inputs record width≤work.length)
    (offsetFits : armed=true → offset<2^record.length) :
    (postCandidate armed one zf frozen fire active inputs record work width offset).Valid := by
  have probeSpace : width+(inputs.toChunks width).length≤work.length :=
    (Nat.le_max_left _ _).trans space
  have recordSpace : record.length+1≤work.length := (Nat.le_max_right _ _).trans space
  cases work with
  | nil => simp at recordSpace
  | cons w ws =>
    have probeDistinct : ([one,zf]++inputs++(w::ws)).Nodup := by
      simp_all [List.nodup_append',List.disjoint_append_right]
    obtain ⟨bs,compiled⟩ := compileProbe_exists one zf inputs (w::ws) width positive probeDistinct probeSpace
    have probe := compileProbe_contract one zf inputs (w::ws) width bs compiled
    have ports := compileProbe_ports one zf inputs (w::ws) width bs compiled
    have identity := compileProbe_identity one zf inputs (w::ws) width bs compiled
    have recInputs := zeroViews_inputs record ws (by simpa using recordSpace)
    have compare : ([one,w]++(List.zipWith ZeroBit.mk record ws).flatMap ZeroBit.wires).Nodup := by
      apply zeroViews_prefixed_distinct
      clear recInputs compiled probe ports identity
      simp_all [List.nodup_append',List.disjoint_append_right]
    have remint : ([frozen,fire]++(List.zipWith ZeroBit.mk record ws).flatMap ZeroBit.wires).Nodup := by
      apply zeroViews_prefixed_distinct
      clear recInputs compiled probe ports identity compare
      simp_all [List.nodup_append',List.disjoint_append_right]
    have recDistinct : (record++ws).Nodup := by
      clear recInputs compiled probe ports identity compare remint
      simp_all [List.nodup_append',List.disjoint_append_right]
    have recPorts := (zeroViews_distinct record ws recDistinct).2
    have sep : List.Disjoint (one::(inputs++(w::ws))) (active::fire::frozen::record) := by
      clear recInputs compiled probe ports identity compare remint recPorts
      simp_all [List.nodup_append',List.disjoint_append_right,List.disjoint_comm,eq_comm]
    have stable (q : Wire) (hq : q∈one::BlockedZero.ports bs) :
        q≠active ∧ q≠fire ∧ q≠frozen ∧ q∉record := by
      have hm : q∈one::(inputs++(w::ws)) := by
        rcases List.mem_cons.mp hq with hq|hq
        · exact List.mem_cons.mpr (Or.inl hq)
        · exact List.mem_cons_of_mem _ (ports q hq)
      have away := List.disjoint_left.mp sep hm
      simpa only [List.mem_cons,not_or] using away
    have workMember (q : Wire) (hq : q∈(List.zipWith ZeroBit.mk record ws).map ZeroBit.work) : q∈ws := by
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
      exact zeroWork_mem record ws b hb
    have workFrame (q : Wire) (hq : q∈w::(List.zipWith ZeroBit.mk record ws).map ZeroBit.work) :
        q≠active ∧ q≠fire ∧ q≠frozen ∧ q∉record := by
      have hm : q∈w::ws := by
        rcases List.mem_cons.mp hq with hq|hq
        · exact List.mem_cons.mpr (Or.inl hq)
        · exact List.mem_cons_of_mem _ (workMember q hq)
      have away := List.disjoint_left.mp sep (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
      simpa only [List.mem_cons,not_or] using away
    have fireWork : fire∉(List.zipWith ZeroBit.mk record ws).map ZeroBit.work :=
      fun hm => (workFrame fire (List.mem_cons_of_mem _ hm)).2.1 rfl
    apply (postStaticCheck_iff _).mp
    simp only [postStaticCheck,postCandidate,WindowPostLayout.recordWires,List.drop_succ_cons,List.drop_zero,
      List.getD_cons_zero,recInputs,←identity]
    refine ⟨probe.1,?_,?_,?_,?_,?_,offsetFits,?_,?_,?_,?_,?_,?_,stable,compare,?_,?_,fireWork,workFrame,remint⟩
    all_goals clear recInputs compiled probe ports identity compare remint recPorts stable workFrame workMember fireWork
    all_goals simp_all [List.nodup_append',List.disjoint_append_right,eq_comm]

theorem compilePost_exists (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record work : List Wire) (width offset : Nat)
    (positive : 0<width)
    (distinct : ([one,zf,frozen,fire,active]++inputs++record++work).Nodup)
    (space : postPoolSize inputs record width≤work.length)
    (offsetFits : armed=true → offset<2^record.length) :
    ∃ P,compilePost armed one zf frozen fire active inputs record work width offset=some P := by
  have valid := postCandidate_valid armed one zf frozen fire active inputs record work width offset positive distinct space offsetFits
  have probeDistinct : ([one,zf]++inputs++work).Nodup := by
    clear valid
    simp_all [List.nodup_append',List.disjoint_append_right]
  obtain ⟨bs,compiled⟩ := compileProbe_exists one zf inputs work width positive probeDistinct ((Nat.le_max_left _ _).trans space)
  have probe := compileProbe_contract one zf inputs work width bs compiled
  have identity := compileProbe_identity one zf inputs work width bs compiled
  have inputsEq : BlockedZero.inputs (postCandidate armed one zf frozen fire active inputs record work width offset).blocks=inputs := by
    change BlockedZero.inputs (BlockedZero.chunks (probeCandidate inputs work width).1 (probeCandidate inputs work width).2)=inputs
    rw [←identity]
    exact probe.2
  have recordSpace : record.length+1≤work.length := (Nat.le_max_right _ _).trans space
  have recInputs := zeroViews_inputs record (work.drop 1) (by simp only [List.length_drop]; omega)
  have recEq : (postCandidate armed one zf frozen fire active inputs record work width offset).recordWires=record := recInputs
  have nonempty : work≠[] := by intro he; simp [he] at recordSpace
  refine ⟨postCandidate armed one zf frozen fire active inputs record work width offset,?_⟩
  unfold compilePost
  rw [if_pos ⟨valid,inputsEq,recEq,nonempty⟩]

/-- The real shared post-stage pool can be allocated and compiled under its
static capacity bound; no post-execution correctness oracle is required. -/
theorem compileBorrowedPost_exists (A : Arena) (armed : Bool) (one zf frozen fire active : Wire)
    (inputs record : List Wire) (width offset : Nat)
    (positive : 0<width)
    (distinct : ([one,zf,frozen,fire,active]++inputs++record).Nodup)
    (owned : ([one,zf,frozen,fire,active]++inputs++record).toFinset⊆A.live)
    (budget : A.live.card+postPoolSize inputs record width≤935)
    (offsetFits : armed=true → offset<2^record.length) :
    ∃ D work P,compileBorrowedPost A armed one zf frozen fire active inputs record width offset=some (D,work,P) := by
  obtain ⟨D,work,borrow⟩ := (A.borrowMany_capacity (postPoolSize inputs record width)).mpr budget
  have geometry := A.borrowMany_append D _ work _ borrow distinct owned
  have length := (A.borrowMany_contract D _ work borrow).1
  obtain ⟨P,compiled⟩ := compilePost_exists armed one zf frozen fire active inputs record work width offset
    positive geometry.1 (by rw [length]) offsetFits
  exact ⟨D,work,P,by simp [compileBorrowedPost,borrow,compiled]⟩

end ECDSAAdd.Arithmetic.Paper935
