import ECDSAAdd.Submission.Entrant.Prelude

namespace ECDSAAdd.Entrant.LocalWireModel
open Arithmetic MeasuredCodec5

theorem run_concat (P Q : Program) (m : List Bool) (s : State) :
    run (P++Q) m s=run Q (m.drop (measurementCount P)) (run P m s) := by
  rw [run_append,run_take]

theorem reg_bit (r : List Wire) (s : BasisState) (q : Nat) (hq : q<r.length) :
    (regValue r s).testBit q=s (r.getD q 0) := by
  rw [Nat.testBit_eq_decide_div_mod_eq,←regValue_bit r q 0 s hq]
  cases s (r.getD q 0) <;> rfl

theorem range_bit (n : Nat) (s : BasisState) (q : Nat) (hq : q<n) :
    (regValue (List.range n) s).testBit q=s q := by
  rw [reg_bit _ _ _ (by simpa using hq)]
  simp [List.getD_eq_getElem?_getD,hq]

theorem model_eq (n : Nat) (P Q : Program) (hP : wires P⊆Finset.range n)
    (hQ : wires Q⊆Finset.range n) (s : State) (m : List Bool) (x : Nat)
    (hb : ∀q∈Finset.range n,s.basis q=bitsOf x q)
    (h : run P m ⟨s.phase,bitsOf x⟩=run Q m ⟨s.phase,bitsOf x⟩) :
    run P m s=run Q m s := by
  have p:=pool_run_agrees P (Finset.range n) hP m s ⟨s.phase,bitsOf x⟩ rfl hb
  have q:=pool_run_agrees Q (Finset.range n) hQ m s ⟨s.phase,bitsOf x⟩ rfl hb
  apply State.extensionality
  · exact p.1.trans ((congrArg State.phase h).trans q.1.symm)
  · funext w
    by_cases hw:w∈Finset.range n
    · exact (p.2 w hw).trans ((congrArg (fun t : State => t.basis w) h).trans (q.2 w hw).symm)
    · exact (run_preserves_outside P m s w (fun hp=>hw (hP hp))).trans
        (run_preserves_outside Q m s w (fun hq=>hw (hQ hq))).symm

def label {n : Nat} (f : Fin n→Wire) (q : Wire) : Wire := if h:q<n then f ⟨q,h⟩ else q

theorem label_injective {n : Nat} (f : Fin n→Wire) (hf : Function.Injective f) :
    ∀a∈Finset.range n,∀b∈Finset.range n,label f a=label f b → a=b := by
  intro a ha b hb e
  have ha' := Finset.mem_range.mp ha
  have hb' := Finset.mem_range.mp hb
  have eq : f ⟨a,ha'⟩=f ⟨b,hb'⟩ := by simpa only [label,dif_pos ha',dif_pos hb'] using e
  exact congrArg Fin.val (hf eq)

theorem renamed_eq {n : Nat} (f : Fin n→Wire) (hf : Function.Injective f)
    (P Q : Program) (hp:wires P⊆Finset.range n) (hq:wires Q⊆Finset.range n)
    (s : State) (m : List Bool)
    (he:run P m ⟨s.phase,fun q=>s.basis (label f q)⟩=
        run Q m ⟨s.phase,fun q=>s.basis (label f q)⟩) :
    run (renameProgram (label f) P) m s=run (renameProgram (label f) Q) m s := by
  let t:State:=⟨s.phase,fun q=>s.basis (label f q)⟩
  have pp:=run_rename_pool (label f) (Finset.range n) (label_injective f hf) P hp m t s rfl (fun _ _=>rfl)
  have qq:=run_rename_pool (label f) (Finset.range n) (label_injective f hf) Q hq m t s rfl (fun _ _=>rfl)
  apply State.extensionality
  · exact pp.1.trans ((congrArg State.phase he).trans qq.1.symm)
  · funext z
    by_cases hz:z∈(Finset.range n).image (label f)
    · obtain ⟨q,hq,rfl⟩:=Finset.mem_image.mp hz
      exact (pp.2 q hq).trans ((congrArg (fun st:State=>st.basis q) he).trans (qq.2 q hq).symm)
    · have absent (R : Program) (hr : wires R⊆Finset.range n) : z∉wires (renameProgram (label f) R) := by
        rw [renameProgram_support]
        intro hh
        obtain ⟨q,hqin,eq⟩:=Finset.mem_image.mp hh
        exact hz (Finset.mem_image.mpr ⟨q,hr hqin,eq⟩)
      exact (run_preserves_outside _ m s z (absent P hp)).trans
        (run_preserves_outside _ m s z (absent Q hq)).symm

theorem run_write_outside (p : Program) (port : Wire) (hp : port∉wires p)
    (s : State) (b : Bool) (m : List Bool) :
    run p m ⟨s.phase,writeBit s.basis port b⟩=
      ⟨(run p m s).phase,writeBit (run p m s).basis port b⟩ := by
  have loc := pool_run_agrees p (wires p) (by rfl) m
    ⟨s.phase,writeBit s.basis port b⟩ s rfl (by
      intro w hw
      exact Function.update_of_ne (show w≠port from fun he => hp (he ▸ hw)) _ _)
  apply State.extensionality
  · exact loc.1
  · funext w
    by_cases hw : w∈wires p
    · change _ = writeBit (run p m s).basis port b w
      rw [show writeBit (run p m s).basis port b w=(run p m s).basis w from
        Function.update_of_ne (show w≠port from fun he => hp (he ▸ hw)) _ _]
      exact loc.2 w hw
    · rw [run_preserves_outside p m _ w hw]
      by_cases he : w=port
      · subst w; simp [writeBit]
      · simp only [writeBit,Function.update_of_ne he]
        exact (run_preserves_outside p m s w hw).symm

theorem rename_toggle {n : Nat} (f : Fin n→Wire) (hf : Function.Injective f)
    (P : Program) (hp : wires P⊆Finset.range n) (target : Fin n) (s : State) (m : List Bool) (z : Bool)
    (he : run P m ⟨s.phase,fun q=>s.basis (label f q)⟩=
      ⟨s.phase,writeBit (fun q=>s.basis (label f q)) target.val (s.basis (f target) ^^ z)⟩) :
    run (renameProgram (label f) P) m s=
      ⟨s.phase,writeBit s.basis (f target) (s.basis (f target) ^^ z)⟩ := by
  have pp := run_rename_pool (label f) (Finset.range n) (label_injective f hf) P hp m
    ⟨s.phase,fun q=>s.basis (label f q)⟩ s rfl (fun _ _=>rfl)
  rw [he] at pp
  apply State.extensionality
  · exact pp.1
  · funext w
    by_cases hw : w∈(Finset.range n).image (label f)
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hw
      have ht : label f target.val=f target := by simp [label,target.isLt]
      have same : label f q=f target ↔ q=target.val := by
        constructor
        · intro e
          exact label_injective f hf q hq target.val (Finset.mem_range.mpr target.isLt) (e.trans ht.symm)
        · intro e; subst q; exact ht
      rw [pp.2 q hq]
      simp only [writeBit,Function.update_apply]
      by_cases eq : q=target.val
      · simp [eq,ht]
      · simp [eq,show label f q≠f target from fun h=>eq (same.mp h)]
    · have noP : w∉wires (renameProgram (label f) P) := by
        rw [renameProgram_support]
        intro h
        obtain ⟨q,hq,e⟩ := Finset.mem_image.mp h
        exact hw (Finset.mem_image.mpr ⟨q,hp hq,e⟩)
      have ne : w≠f target := by
        intro e
        apply hw
        refine Finset.mem_image.mpr ⟨target.val,Finset.mem_range.mpr target.isLt,?_⟩
        simpa [label,target.isLt] using e.symm
      rw [run_preserves_outside _ m s w noP]
      simp [writeBit,ne]

theorem listPorts_injective (r : List Wire) (hn : r.Nodup) {n : Nat} (hl : r.length=n) :
    Function.Injective (fun q : Fin n => r.getD q.val 0) := by
  intro a b eq
  have ha : a.val<r.length := by rw [hl]; exact a.isLt
  have hb : b.val<r.length := by rw [hl]; exact b.isLt
  dsimp only at eq
  rw [List.getD_eq_getElem _ _ ha,List.getD_eq_getElem _ _ hb] at eq
  exact Fin.ext (hn.getElem_inj_iff.mp eq)

end ECDSAAdd.Entrant.LocalWireModel
