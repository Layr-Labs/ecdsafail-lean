import ECDSAAdd.Arithmetic.Paper935.RowResize
import ECDSAAdd.Arithmetic.Paper935.WindowSchedule
import ECDSAAdd.Framework.GateInverse

namespace ECDSAAdd.Arithmetic.Paper935

/-- Sign-extend a public suffix of new payload wires. Its reverse releases
that suffix when the represented integer fits the smaller public window. -/
def growRow (sign : Wire) (extra : List Wire) : Program :=
  extra.flatMap (resizeBit sign)

def shrinkRow (sign : Wire) (extra : List Wire) : Program :=
  (growRow sign extra).reverse

theorem growRow_proper (sign : Wire) (extra : List Wire) (hs : sign∉extra) :
    ProperProgram (growRow sign extra) := by
  intro g hg
  obtain ⟨w,hw,hg⟩ := List.mem_flatMap.mp hg
  simp only [resizeBit,List.mem_singleton] at hg
  subst g
  exact fun he => hs (he ▸ hw)

theorem growRow_frame (sign : Wire) (extra : List Wire) (s : State) (m : List Bool) :
    (run (growRow sign extra) m s).phase=s.phase ∧
    ∀ w,w∉extra → (run (growRow sign extra) m s).basis w=s.basis w := by
  induction extra generalizing s m with
  | nil => simp [growRow,run]
  | cons q qs ih =>
    simp only [growRow,List.flatMap_cons,resizeBit,List.singleton_append,run]
    have h := ih ⟨s.phase,writeBit s.basis q (s.basis q ^^ s.basis sign)⟩ m
    refine ⟨h.1,?_⟩
    intro w hw
    exact (h.2 w (fun h => hw (List.mem_cons_of_mem _ h))).trans
      (Function.update_of_ne (by intro he; exact hw (by simp [he])) _ _)

theorem growRow_values (lo extra : List Wire) (sign : Wire)
    (hn : (sign::(lo++extra)).Nodup) (s : State) (m : List Bool)
    (hz : ∀ w∈extra,s.basis w=false) :
    signedRegValue ((lo++extra)++[sign]) (run (growRow sign extra) m s).basis=
      signedRegValue (lo++[sign]) s.basis := by
  induction extra generalizing lo s m with
  | nil => simp [growRow,run]
  | cons q qs ih =>
    have hsq : sign≠q := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
    have hql : q∉lo := by
      have hd := (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.2
      exact fun hq => hd q hq q (by simp) rfl
    have hqq : q∉qs := (List.nodup_cons.mp (List.nodup_append.mp (List.nodup_cons.mp hn).2).2.1).1
    let t := run (resizeBit sign q) m s
    have first := rowGrow_run lo sign q hql hsq s m (hz q (by simp))
    have hn' : (sign::((lo++[q])++qs)).Nodup := by simpa only [List.append_assoc,List.singleton_append] using hn
    have tail := ih (lo++[q]) hn' t m (by
      intro w hw
      rw [first.2.1 w (fun he => hqq (he ▸ hw))]
      exact hz w (by simp [hw]))
    simpa [growRow,run_append,run_take,resizeBit,measurementCount,t,List.append_assoc] using tail.trans first.2.2

theorem shrinkRow_eq (sign : Wire) (extra : List Wire) :
    shrinkRow sign extra=growRow sign extra.reverse := by
  simp [shrinkRow,growRow,List.reverse_flatMap,Function.comp_def,resizeBit]
  rfl

theorem shrinkRow_frame (sign : Wire) (extra : List Wire) (s : State) (m : List Bool) :
    (run (shrinkRow sign extra) m s).phase=s.phase ∧
    ∀ w,w∉extra → (run (shrinkRow sign extra) m s).basis w=s.basis w := by
  rw [shrinkRow_eq]
  simpa only [List.mem_reverse] using growRow_frame sign extra.reverse s m

theorem shrinkRow_values (lo extra : List Wire) (sign : Wire)
    (hn : (sign::(lo++extra)).Nodup) (s : State) (m : List Bool)
    (hfit : PayloadFits lo.length (signedRegValue ((lo++extra)++[sign]) s.basis)) :
    (∀ w∈extra,(run (shrinkRow sign extra) m s).basis w=false) ∧
    signedRegValue (lo++[sign]) (run (shrinkRow sign extra) m s).basis=
      signedRegValue ((lo++extra)++[sign]) s.basis := by
  induction extra using List.reverseRecOn generalizing lo s m with
  | nil => simp [shrinkRow,growRow,run]
  | append_singleton extra q ih =>
    have hn' : (sign::(lo++extra)).Nodup :=
      List.Nodup.of_append_left (l₂ := [q]) (by simpa only [List.cons_append,List.append_assoc] using hn)
    have hd : ((lo++extra)++[q]).Nodup := by
      simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
    have hq : q∉lo++extra := by
      intro h
      exact (List.nodup_append.mp hd).2.2 q h q (by simp) rfl
    have hsq : sign≠q := fun he => (List.nodup_cons.mp hn).1 (by simp [he])
    have hfit' : PayloadFits (lo++extra).length
        (signedRegValue (((lo++extra)++[q])++[sign]) s.basis) := by
      simpa only [List.length_append,List.append_assoc] using
        hfit.mono (Nat.le_add_right lo.length extra.length)
    have bit := rowShrink_bit_of_fits (lo++extra) sign q s.basis hfit'.1 hfit'.2
    let t := run (resizeBit sign q) m s
    have first := rowShrink_run (lo++extra) sign q hq hsq s m bit
    have fit : PayloadFits lo.length (signedRegValue ((lo++extra)++[sign]) t.basis) := by
      rw [first.2.2.2]
      simpa only [List.append_assoc] using hfit
    have tail := ih lo hn' t m fit
    have frame := shrinkRow_frame sign extra t m
    have program : shrinkRow sign (extra++[q])=resizeBit sign q++shrinkRow sign extra := by
      simp [shrinkRow,growRow,List.flatMap_append,resizeBit]
    rw [program,run_append,run_take]
    simp only [resizeBit,measurementCount,List.drop_zero]
    change (∀ w∈extra++[q],(run (shrinkRow sign extra) m t).basis w=false) ∧ _
    refine ⟨?_,?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with hw|hw
      · exact tail.1 w hw
      · have he : w=q := by simpa using hw
        subst w
        exact (frame.2 q (fun h => hq (List.mem_append_right _ h))).trans first.2.2.1
    · exact tail.2.trans (by simpa only [List.append_assoc] using first.2.2.2)

theorem rowWindow_roundtrip (sign : Wire) (extra : List Wire) (hs : sign∉extra)
    (s : State) (m n : List Bool) :
    run (shrinkRow sign extra) n (run (growRow sign extra) m s)=s := by
  exact run_reverse_proper _ (growRow_proper sign extra hs) s m n

theorem rowWindow_cost (sign : Wire) (extra : List Wire) :
    toffoliCount (growRow sign extra)=0 ∧ measurementCount (growRow sign extra)=0 ∧
    toffoliCount (shrinkRow sign extra)=0 ∧ measurementCount (shrinkRow sign extra)=0 := by
  have grow (xs : List Wire) : toffoliCount (growRow sign xs)=0 ∧ measurementCount (growRow sign xs)=0 := by
    induction xs with
    | nil => simp [growRow,toffoliCount,measurementCount]
    | cons q qs ih => simpa [growRow,resizeBit,toffoliCount,measurementCount] using ih
  rw [shrinkRow_eq]
  exact ⟨(grow extra).1,(grow extra).2,(grow extra.reverse).1,(grow extra.reverse).2⟩

theorem growRow_support (sign : Wire) (extra : List Wire) :
    wires (growRow sign extra)⊆insert sign extra.toFinset := by
  induction extra with
  | nil => simp [growRow,wires]
  | cons q qs ih =>
    intro w hw
    simp only [growRow,List.flatMap_cons,resizeBit,List.singleton_append,wires,Instr.wires,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with (rfl|rfl)|hw
    · simp
    · simp
    · have h := ih hw
      simp only [Finset.mem_insert,List.mem_toFinset] at h ⊢
      rcases h with h|h <;> simp [h]

theorem shrinkRow_release (A : Arena) (lo extra : List Wire) (sign : Wire)
    (hn : (sign::(lo++extra)).Nodup) (s : State) (m : List Bool)
    (hready : A.Ready s.basis) (hown : extra.toFinset⊆A.live)
    (hfit : PayloadFits lo.length (signedRegValue ((lo++extra)++[sign]) s.basis)) :
    ∃ B, A.release extra.toFinset (run (shrinkRow sign extra) m s).basis=some B ∧
      B.Ready (run (shrinkRow sign extra) m s).basis ∧
      signedRegValue (lo++[sign]) (run (shrinkRow sign extra) m s).basis=
        signedRegValue ((lo++extra)++[sign]) s.basis := by
  have vals := shrinkRow_values lo extra sign hn s m hfit
  have frame := shrinkRow_frame sign extra s m
  have clean : A.Ready (run (shrinkRow sign extra) m s).basis := by
    intro q hq hout
    rw [frame.2 q (fun h => hout (hown (List.mem_toFinset.mpr h)))]
    exact hready q hq hout
  obtain ⟨B,hB⟩ := (A.release_success extra.toFinset _).mpr
    ⟨hown,fun q hq => vals.1 q (List.mem_toFinset.mp hq)⟩
  exact ⟨B,hB,A.release_ready B _ _ clean hB,vals.2⟩

end ECDSAAdd.Arithmetic.Paper935
