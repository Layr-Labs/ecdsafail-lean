import ECDSAAdd.Arithmetic.Registers

namespace ECDSAAdd.Arithmetic

/-- A terminal signed trajectory has rails (0,1) or (1,0), with orientation
stored separately. Clear both low bits so the entire rail workspace can be
borrowed during field replay. The same Clifford program restores the rails. -/
def skywalkTerminalClear (g a b : Wire) : Program := [.CX g a,.X a,.CX g b]

theorem skywalkTerminalClear_correct (g a b : Wire) (hn : [g,a,b].Nodup)
    (s : State) (m : List Bool) :
    (run (skywalkTerminalClear g a b) m s).phase=s.phase ∧
    (∀ q, q≠a → q≠b → (run (skywalkTerminalClear g a b) m s).basis q=s.basis q) ∧
    (run (skywalkTerminalClear g a b) m s).basis a=(!(s.basis a ^^ s.basis g)) ∧
    (run (skywalkTerminalClear g a b) m s).basis b=(s.basis b ^^ s.basis g) := by
  have hd : g≠a ∧ g≠b ∧ a≠b := by simpa [and_assoc] using hn
  refine ⟨rfl,?_,?_,?_⟩
  · intro q hqa hqb
    simp [skywalkTerminalClear,run,writeBit,hqa,hqb]
  · simp [skywalkTerminalClear,run,writeBit,hd.1,hd.2.2]
  · simp [skywalkTerminalClear,run,writeBit,hd.1,Ne.symm hd.2.2]

theorem skywalkTerminalClear_spec (g a b : Wire) (hn : [g,a,b].Nodup) (G : Bool) :
    {{ g=G,a=(!G),b=G }} skywalkTerminalClear g a b {{ g=G,a=false,b=false }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hd : g≠a ∧ g≠b ∧ a≠b := by simpa [and_assoc] using hn
  obtain ⟨hp,he,ha,hb⟩ := skywalkTerminalClear_correct g a b hn s m
  refine ⟨hp,⟨(he g hd.1 hd.2.1).trans h.1.1,?_⟩,?_⟩
  · rw [ha,h.1.2,h.1.1]
    cases G <;> rfl
  · rw [hb,h.2,h.1.1]
    cases G <;> rfl

theorem skywalkTerminalClear_twice (g a b : Wire) (hn : [g,a,b].Nodup)
    (s : State) (m1 m2 : List Bool) :
    run (skywalkTerminalClear g a b) m2 (run (skywalkTerminalClear g a b) m1 s)=s := by
  have hd : g≠a ∧ g≠b ∧ a≠b := by simpa [and_assoc] using hn
  obtain ⟨p1,e1,a1,b1⟩ := skywalkTerminalClear_correct g a b hn s m1
  obtain ⟨p2,e2,a2,b2⟩ := skywalkTerminalClear_correct g a b hn
    (run (skywalkTerminalClear g a b) m1 s) m2
  have hg := e1 g hd.1 hd.2.1
  apply congrArg₂ State.mk
  · exact p2.trans p1
  · funext q
    change (run (skywalkTerminalClear g a b) m2
      (run (skywalkTerminalClear g a b) m1 s)).basis q=s.basis q
    by_cases hqa : q=a
    · subst q
      rw [a2,a1,hg]
      cases s.basis a <;> cases s.basis g <;> rfl
    by_cases hqb : q=b
    · subst q
      rw [b2,b1,hg]
      cases s.basis b <;> cases s.basis g <;> rfl
    exact (e2 q hqa hqb).trans (e1 q hqa hqb)

/-- Whole-word interface: all high bits are already zero because each rail
has value zero or one. No high-word conditional swap is required. -/
theorem skywalkTerminalClear_words (g a b : Wire) (aTail bTail : List Wire)
    (hn : (g::a::b::(aTail++bTail)).Nodup) (G : Bool) :
    {{ g=G,(a::aTail)=(if G then 0 else 1),(b::bTail)=(if G then 1 else 0) }}
      skywalkTerminalClear g a b {{ g=G,(a::aTail)=0,(b::bTail)=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hgates : [g,a,b].Nodup := by
    have hh := hn
    simp only [List.nodup_cons,List.mem_cons,List.mem_append,not_or] at hh
    simp [hh.1.1,hh.1.2.1,hh.2.1.1]
  have hav := h.1.2
  have hbv := h.2
  change (if s.basis a then 1 else 0)+2*regValue aTail s.basis=(if G then 0 else 1) at hav
  change (if s.basis b then 1 else 0)+2*regValue bTail s.basis=(if G then 1 else 0) at hbv
  have ha0 : s.basis a=(!G) ∧ regValue aTail s.basis=0 := by
    cases G <;> cases ha : s.basis a <;> simp [ha] at hav ⊢ <;> omega
  have hb0 : s.basis b=G ∧ regValue bTail s.basis=0 := by
    cases G <;> cases hb : s.basis b <;> simp [hb] at hbv ⊢ <;> omega
  obtain ⟨hp,hpost⟩ := skywalkTerminalClear_spec g a b hgates G s m ⟨⟨h.1.1,ha0.1⟩,hb0.1⟩
  have keep (q : Wire) (hq : q∈aTail++bTail) :
      (run (skywalkTerminalClear g a b) m s).basis q=s.basis q := by
    have hq0 : q≠a ∧ q≠b := by
      have hd := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
      have hb := (List.nodup_cons.mp (List.nodup_cons.mp (List.nodup_cons.mp hn).2).2).1
      constructor
      · intro he
        subst q
        exact hd (List.mem_cons_of_mem _ hq)
      · intro he
        subst q
        exact hb hq
    exact (skywalkTerminalClear_correct g a b hgates s m).2.1 q hq0.1 hq0.2
  have hat := (regValue_congr aTail _ _ (fun q hq => keep q (List.mem_append_left _ hq))).trans ha0.2
  have hbt := (regValue_congr bTail _ _ (fun q hq => keep q (List.mem_append_right _ hq))).trans hb0.2
  simp only [Holds.holds] at hpost
  refine ⟨hp,⟨hpost.1.1,?_⟩,?_⟩
  · change (if (run (skywalkTerminalClear g a b) m s).basis a then 1 else 0)+
      2*regValue aTail (run (skywalkTerminalClear g a b) m s).basis=0
    rw [hpost.1.2,hat]
    rfl
  · change (if (run (skywalkTerminalClear g a b) m s).basis b then 1 else 0)+
      2*regValue bTail (run (skywalkTerminalClear g a b) m s).basis=0
    rw [hpost.2,hbt]
    rfl

theorem skywalkTerminalClear_counts (g a b : Wire) :
    toffoliCount (skywalkTerminalClear g a b)=0 ∧
    measurementCount (skywalkTerminalClear g a b)=0 := by
  simp [skywalkTerminalClear,toffoliCount,measurementCount]

theorem skywalkTerminalClear_wires (g a b : Wire) :
    wires (skywalkTerminalClear g a b)=[g,a,b].toFinset := by
  ext q
  simp [skywalkTerminalClear,wires,Instr.wires]

end ECDSAAdd.Arithmetic
