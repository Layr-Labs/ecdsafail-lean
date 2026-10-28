import ECDSAAdd.Arithmetic.UnaryModResources
import ECDSAAdd.Arithmetic.ConditionalXor

namespace ECDSAAdd.Arithmetic

/-- r 允许大于模数：先规范化，再取负；两次约减之间的临时值最终归零。 -/
def negativeInit (L : ModLayout) (q : Nat) (src temp dst : List Wire) : Program :=
  reduceXor L q src temp ++ negateXor L q temp dst ++ reduceXor L q src temp

theorem negativeInit_correct (L : ModLayout) (q : Nat) (src temp dst : List Wire)
    (hnd : (src ++ temp ++ dst ++ L.wires).Nodup)
    (hs : src.length=L.width+1) (ht : temp.length=L.width+1) (hd : dst.length=L.width+1)
    (hq0 : 0<q) (hq : q<2^L.width) (s : State) (m : List Bool)
    (hx : regValue src s.basis < 2*q) (hT : regValue temp s.basis=0)
    (hW : regValue L.wires s.basis=0) :
    (run (negativeInit L q src temp dst) m s).phase=s.phase ∧
    (∀ w, w∉dst → (run (negativeInit L q src temp dst) m s).basis w=s.basis w) ∧
    regValue dst (run (negativeInit L q src temp dst) m s).basis =
      regValue dst s.basis ^^^ ((q-(regValue src s.basis%q))%q) := by
  have h0 := List.nodup_append'.mp hnd
  have h1 := List.nodup_append'.mp h0.1
  have h2 := List.nodup_append'.mp h1.1
  have hst := h2.2.2
  have hsd : src.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp h1.2.2 (List.mem_append_left _ ha) hb)
  have htd : temp.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp h1.2.2 (List.mem_append_right _ ha) hb)
  have hwt : L.wires.Disjoint temp := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp h0.2.2 (by simp [hb]) ha)
  have hwd : L.wires.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp h0.2.2 (by simp [hb]) ha)
  have hred : (src++temp++L.wires).Nodup := List.nodup_append'.mpr
    ⟨h1.1,h0.2.1,List.disjoint_left.mpr (fun _ ha hb =>
      List.disjoint_left.mp h0.2.2 (List.mem_append_left _ ha) hb)⟩
  have hneg : (temp++dst++L.wires).Nodup := List.nodup_append'.mpr
    ⟨List.nodup_append'.mpr ⟨h2.2.1,h1.2.1,htd⟩,h0.2.1,List.disjoint_left.mpr (fun w ha hb => by
      rcases List.mem_append.mp ha with ht | hd
      · exact List.disjoint_left.mp h0.2.2 (by simp [ht]) hb
      · exact List.disjoint_left.mp h0.2.2 (by simp [hd]) hb)⟩
  let X := regValue src s.basis
  let O := regValue dst s.basis
  let R := X%q
  let N := (q-R)%q
  let P := PairFrame temp dst s.basis
  have reduction (T B : Nat) : Triple (P T B) (reduceXor L q src temp) (P (T ^^^ R) B) := by
    intro st ms h
    have hx' := PairFrame.read temp dst src s.basis st.basis T B h hst hsd
    have hw' := PairFrame.read temp dst L.wires s.basis st.basis T B h hwt hwd
    obtain ⟨hp,he,hz⟩ := reduceXor_correct L src temp hred hs ht q hq0 hq st ms
      (by simpa [hx'] using hx) (hw'.trans hW)
    exact ⟨hp,PairFrame.update_temp temp dst _ _ _ T B _ htd h he
      (by simpa [h.1,hx',R,X] using hz)⟩
  have negation : Triple (P R O) (negateXor L q temp dst) (P R (O ^^^ N)) := by
    intro st ms h
    have hw' := PairFrame.read temp dst L.wires s.basis st.basis R O h hwt hwd
    obtain ⟨hp,he,hz⟩ := negateXor_correct L temp dst hneg ht hd q hq0 hq st ms
      (by rw [h.1]; exact Nat.mod_lt X hq0) (hw'.trans hW)
    exact ⟨hp,PairFrame.update_dst temp dst _ _ _ R O _ htd h he
      (by simpa [h.1,h.2.1,N] using hz)⟩
  have first : Triple (P 0 O) (reduceXor L q src temp) (P R O) := by simpa using reduction 0 O
  have last : Triple (P R (O ^^^ N)) (reduceXor L q src temp) (P 0 (O ^^^ N)) := by
    simpa using reduction R (O ^^^ N)
  have proof := first.seq (negation.seq last)
  obtain ⟨hp,hf⟩ := proof s m ⟨hT,rfl,fun _ _ _ => rfl⟩
  have heq : negativeInit L q src temp dst =
      reduceXor L q src temp ++ (negateXor L q temp dst ++ reduceXor L q src temp) := by
    simp only [negativeInit,List.append_assoc]
  rw [heq]
  refine ⟨hp,?_,hf.2.1⟩
  intro w hw
  by_cases hm : w∈temp
  · exact ((regValue_zero _ _).mp hf.1 w hm).trans ((regValue_zero _ _).mp hT w hm).symm
  · exact hf.2.2 w hm hw

end ECDSAAdd.Arithmetic
