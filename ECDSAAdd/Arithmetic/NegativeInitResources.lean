import ECDSAAdd.Arithmetic.NegativeInit
import ECDSAAdd.Math.ModularHalving

namespace ECDSAAdd.Arithmetic

theorem negativeInit_value (q R : Nat) (hq : 0<q) :
    (q-(R%q))%q = (-(R : ZMod q)).val := by
  letI : NeZero q := ⟨by omega⟩
  rw [ZMod.neg_val',ZMod.val_natCast]

theorem negativeInit_wires (L : ModLayout) (q : Nat) (src temp dst : List Wire)
    (hs : src.length=L.width+1) (ht : temp.length=L.width+1) (hd : dst.length=L.width+1) :
    wires (negativeInit L q src temp dst)=(src++temp++dst++L.wires).toFinset := by
  rw [negativeInit,wires_append,wires_append,reduceXor_wires L src temp q hs ht,
    negateXor_wires L temp dst q ht hd]
  ext w
  simp [or_left_comm]

theorem negativeInit_counts (L : ModLayout) (q : Nat) (src temp dst : List Wire)
    (hnd : L.wires.Nodup) (hs : src.length=L.width+1)
    (ht : temp.length=L.width+1) (hd : dst.length=L.width+1) :
    toffoliCount (negativeInit L q src temp dst)=30*L.width+24 ∧
    measurementCount (negativeInit L q src temp dst)=24*(L.width+1) := by
  have ha := modAdd_resources L hnd q
  have hb := modSub_resources L hnd q
  have hr := unaryModXor_counts L .x (modAdd L q) src temp hs ht
  have hn := unaryModXor_counts L .y (modSub L q) temp dst ht hd
  simp only [negativeInit,reduceXor,negateXor,toffoliCount_append,measurementCount_append,
    hr.1,hr.2,hn.1,hn.2,ha.1,ha.2.1,hb.1,hb.2.1]
  omega

theorem negativeInit_spec (L : ModLayout) (q : Nat) (src temp dst : List Wire)
    (hnd : (src++temp++dst++L.wires).Nodup)
    (hs : src.length=L.width+1) (ht : temp.length=L.width+1) (hd : dst.length=L.width+1)
    (X O : Nat) (hq0 : 0<q) (hq : q<2^L.width) (hx : X<2*q) :
    {{ src=X, temp=0, dst=O, L.wires=0 }} negativeInit L q src temp dst
    {{ src=X, temp=0, dst=(O ^^^ (-(X : ZMod q)).val), L.wires=0 }} := by
  intro s m h
  simp only [Holds.holds] at h ⊢
  have hh := List.nodup_append'.mp hnd
  have htd := (List.nodup_append'.mp hh.1).2.2
  have hsdis : src.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp htd (List.mem_append_left _ ha) hb)
  have htdis : temp.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp htd (List.mem_append_right _ ha) hb)
  have hwdis : L.wires.Disjoint dst := List.disjoint_left.mpr (fun _ ha hb =>
    List.disjoint_left.mp hh.2.2 (List.mem_append_right _ hb) ha)
  obtain ⟨hp,he,hz⟩ := negativeInit_correct L q src temp dst hnd hs ht hd hq0 hq s m
    (by simpa [h.1.1.1] using hx) h.1.1.2 h.2
  have keep (r : List Wire) (hr : r.Disjoint dst) :
      regValue r (run (negativeInit L q src temp dst) m s).basis=regValue r s.basis :=
    regValue_congr _ _ _ (fun w hm => he w (List.disjoint_left.mp hr hm))
  exact ⟨hp,⟨⟨(keep src hsdis).trans h.1.1.1,(keep temp htdis).trans h.1.1.2⟩,
    by simpa [h.1.2,h.1.1.1,negativeInit_value q X hq0] using hz⟩,(keep L.wires hwdis).trans h.2⟩

end ECDSAAdd.Arithmetic
