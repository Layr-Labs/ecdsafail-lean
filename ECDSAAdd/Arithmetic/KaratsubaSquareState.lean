import ECDSAAdd.Arithmetic.KaratsubaSquareProof

namespace ECDSAAdd.Arithmetic

/-- The retained half-squares and temporary registers at composition boundaries. -/
structure KaratsubaValues (L : KaratsubaSquareLayout) (lo hi av dv cv zv sv : Nat)
    (s : BasisState) : Prop where
  low : regValue L.low s=lo
  high : regValue L.high s=hi
  a : regValue L.a s=av
  d : regValue L.d s=dv
  c : regValue L.c s=cv
  z : regValue L.z s=zv
  sum : regValue L.sum s=sv
  pad : regValue L.pad s=0
  mask : regValue L.mask s=0
  carry : regValue L.carry s=0
  cin : s L.cin=false

namespace KaratsubaValues

private theorem keep (L : KaratsubaSquareLayout) (h : L.Valid) (r dst : List Wire)
    (hc : ∀ w,r.count w+dst.count w≤L.wires.count w) (s u : BasisState)
    (hf : ∀ w,w∉dst→u w=s w) : regValue r u=regValue r s := by
  apply regValue_congr
  intro w hw
  apply hf
  intro hd
  have hn := List.nodup_iff_count.mp h.nodup w
  have hr := List.count_pos_iff.mpr hw
  have ht := List.count_pos_iff.mpr hd
  have hh := hc w
  omega

theorem update_a (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.a u=V) (hf : ∀ w,w∉L.a→u w=s w) :
    KaratsubaValues L lo hi V dv cv zv sv u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.a.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.a hc s u hf
  refine ⟨?_,?_,hv,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.d (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.d
  · apply Eq.trans (same L.c (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.c
  · apply Eq.trans (same L.z (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.z
  · apply Eq.trans (same L.sum (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.sum
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

theorem update_d (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.d u=V) (hf : ∀ w,w∉L.d→u w=s w) :
    KaratsubaValues L lo hi av V cv zv sv u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.d.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.d hc s u hf
  refine ⟨?_,?_,?_,hv,?_,?_,?_,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.a (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.a
  · apply Eq.trans (same L.c (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.c
  · apply Eq.trans (same L.z (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.z
  · apply Eq.trans (same L.sum (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.sum
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

theorem update_c (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.c u=V) (hf : ∀ w,w∉L.c→u w=s w) :
    KaratsubaValues L lo hi av dv V zv sv u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.c.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.c hc s u hf
  refine ⟨?_,?_,?_,?_,hv,?_,?_,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.a (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.a
  · apply Eq.trans (same L.d (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.d
  · apply Eq.trans (same L.z (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.z
  · apply Eq.trans (same L.sum (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.sum
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

theorem update_z (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.z u=V) (hf : ∀ w,w∉L.z→u w=s w) :
    KaratsubaValues L lo hi av dv cv V sv u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.z.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.z hc s u hf
  refine ⟨?_,?_,?_,?_,?_,hv,?_,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.a (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.a
  · apply Eq.trans (same L.d (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.d
  · apply Eq.trans (same L.c (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.c
  · apply Eq.trans (same L.sum (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.sum
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

theorem update_sum (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv V : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv cv zv sv s)
    (hv : regValue L.sum u=V) (hf : ∀ w,w∉L.sum→u w=s w) :
    KaratsubaValues L lo hi av dv cv zv V u := by
  have same (r : List Wire) (hc : ∀ w,r.count w+L.sum.count w≤L.wires.count w) :
      regValue r u=regValue r s := keep L h r L.sum hc s u hf
  refine ⟨?_,?_,?_,?_,?_,?_,hv,?_,?_,?_,?_⟩
  · apply Eq.trans (same L.low (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.low
  · apply Eq.trans (same L.high (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.high
  · apply Eq.trans (same L.a (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.a
  · apply Eq.trans (same L.d (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.d
  · apply Eq.trans (same L.c (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.c
  · apply Eq.trans (same L.z (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.z
  · apply Eq.trans (same L.pad (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.pad
  · apply Eq.trans (same L.mask (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.mask
  · apply Eq.trans (same L.carry (by
      intro w; simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append]; omega)) hs.carry
  · apply Eq.trans (hf L.cin (by
      intro hw
      have hh := List.nodup_iff_count.mp h.nodup L.cin
      have ht := List.count_pos_iff.mpr hw
      simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh
      simp only [beq_self_eq_true,ite_true] at hh
      omega)) hs.cin

end KaratsubaValues

theorem karatsuba_squareLow_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi _av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi 0 dv cv zv sv) L.squareLow
      (KaratsubaValues L lo hi (lo^2) dv cv zv sv) := by
  have hn : (L.cin::L.low++L.a++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.a.length=2*L.low.length := by simp [h.a_length,h.low_length]
  have hp : L.low.length-1≤L.pad.length := by simp [h.low_length,h.pad_length]
  have hm : 2*(L.low.length-1)≤L.mask.length := by simp [h.low_length,h.mask_length]
  have hk : 2*(L.low.length-1)-1≤L.carry.length := by simp [h.low_length,h.carry_length]
  intro s m hs
  have hr := triangularSquare_spec L.low L.a L.pad L.mask L.carry L.cin
    hn hd hp hm hk lo s m ⟨⟨⟨⟨⟨hs.low,hs.a⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquare_frame L.low L.a L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m hs.a hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_a L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_clearLow_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi _av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi (lo^2) dv cv zv sv) L.clearLow
      (KaratsubaValues L lo hi 0 dv cv zv sv) := by
  have hn : (L.cin::L.low++L.a++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.a.length=2*L.low.length := by simp [h.a_length,h.low_length]
  have hp : L.low.length-1≤L.pad.length := by simp [h.low_length,h.pad_length]
  have hm : 2*(L.low.length-1)≤L.mask.length := by simp [h.low_length,h.mask_length]
  have hk : 2*(L.low.length-1)-1≤L.carry.length := by simp [h.low_length,h.carry_length]
  intro s m hs
  have hr := triangularSquareClear_spec L.low L.a L.pad L.mask L.carry L.cin
    hn hd hp hm hk lo s m ⟨⟨⟨⟨⟨hs.low,hs.a⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquareClear_frame L.low L.a L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m (by simpa [hs.low] using hs.a) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_a L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_squareHigh_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av _dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av 0 cv zv sv) L.squareHigh
      (KaratsubaValues L lo hi av (hi^2) cv zv sv) := by
  have hn : (L.cin::L.high++L.d++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.d.length=2*L.high.length := by simp [h.d_length,h.high_length]
  have hp : L.high.length-1≤L.pad.length := by simp [h.high_length,h.pad_length]
  have hm : 2*(L.high.length-1)≤L.mask.length := by simp [h.high_length,h.mask_length]
  have hk : 2*(L.high.length-1)-1≤L.carry.length := by simp [h.high_length,h.carry_length]
  intro s m hs
  have hr := triangularSquare_spec L.high L.d L.pad L.mask L.carry L.cin
    hn hd hp hm hk hi s m ⟨⟨⟨⟨⟨hs.high,hs.d⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquare_frame L.high L.d L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m hs.d hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_d L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_clearHigh_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av _dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av (hi^2) cv zv sv) L.clearHigh
      (KaratsubaValues L lo hi av 0 cv zv sv) := by
  have hn : (L.cin::L.high++L.d++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.d.length=2*L.high.length := by simp [h.d_length,h.high_length]
  have hp : L.high.length-1≤L.pad.length := by simp [h.high_length,h.pad_length]
  have hm : 2*(L.high.length-1)≤L.mask.length := by simp [h.high_length,h.mask_length]
  have hk : 2*(L.high.length-1)-1≤L.carry.length := by simp [h.high_length,h.carry_length]
  intro s m hs
  have hr := triangularSquareClear_spec L.high L.d L.pad L.mask L.carry L.cin
    hn hd hp hm hk hi s m ⟨⟨⟨⟨⟨hs.high,hs.d⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquareClear_frame L.high L.d L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m (by simpa [hs.high] using hs.d) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_d L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_squareSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv _cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv 0 zv sv) L.squareSum
      (KaratsubaValues L lo hi av dv (sv^2) zv sv) := by
  have hn : (L.cin::L.sum++L.c++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.c.length=2*L.sum.length := by simp [h.c_length,h.sum_length]
  have hp : L.sum.length-1≤L.pad.length := by simp [h.sum_length,h.pad_length]
  have hm : 2*(L.sum.length-1)≤L.mask.length := by simp [h.sum_length,h.mask_length]
  have hk : 2*(L.sum.length-1)-1≤L.carry.length := by simp [h.sum_length,h.carry_length]
  intro s m hs
  have hr := triangularSquare_spec L.sum L.c L.pad L.mask L.carry L.cin
    hn hd hp hm hk sv s m ⟨⟨⟨⟨⟨hs.sum,hs.c⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquare_frame L.sum L.c L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m hs.c hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_c L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_clearSquareSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv _cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv (sv^2) zv sv) L.clearSquareSum
      (KaratsubaValues L lo hi av dv 0 zv sv) := by
  have hn : (L.cin::L.sum++L.c++L.pad++L.mask++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  have hd : L.c.length=2*L.sum.length := by simp [h.c_length,h.sum_length]
  have hp : L.sum.length-1≤L.pad.length := by simp [h.sum_length,h.pad_length]
  have hm : 2*(L.sum.length-1)≤L.mask.length := by simp [h.sum_length,h.mask_length]
  have hk : 2*(L.sum.length-1)-1≤L.carry.length := by simp [h.sum_length,h.carry_length]
  intro s m hs
  have hr := triangularSquareClear_spec L.sum L.c L.pad L.mask L.carry L.cin
    hn hd hp hm hk sv s m ⟨⟨⟨⟨⟨hs.sum,hs.c⟩,hs.pad⟩,hs.mask⟩,hs.carry⟩,hs.cin⟩
  have hf := triangularSquareClear_frame L.sum L.c L.pad L.mask L.carry L.cin
    hn hd hp hm hk s m (by simpa [hs.sum] using hs.c) hs.pad hs.mask hs.carry hs.cin
  exact ⟨hr.1,KaratsubaValues.update_c L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1.1.1.1.2 hf⟩

theorem karatsuba_prepareSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv 0) L.prepareSum
      (KaratsubaValues L lo hi av dv cv zv (lo+hi)) := by
  intro s m hs
  have hr := (karatsuba_sum_correct L h s.basis hs.pad hs.carry hs.cin).1 s m
    ⟨by simpa [hs.low,hs.high] using hs.sum,fun _ _ => rfl⟩
  have hv : regValue L.sum (run L.prepareSum m s).basis=(lo+hi) := by
    simpa [hs.low,hs.high] using hr.2.1
  exact ⟨hr.1,KaratsubaValues.update_sum L h _ _ _ _ _ _ _ _ _ _ hs hv hr.2.2⟩

theorem karatsuba_clearSum_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv (lo+hi)) L.clearSum
      (KaratsubaValues L lo hi av dv cv zv 0) := by
  intro s m hs
  have hr := (karatsuba_sum_correct L h s.basis hs.pad hs.carry hs.cin).2 s m
    ⟨by simpa [hs.low,hs.high] using hs.sum,fun _ _ => rfl⟩
  have hv : regValue L.sum (run L.clearSum m s).basis=0 := by
    simpa [hs.low,hs.high] using hr.2.1
  exact ⟨hr.1,KaratsubaValues.update_sum L h _ _ _ _ _ _ _ _ _ _ hs hv hr.2.2⟩


theorem karatsuba_copySquares_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv 0 sv) L.copySquares
      (KaratsubaValues L lo hi av dv cv (av+2^256*dv) sv) ∧
    Triple (KaratsubaValues L lo hi av dv cv (av+2^256*dv) sv) L.copySquares
      (KaratsubaValues L lo hi av dv cv 0 sv) := by
  constructor
  · intro s m hs
    have hr := (karatsuba_copySquares_frame L h s.basis).1 s m ⟨hs.z,fun _ _=>rfl⟩
    exact ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs
      (by simpa [hs.a,hs.d] using hr.2.1) hr.2.2⟩
  · intro s m hs
    have hr := (karatsuba_copySquares_frame L h s.basis).2 s m
      ⟨by simpa [hs.a,hs.d] using hs.z,fun _ _=>rfl⟩
    exact ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs hr.2.1 hr.2.2⟩

/-- Full-word value after a modular operation in its high 384-bit slice. -/
def karatsubaHighValue (sub : Bool) (v a : Nat) : Nat :=
  v%2^128+2^128*(if sub then (v/2^128+2^384-a)%2^384 else (v/2^128+a)%2^384)

theorem karatsuba_high_a_spec (sub : Bool) (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv sv)
      (if sub then subInPlace (L.a++L.pad) (L.z.drop 128) L.carry L.cin
       else addInPlace (L.a++L.pad) (L.z.drop 128) L.carry L.cin)
      (KaratsubaValues L lo hi av dv cv (karatsubaHighValue sub zv av) sv) := by
  have hn : (L.cin::(L.a++L.pad)++L.z++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  intro s m hs
  have pv : regValue (L.pad) s.basis=0 := by
    exact hs.pad
  have hr := karatsuba_high_correct sub (L.a++L.pad) L.z L.carry L.cin hn h.z_length
    (by simp [h.a_length,h.pad_length]) h.carry_length s m hs.carry hs.cin
  refine ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs ?_ hr.2.2⟩
  simpa only [karatsubaHighValue,regValue_append,pv,Nat.mul_zero,Nat.add_zero,hs.z,hs.a] using hr.2.1

theorem karatsuba_high_d_spec (sub : Bool) (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv sv)
      (if sub then subInPlace (L.d++L.pad) (L.z.drop 128) L.carry L.cin
       else addInPlace (L.d++L.pad) (L.z.drop 128) L.carry L.cin)
      (KaratsubaValues L lo hi av dv cv (karatsubaHighValue sub zv dv) sv) := by
  have hn : (L.cin::(L.d++L.pad)++L.z++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  intro s m hs
  have pv : regValue (L.pad) s.basis=0 := by
    exact hs.pad
  have hr := karatsuba_high_correct sub (L.d++L.pad) L.z L.carry L.cin hn h.z_length
    (by simp [h.d_length,h.pad_length]) h.carry_length s m hs.carry hs.cin
  refine ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs ?_ hr.2.2⟩
  simpa only [karatsubaHighValue,regValue_append,pv,Nat.mul_zero,Nat.add_zero,hs.z,hs.d] using hr.2.1

theorem karatsuba_high_c_spec (sub : Bool) (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv zv sv : Nat) :
    Triple (KaratsubaValues L lo hi av dv cv zv sv)
      (if sub then subInPlace (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin
       else addInPlace (L.c++L.pad.take 126) (L.z.drop 128) L.carry L.cin)
      (KaratsubaValues L lo hi av dv cv (karatsubaHighValue sub zv cv) sv) := by
  have hn : (L.cin::(L.c++L.pad.take 126)++L.z++L.carry).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp h.nodup w
    have hp := (List.take_sublist 126 L.pad).count_le w
    simp only [KaratsubaSquareLayout.wires,List.count_cons,List.count_append] at hh ⊢; omega
  intro s m hs
  have pv : regValue (L.pad.take 126) s.basis=0 := by
    exact (regValue_zero _ _).mpr (fun w hw=>(regValue_zero _ _).mp hs.pad w (List.mem_of_mem_take hw))
  have hr := karatsuba_high_correct sub (L.c++L.pad.take 126) L.z L.carry L.cin hn h.z_length
    (by simp [h.c_length,h.pad_length]) h.carry_length s m hs.carry hs.cin
  refine ⟨hr.1,KaratsubaValues.update_z L h _ _ _ _ _ _ _ _ _ _ hs ?_ hr.2.2⟩
  simpa only [karatsubaHighValue,regValue_append,pv,Nat.mul_zero,Nat.add_zero,hs.z,hs.c] using hr.2.1


private theorem high_add (v a : Nat) :
    karatsubaHighValue false v a=(v+2^128*a)%2^512 := by
  unfold karatsubaHighValue
  norm_num only [Bool.false_eq_true,if_false]
  omega

private theorem high_sub (v a : Nat) (hv : v<2^512) (ha : a<2^384) :
    karatsubaHighValue true v a=(v+2^512-2^128*a)%2^512 := by
  unfold karatsubaHighValue
  norm_num only [if_true]
  omega

private theorem high_bound (sub : Bool) (v a : Nat) :
    karatsubaHighValue sub v a<2^512 := by
  unfold karatsubaHighValue
  split <;> omega

private theorem combine_value (av dv cv initial result : Nat)
    (ha : av<2^384) (hd : dv<2^384)
    (_hi : initial<2^512) (hr : result<2^512)
    (he : initial+2^128*cv=result+2^128*av+2^128*dv) :
    karatsubaHighValue true (karatsubaHighValue true
      (karatsubaHighValue false initial cv) av) dv=result := by
  rw [high_sub _ _ (high_bound _ _ _) hd,high_sub _ _ (high_bound _ _ _) ha,high_add]
  omega

private theorem uncombine_value (av dv cv initial result : Nat)
    (hc : cv<2^384) (hi : initial<2^512) (_hr : result<2^512)
    (he : initial+2^128*cv=result+2^128*av+2^128*dv) :
    karatsubaHighValue true (karatsubaHighValue false
      (karatsubaHighValue false result dv) av) cv=initial := by
  rw [high_sub _ _ (high_bound _ _ _) hc,high_add,high_add]
  omega


/-- Recombination is modulo the full result width, including intermediate wraps. -/
theorem karatsuba_combine_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv sv initial result : Nat)
    (ha : av<2^384) (hd : dv<2^384) (hi' : initial<2^512) (hr : result<2^512)
    (he : initial+2^128*cv=result+2^128*av+2^128*dv) :
    Triple (KaratsubaValues L lo hi av dv cv initial sv) L.combine
      (KaratsubaValues L lo hi av dv cv result sv) := by
  have c := karatsuba_high_c_spec false L h lo hi av dv cv initial sv
  have a := karatsuba_high_a_spec true L h lo hi av dv cv
    (karatsubaHighValue false initial cv) sv
  have d := karatsuba_high_d_spec true L h lo hi av dv cv
    (karatsubaHighValue true (karatsubaHighValue false initial cv) av) sv
  have hh := (c.seq a).seq d
  rw [combine_value av dv cv initial result ha hd hi' hr he] at hh
  exact hh

theorem karatsuba_uncombine_spec (L : KaratsubaSquareLayout) (h : L.Valid)
    (lo hi av dv cv sv initial result : Nat)
    (hc : cv<2^384) (hi' : initial<2^512) (hr : result<2^512)
    (he : initial+2^128*cv=result+2^128*av+2^128*dv) :
    Triple (KaratsubaValues L lo hi av dv cv result sv) L.uncombine
      (KaratsubaValues L lo hi av dv cv initial sv) := by
  have d := karatsuba_high_d_spec false L h lo hi av dv cv result sv
  have a := karatsuba_high_a_spec false L h lo hi av dv cv
    (karatsubaHighValue false result dv) sv
  have c := karatsuba_high_c_spec true L h lo hi av dv cv
    (karatsubaHighValue false (karatsubaHighValue false result dv) av) sv
  have hh := (d.seq a).seq c
  rw [uncombine_value av dv cv initial result hc hi' hr he] at hh
  exact hh

private theorem recombination_bounds (lo hi : Nat) (hl : lo<2^128) (hh : hi<2^128) :
    lo^2<2^384 ∧ hi^2<2^384 ∧ (lo+hi)^2<2^384 ∧
    lo^2+2^256*hi^2<2^512 ∧ (lo+2^128*hi)^2<2^512 ∧
    lo^2+2^256*hi^2+2^128*(lo+hi)^2=
      (lo+2^128*hi)^2+2^128*lo^2+2^128*hi^2 := by
  have al := square_bound lo 128 hl
  have ah := square_bound hi 128 hh
  have ac := square_sum128_square_bound lo hi hl hh
  have xb : lo+2^128*hi<2^256 := by omega
  have ax := square_bound _ 256 xb
  refine ⟨by omega,by omega,by omega,by omega,by simpa only [Nat.reduceMul] using ax,?_⟩
  ring

/-- The full compute preserves its input, retains A and D, and clears every temporary. -/
theorem karatsubaSquare_spec (L : KaratsubaSquareLayout) (h : L.Valid) (lo hi : Nat) :
    Triple (KaratsubaValues L lo hi 0 0 0 0 0) (karatsubaSquare L)
      (KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0) := by
  intro s m hs
  have hl : lo<2^128 := by simpa [h.low_length,hs.low] using regValue_lt L.low s.basis
  have hh : hi<2^128 := by simpa [h.high_length,hs.high] using regValue_lt L.high s.basis
  obtain ⟨ba,bd,bc,bi,br,be⟩ := recombination_bounds lo hi hl hh
  have a := karatsuba_squareLow_spec L h lo hi 0 0 0 0 0
  have d := karatsuba_squareHigh_spec L h lo hi (lo^2) 0 0 0 0
  have s1 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) 0 0
  have c1 := karatsuba_squareSum_spec L h lo hi (lo^2) (hi^2) 0 0 (lo+hi)
  have s2 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
  have cp := (karatsuba_copySquares_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0).1
  have comb := karatsuba_combine_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
    (lo^2+2^256*hi^2) ((lo+2^128*hi)^2) ba bd bi br be
  have s3 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) ((lo+2^128*hi)^2)
  have c2 := karatsuba_clearSquareSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) (lo+hi)
  have s4 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2)
  exact ((((((((a.seq d).seq s1).seq c1).seq s2).seq cp).seq comb).seq s3).seq c2).seq s4 s m hs

/-- Cleanup uses forward programs and restores all retained square words. -/
theorem karatsubaSquareClear_spec (L : KaratsubaSquareLayout) (h : L.Valid) (lo hi : Nat) :
    Triple (KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0)
      (karatsubaSquareClear L) (KaratsubaValues L lo hi 0 0 0 0 0) := by
  intro s m hs
  have hl : lo<2^128 := by simpa [h.low_length,hs.low] using regValue_lt L.low s.basis
  have hh : hi<2^128 := by simpa [h.high_length,hs.high] using regValue_lt L.high s.basis
  obtain ⟨ba,bd,bc,bi,br,be⟩ := recombination_bounds lo hi hl hh
  have s1 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2)
  have c1 := karatsuba_squareSum_spec L h lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) (lo+hi)
  have s2 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) ((lo+2^128*hi)^2)
  have comb := karatsuba_uncombine_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
    (lo^2+2^256*hi^2) ((lo+2^128*hi)^2) bc bi br be
  have cp := (karatsuba_copySquares_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0).2
  have s3 := karatsuba_prepareSum_spec L h lo hi (lo^2) (hi^2) ((lo+hi)^2) 0
  have c2 := karatsuba_clearSquareSum_spec L h lo hi (lo^2) (hi^2) 0 0 (lo+hi)
  have s4 := karatsuba_clearSum_spec L h lo hi (lo^2) (hi^2) 0 0
  have d := karatsuba_clearHigh_spec L h lo hi (lo^2) 0 0 0 0
  have a := karatsuba_clearLow_spec L h lo hi 0 0 0 0 0
  exact ((((((((s1.seq c1).seq s2).seq comb).seq cp).seq s3).seq c2).seq s4).seq d).seq a s m hs


private theorem values_frame (L : KaratsubaSquareLayout)
    (lo hi av dv zv av' dv' zv' : Nat) (s u : BasisState)
    (hs : KaratsubaValues L lo hi av dv 0 zv 0 s)
    (hu : KaratsubaValues L lo hi av' dv' 0 zv' 0 u)
    (ho : ∀ w,w∉L.wires→u w=s w) :
    ∀ w,w∉L.a++L.d++L.z→u w=s w := by
  intro w hw
  have eqv (r : List Wire) (he : regValue r u=regValue r s) (hm : w∈r) : u w=s w :=
    (regValue_eq_iff r u s).mp he w hm
  by_cases hl : w∈L.low
  · exact eqv L.low (hu.low.trans hs.low.symm) hl
  by_cases hh : w∈L.high
  · exact eqv L.high (hu.high.trans hs.high.symm) hh
  by_cases hc : w∈L.c
  · exact eqv L.c (hu.c.trans hs.c.symm) hc
  by_cases hz : w∈L.sum
  · exact eqv L.sum (hu.sum.trans hs.sum.symm) hz
  by_cases hp : w∈L.pad
  · exact eqv L.pad (hu.pad.trans hs.pad.symm) hp
  by_cases hm : w∈L.mask
  · exact eqv L.mask (hu.mask.trans hs.mask.symm) hm
  by_cases hk : w∈L.carry
  · exact eqv L.carry (hu.carry.trans hs.carry.symm) hk
  by_cases hi : w=L.cin
  · subst w; exact hu.cin.trans hs.cin.symm
  apply ho
  simpa only [KaratsubaSquareLayout.wires,List.mem_cons,List.mem_append,hl,hh,hc,hz,hp,hm,hk,hi,
    false_or,or_false] using hw

/-- Every wire outside the three retained output words is exactly preserved. -/
theorem karatsubaSquare_frame (L : KaratsubaSquareLayout) (h : L.Valid) (lo hi : Nat)
    (s : State) (m : List Bool) (hs : KaratsubaValues L lo hi 0 0 0 0 0 s.basis) :
    ∀ w,w∉L.a++L.d++L.z→(run (karatsubaSquare L) m s).basis w=s.basis w := by
  have hr := karatsubaSquare_spec L h lo hi s m hs
  apply values_frame L lo hi 0 0 0 (lo^2) (hi^2) ((lo+2^128*hi)^2) _ _ hs hr.2
  intro w hw
  apply run_preserves_outside
  intro hm
  exact hw (List.mem_toFinset.mp ((karatsubaSquare_wires_subset L h).1 hm))

theorem karatsubaSquareClear_frame (L : KaratsubaSquareLayout) (h : L.Valid) (lo hi : Nat)
    (s : State) (m : List Bool)
    (hs : KaratsubaValues L lo hi (lo^2) (hi^2) 0 ((lo+2^128*hi)^2) 0 s.basis) :
    ∀ w,w∉L.a++L.d++L.z→(run (karatsubaSquareClear L) m s).basis w=s.basis w := by
  have hr := karatsubaSquareClear_spec L h lo hi s m hs
  apply values_frame L lo hi (lo^2) (hi^2) ((lo+2^128*hi)^2) 0 0 0 _ _ hs hr.2
  intro w hw
  apply run_preserves_outside
  intro hm
  exact hw (List.mem_toFinset.mp ((karatsubaSquare_wires_subset L h).2 hm))

end ECDSAAdd.Arithmetic
