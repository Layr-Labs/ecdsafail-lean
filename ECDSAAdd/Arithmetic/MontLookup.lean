import ECDSAAdd.Arithmetic.MontPrepare

namespace ECDSAAdd.Arithmetic

/-- 减法也逐线保持目标以外所有位；清零进位仍由同一前向门列证明。 -/
theorem subInPlace_frame (x y carry : List Wire) (cin : Wire)
    (hnd : (cin::(x++y++carry)).Nodup) (hx : x.length=y.length)
    (hc : carry.length+1=y.length) (s : State) (m : List Bool)
    (hcin : s.basis cin=false) (hcarry : regValue carry s.basis=0)
    (w : Wire) (hw : w∉y) : (run (subInPlace x y carry cin) m s).basis w=s.basis w := by
  have h := (subInPlace_spec x y carry cin hnd hx hc
    (regValue x s.basis) (regValue y s.basis) s m ⟨⟨⟨rfl,rfl⟩,hcin⟩,hcarry⟩).2
  by_cases hxw : w∈x
  · exact (regValue_eq_iff x _ _).mp h.1.1.1 w hxw
  by_cases hcw : w∈carry
  · exact (regValue_eq_iff carry _ _).mp (h.2.trans hcarry.symm) w hcw
  by_cases he : w=cin
  · subst w; exact h.1.2.trans hcin.symm
  apply run_preserves_outside
  rw [subInPlace_wires x y carry cin hx hc]
  simpa using (show w∉cin::(x++y++carry) by simp [he,hxw,hw,hcw])

/-- 查表加法以 addr 为只读输入，仅改变 acc；table/scratch/carry 全部回零。 -/
private theorem montLookupUpdate_correct (subtract : Bool) (L : MontStageLayout) (addr : List Wire) (K : Nat)
    (hnd : (L.cin::(addr++L.table++L.acc++L.carry++L.scratch)).Nodup)
    (ha : addr.length=4) (hs : L.scratch.length=3)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hK : ∀ d<16, d*K<2^L.table.length)
    (s : State) (m : List Bool)
    (hz : regValue L.table s.basis=0) (hsc : regValue L.scratch s.basis=0)
    (hca : regValue L.carry s.basis=0) (hci : s.basis L.cin=false) :
    (run (montLookup L addr K ++ (if subtract then subInPlace L.table L.acc L.carry L.cin else addInPlace L.table L.acc L.carry L.cin) ++ montLookup L addr K) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montLookup L addr K ++ (if subtract then subInPlace L.table L.acc L.carry L.cin else addInPlace L.table L.acc L.carry L.cin) ++ montLookup L addr K) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montLookup L addr K ++ (if subtract then subInPlace L.table L.acc L.carry L.cin else addInPlace L.table L.acc L.carry L.cin) ++ montLookup L addr K) m s).basis=
      (if subtract then (regValue L.acc s.basis + 2^L.acc.length - regValue addr s.basis*K)%2^L.acc.length
       else (regValue L.acc s.basis + regValue addr s.basis*K)%2^L.acc.length) := by
  cases addr with
  | nil => simp at ha
  | cons a bs =>
    have hb : bs.length=3 := by simpa using ha
    have hn := List.nodup_iff_count.mp hnd
    have hnlookup : (a::(bs++L.scratch++L.table)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have h := hn w
      simp only [List.count_cons,List.count_append] at h ⊢; omega
    have hnadd : (L.cin::(L.table++L.acc++L.carry)).Nodup := by
      apply List.nodup_iff_count.mpr; intro w; have h := hn w
      simp only [List.count_cons,List.count_append] at h ⊢; omega
    have accT : L.acc.Disjoint L.table := by
      apply List.disjoint_left.mpr; intro w hw ht'
      have h := hn w; have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr ht'
      simp only [List.count_cons,List.count_append] at h; omega
    have carryT : L.carry.Disjoint L.table := by
      apply List.disjoint_left.mpr; intro w hw ht'
      have h := hn w; have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr ht'
      simp only [List.count_cons,List.count_append] at h; omega
    have cinT : L.cin∉L.table := by
      intro ht'; have h := hn L.cin; have h1 := List.count_pos_iff.mpr ht'
      simp only [List.count_cons,List.count_append,beq_self_eq_true,if_true] at h; omega
    let p := lookup a bs L.scratch L.table (fun d => d*K)
    let s1 := run p m s
    let m1 := m.drop (measurementCount p)
    let arith := if subtract then subInPlace L.table L.acc L.carry L.cin else addInPlace L.table L.acc L.carry L.cin
    let s2 := run arith m1 s1
    let m2 := m1.drop (measurementCount arith)
    have h1 := lookup_correct a bs L.scratch L.table (fun d => d*K)
      hnlookup hb hs hK s m ((regValue_zero _ _).mp hsc)
    have keep1 (r : List Wire) (hr : r.Disjoint L.table) : regValue r s1.basis=regValue r s.basis :=
      regValue_congr _ _ _ (fun w hw => h1.2.1 w (List.disjoint_left.mp hr hw))
    have ca1 : regValue L.carry s1.basis=0 := (keep1 L.carry carryT).trans hca
    have ci1 : s1.basis L.cin=false := (h1.2.1 L.cin cinT).trans hci
    have h2 : s2.phase=s1.phase ∧ (∀ w, w∉L.acc → s2.basis w=s1.basis w) ∧
        regValue L.acc s2.basis=(if subtract then
          (regValue L.acc s1.basis+2^L.acc.length-regValue L.table s1.basis)%2^L.acc.length
          else (regValue L.acc s1.basis+regValue L.table s1.basis)%2^L.acc.length) := by
      cases subtract with
      | false =>
        have hh := addInPlace_correct L.table L.acc L.carry L.cin hnadd ht hc s1 m1
          ((regValue_zero _ _).mp ca1)
        simpa [s2,arith,ci1,Nat.add_comm] using hh
      | true =>
        have hh := subInPlace_spec L.table L.acc L.carry L.cin hnadd ht hc
          (regValue L.table s1.basis) (regValue L.acc s1.basis) s1 m1 ⟨⟨⟨rfl,rfl⟩,ci1⟩,ca1⟩
        exact ⟨hh.1,subInPlace_frame L.table L.acc L.carry L.cin hnadd ht hc s1 m1 ci1 ca1,
          hh.2.1.1.2⟩
    have tableA : L.table.Disjoint L.acc := accT.symm
    have addrA : (a::bs).Disjoint L.acc := by
      apply List.disjoint_left.mpr; intro w hw ht'
      have h := hn w; have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr ht'
      simp only [List.count_cons,List.count_append] at h h1; omega
    have scA : L.scratch.Disjoint L.acc := by
      apply List.disjoint_left.mpr; intro w hw ht'
      have h := hn w; have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr ht'
      simp only [List.count_cons,List.count_append] at h; omega
    have scT : L.scratch.Disjoint L.table := by
      apply List.disjoint_left.mpr; intro w hw ht'
      have h := hn w; have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr ht'
      simp only [List.count_cons,List.count_append] at h; omega
    have addrT : (a::bs).Disjoint L.table := by
      apply List.disjoint_left.mpr; intro w hw ht'
      have h := hn w; have h1 := List.count_pos_iff.mpr hw; have h2 := List.count_pos_iff.mpr ht'
      simp only [List.count_cons,List.count_append] at h h1; omega
    have keep2 (r : List Wire) (hr : r.Disjoint L.acc) : regValue r s2.basis=regValue r s1.basis :=
      regValue_congr _ _ _ (fun w hw => h2.2.1 w (List.disjoint_left.mp hr hw))
    have sc2 : regValue L.scratch s2.basis=0 :=
      (keep2 L.scratch scA).trans ((keep1 L.scratch scT).trans hsc)
    have h3 := lookup_correct a bs L.scratch L.table (fun d => d*K)
      hnlookup hb hs hK s2 m2 ((regValue_zero _ _).mp sc2)
    have addr2 : regValue (a::bs) s2.basis=regValue (a::bs) s.basis :=
      (keep2 _ addrA).trans (keep1 _ addrT)
    have table1 : regValue L.table s1.basis=regValue (a::bs) s.basis*K := by
      simpa only [hz,Nat.zero_xor] using h1.2.2
    have table3 : regValue L.table (run p m2 s2).basis=0 := by
      rw [h3.2.2,keep2 L.table tableA,table1,addr2,Nat.xor_self]
    have hp : montLookup L (a::bs) K ++ (if subtract then subInPlace L.table L.acc L.carry L.cin
        else addInPlace L.table L.acc L.carry L.cin) ++ montLookup L (a::bs) K=p++(arith++p) := by
      simp [montLookup,p,arith,List.append_assoc]
    simp only [hp,run_append,run_take]
    change (run p m2 s2).phase=s.phase ∧ _
    refine ⟨h3.1.trans (h2.1.trans h1.1),?_,?_⟩
    · intro w hw
      by_cases hwT : w∈L.table
      · exact (regValue_eq_iff L.table _ _).mp (table3.trans hz.symm) w hwT
      · exact (h3.2.1 w hwT).trans ((h2.2.1 w hw).trans (h1.2.1 w hwT))
    · rw [regValue_congr L.acc _ s2.basis (fun w hw => h3.2.1 w (List.disjoint_left.mp accT hw)),
        h2.2.2,table1,keep1 L.acc accT]

/-- 查表Add更新仅改变 acc，并清空查表和算术工作区。 -/
theorem montLookupAdd_correct (L : MontStageLayout) (addr : List Wire) (K : Nat)
    (hnd : (L.cin::(addr++L.table++L.acc++L.carry++L.scratch)).Nodup)
    (ha : addr.length=4) (hs : L.scratch.length=3)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hK : ∀ d<16, d*K<2^L.table.length)
    (s : State) (m : List Bool)
    (hz : regValue L.table s.basis=0) (hsc : regValue L.scratch s.basis=0)
    (hca : regValue L.carry s.basis=0) (hci : s.basis L.cin=false) :
    (run (montLookupAdd L addr K) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montLookupAdd L addr K) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montLookupAdd L addr K) m s).basis=(regValue L.acc s.basis + regValue addr s.basis*K)%2^L.acc.length := by
  simpa only [montLookupAdd,Bool.false_eq_true,if_false] using
    montLookupUpdate_correct false L addr K hnd ha hs ht hc hK s m hz hsc hca hci

/-- 查表Sub更新仅改变 acc，并清空查表和算术工作区。 -/
theorem montLookupSub_correct (L : MontStageLayout) (addr : List Wire) (K : Nat)
    (hnd : (L.cin::(addr++L.table++L.acc++L.carry++L.scratch)).Nodup)
    (ha : addr.length=4) (hs : L.scratch.length=3)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hK : ∀ d<16, d*K<2^L.table.length)
    (s : State) (m : List Bool)
    (hz : regValue L.table s.basis=0) (hsc : regValue L.scratch s.basis=0)
    (hca : regValue L.carry s.basis=0) (hci : s.basis L.cin=false) :
    (run (montLookupSub L addr K) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montLookupSub L addr K) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montLookupSub L addr K) m s).basis=(regValue L.acc s.basis + 2^L.acc.length - regValue addr s.basis*K)%2^L.acc.length := by
  simpa only [montLookupSub,if_true] using
    montLookupUpdate_correct true L addr K hnd ha hs ht hc hK s m hz hsc hca hci

end ECDSAAdd.Arithmetic
