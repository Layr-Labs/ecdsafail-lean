import ECDSAAdd.Arithmetic.MontLookup

namespace ECDSAAdd.Arithmetic

private theorem montConstantUpdate_correct (subtract : Bool) (L : MontStageLayout) (K : Nat)
    (hnd : (L.cin::(L.table++L.acc++L.carry)).Nodup)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hK : K<2^L.table.length) (s : State) (m : List Bool)
    (hz : regValue L.table s.basis=0) (hca : regValue L.carry s.basis=0)
    (hci : s.basis L.cin=false) :
    let circuit := xorConstant L.table K ++
      (if subtract then subInPlace L.table L.acc L.carry L.cin else addInPlace L.table L.acc L.carry L.cin) ++
      xorConstant L.table K
    (run circuit m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run circuit m s).basis w=s.basis w) ∧
    regValue L.acc (run circuit m s).basis=(if subtract then
      (regValue L.acc s.basis+2^L.acc.length-K)%2^L.acc.length
      else (regValue L.acc s.basis+K)%2^L.acc.length) := by
  have hn := List.nodup_iff_count.mp hnd
  have hT : L.table.Nodup := by
    apply List.nodup_iff_count.mpr; intro w; have h := hn w
    simp only [List.count_cons,List.count_append] at h; omega
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
  let p := xorConstant L.table K
  let s1 := run p m s
  let m1 := m.drop (measurementCount p)
  let arith := if subtract then subInPlace L.table L.acc L.carry L.cin else addInPlace L.table L.acc L.carry L.cin
  let s2 := run arith m1 s1
  let m2 := m1.drop (measurementCount arith)
  have h1 := xorConstant_correct L.table hT K hK s m
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
      have hh := addInPlace_correct L.table L.acc L.carry L.cin hnd ht hc s1 m1
        ((regValue_zero _ _).mp ca1)
      simpa [s2,arith,ci1,Nat.add_comm] using hh
    | true =>
      have hh := subInPlace_spec L.table L.acc L.carry L.cin hnd ht hc
        (regValue L.table s1.basis) (regValue L.acc s1.basis) s1 m1 ⟨⟨⟨rfl,rfl⟩,ci1⟩,ca1⟩
      exact ⟨hh.1,subInPlace_frame L.table L.acc L.carry L.cin hnd ht hc s1 m1 ci1 ca1,hh.2.1.1.2⟩
  have h3 := xorConstant_correct L.table hT K hK s2 m2
  have table1 : regValue L.table s1.basis=K := by simpa only [hz,Nat.zero_xor] using h1.2.2
  have table2 : regValue L.table s2.basis=K :=
    (regValue_congr _ _ _ (fun w hw => h2.2.1 w (List.disjoint_left.mp accT.symm hw))).trans table1
  have table3 : regValue L.table (run p m2 s2).basis=0 := by rw [h3.2.2,table2,Nat.xor_self]
  dsimp only
  rw [List.append_assoc,run_append,run_take,run_append,run_take]
  change (run p m2 s2).phase=s.phase ∧ _
  refine ⟨h3.1.trans (h2.1.trans h1.1),?_,?_⟩
  · intro w hw
    by_cases hwT : w∈L.table
    · exact (regValue_eq_iff L.table _ _).mp (table3.trans hz.symm) w hwT
    · exact (h3.2.1 w hwT).trans ((h2.2.1 w hw).trans (h1.2.1 w hwT))
  · rw [regValue_congr L.acc _ s2.basis (fun w hw => h3.2.1 w (List.disjoint_left.mp accT hw)),
      h2.2.2,table1,keep1 L.acc accT]

theorem montConstantAdd_correct (L : MontStageLayout) (K : Nat)
    (hnd : (L.cin::(L.table++L.acc++L.carry)).Nodup)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hK : K<2^L.table.length) (s : State) (m : List Bool)
    (hz : regValue L.table s.basis=0) (hca : regValue L.carry s.basis=0)
    (hci : s.basis L.cin=false) :
    (run (montConstantAdd L K) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montConstantAdd L K) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montConstantAdd L K) m s).basis=(regValue L.acc s.basis+K)%2^L.acc.length := by
  simpa only [montConstantAdd,Bool.false_eq_true,if_false] using
    montConstantUpdate_correct false L K hnd ht hc hK s m hz hca hci

theorem montConstantSub_correct (L : MontStageLayout) (K : Nat)
    (hnd : (L.cin::(L.table++L.acc++L.carry)).Nodup)
    (ht : L.table.length=L.acc.length) (hc : L.carry.length+1=L.acc.length)
    (hK : K<2^L.table.length) (s : State) (m : List Bool)
    (hz : regValue L.table s.basis=0) (hca : regValue L.carry s.basis=0)
    (hci : s.basis L.cin=false) :
    (run (montConstantSub L K) m s).phase=s.phase ∧
    (∀ w, w∉L.acc → (run (montConstantSub L K) m s).basis w=s.basis w) ∧
    regValue L.acc (run (montConstantSub L K) m s).basis=(regValue L.acc s.basis+2^L.acc.length-K)%2^L.acc.length := by
  simpa only [montConstantSub,if_true] using
    montConstantUpdate_correct true L K hnd ht hc hK s m hz hca hci

end ECDSAAdd.Arithmetic
