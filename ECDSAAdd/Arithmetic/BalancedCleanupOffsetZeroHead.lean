import ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlimChainProof
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroHead
open BalancedCleanupOffset
attribute [local irreducible] run BalancedCleanupOffsetSlim.chain majority eraseCarry

/-- Offset bit0 and its incoming carry are both zero. The comparison carry
is still computed and measured cleanly; the offset carry is never emitted. -/
def program (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire) : Program :=
  ([.X y]++majority a y cinB d)++
    (BalancedCleanupOffsetSlim.chain bits xs ys cs ds cinC d target++
      (eraseCarry a y cinB d++[.X y]))

private theorem zero_records (P : Program) (h : measurementCount P=0)
    (s : State) (m n : List Bool) : run P m s=run P n s := by
  have x := run_take P m s
  have z := run_take P n s
  rw [h,List.take_zero] at x z
  exact x.symm.trans z
private theorem run_zero (P Q : Program) (h : measurementCount P=0) (s : State) (m : List Bool) :
    run (P++Q) m s=run Q m (run P m s) := by
  rw [run_append,h,List.take_zero,List.drop_zero,zero_records P h s [] m]

/-- Exact full-state semantics, including arbitrary incoming phase and all
independent measurement records. Both tail banks and d are restored. -/
theorem run_correct (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire)
    (hn : ([a,y,cinC,cinB,d,target]++(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉[a,y,cinC,cinB,d,target]++(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (m : List Bool) (hz : s.basis cinC=false) (hzD : s.basis d=false)
    (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false) :
    run (program bits xs ys cs ds a y cinC cinB d target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^
        decision (false::bits.map (fun b => b.value s.basis))
          (s.basis a::xs.map s.basis) (s.basis y::ys.map s.basis) false (s.basis cinB))⟩ := by
  have full := List.nodup_append'.mp hn
  have nd := full.1
  have nr := List.nodup_reverse.mpr nd
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd nr
  have majND : [a,y,cinB,d].Nodup := by simp [List.nodup_cons,nd,nr]
  let A := s.basis a
  let Y := s.basis y
  let E := s.basis cinB
  let D := carryBit A (!Y) E
  let u : State := ⟨s.phase,writeBit (writeBit s.basis y (!Y)) d D⟩
  have pm : measurementCount ([.X y]++majority a y cinB d)=0 := by
    simp [measurementCount_append,majority,measurementCount]
  have pre : run ([.X y]++majority a y cinB d) m s=u := by
    rw [run_zero _ _ (show measurementCount [.X y]=0 from rfl),x_run,
      majority_correct a y cinB d majND]
    simp only [writeBit,Function.update_of_ne (show d≠y by simp [nd,nr]),
      Function.update_of_ne (show a≠y by simp [nd,nr]),
      Function.update_of_ne (show cinB≠y by simp [nd,nr]),Function.update_self,
      hzD,Bool.false_xor]
    rfl
  have uf (q : Wire) (qy : q≠y) (qd : q≠d) : u.basis q=s.basis q := by
    simp only [u,writeBit,Function.update_of_ne qy,Function.update_of_ne qd]
  have tailNe (q : Wire) (hq : q∈xs++ys++cs++ds) (h : Wire)
      (hh : h∈[a,y,cinC,cinB,d,target]) : q≠h := by
    intro eq
    exact List.disjoint_left.mp full.2.2 hh (eq ▸ hq)
  have same (q : Wire) (hq : q∈xs++ys++cs++ds) : u.basis q=s.basis q :=
    uf q (tailNe q hq y (by simp)) (tailNe q hq d (by simp))
  have mapA : xs.map u.basis=xs.map s.basis := by
    apply List.map_congr_left
    intro q hq
    exact same q (by simp [hq])
  have mapY : ys.map u.basis=ys.map s.basis := by
    apply List.map_congr_left
    intro q hq
    exact same q (by simp [hq])
  have src (q : Wire) (hq : q∈[a,y,cinC,cinB,d,target])
      (w : Wire) (hw : w∈mappedWires bits) : w≠q := by
    intro eq
    exact ha w hw (List.mem_append_left _ (eq.symm ▸ hq))
  have mapBits : bits.map (fun b => b.value u.basis)=bits.map (fun b => b.value s.basis) := by
    apply List.map_congr_left
    intro bit hbit
    apply mappedBit_value_congr
    intro w hw
    have member : w∈mappedWires bits := by
      apply List.mem_flatMap.mpr
      refine ⟨bit,hbit,?_⟩
      cases he : bit.wire with
      | none => simp [he] at hw
      | some wire =>
        have eq : wire=w := by simpa [he] using hw
        subst w
        simp [he]
    exact uf w (src y (by simp) w member) (src d (by simp) w member)
  have tailND : (target::cinC::d::(xs++ys++cs++ds)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have tailFresh : ∀w∈mappedWires bits,w∉target::cinC::d::(xs++ys++cs++ds) := by
    intro w hw hm
    apply ha w hw
    simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hm ⊢
    tauto
  have uc : u.basis cinC=false := (uf cinC (by simp [nd,nr]) (by simp [nd,nr])).trans hz
  have ud : u.basis d=D := by simp only [u,writeBit,Function.update_self]
  have cleanC : ∀q∈cs,u.basis q=false := fun q hq => (same q (by simp [hq])).trans (hcc q hq)
  have cleanD : ∀q∈ds,u.basis q=false := fun q hq => (same q (by simp [hq])).trans (hdd q hq)
  have tail := BalancedCleanupOffsetSlim.chain_run bits xs ys cs ds cinC d target tailND
    tailFresh hb hx hc hd u m cleanC cleanD
  rw [mapBits,mapA,mapY,uc,ud] at tail
  let V := decision (bits.map (fun b => b.value s.basis)) (xs.map s.basis) (ys.map s.basis) false D
  let v : State := ⟨u.phase,writeBit u.basis target (u.basis target ^^ V)⟩
  change run (BalancedCleanupOffsetSlim.chain bits xs ys cs ds cinC d target) m u=v at tail
  have vf (q : Wire) (hq : q≠target) : v.basis q=u.basis q := by
    simp only [v,writeBit,Function.update_of_ne hq]
  have va : v.basis a=A := (vf a (by simp [nd,nr])).trans (uf a (by simp [nd,nr]) (by simp [nd,nr]))
  have ve : v.basis cinB=E := (vf cinB (by simp [nd,nr])).trans
    (uf cinB (by simp [nd,nr]) (by simp [nd,nr]))
  have vy : v.basis y= !Y := by
    rw [vf y (by simp [nd,nr])]
    simp only [u,writeBit,Function.update_of_ne (show y≠d by simp [nd,nr]),Function.update_self]
  have vd : v.basis d=D := (vf d (by simp [nd,nr])).trans ud
  have post (n : List Bool) : run (eraseCarry a y cinB d++[.X y]) n v=
      ⟨v.phase,writeBit (writeBit v.basis d false) y Y⟩ := by
    have carry : v.basis d=carryBit (v.basis a) (v.basis y) (v.basis cinB) := by
      rw [vd,va,vy,ve]
    rw [run_append,run_take,eraseCarry_correct a y cinB d
      (by simp [nd,nr]) (by simp [nd,nr]) (by simp [nd,nr]) v carry,x_run]
    simp only [writeBit,Function.update_of_ne (show y≠d by simp [nd,nr]),vy,Bool.not_not]
  rw [program,run_zero _ _ pm,pre,run_append,run_take,tail,post]
  apply State.extensionality
  · rfl
  · funext q
    have boolean : carryBit false Y false=false ∧ sumBit false Y false=Y := by
      cases Y <;> decide
    by_cases qt : q=target
    · subst q
      simp only [u,v,V,D,A,Y,E,decision,boolean.1,boolean.2,writeBit,
        Function.update_of_ne (show target≠y by simp [nd,nr]),
        Function.update_of_ne (show target≠d by simp [nd,nr]),Function.update_self]
    · by_cases qy : q=y
      · subst q
        simp only [u,v,Y,writeBit,Function.update_self,
          Function.update_of_ne (show y≠target by simp [nd,nr])]
      · by_cases qd : q=d
        · subst q
          simp only [u,v,writeBit,Function.update_of_ne qy,Function.update_self,
            Function.update_of_ne (show d≠target by simp [nd,nr]),hzD]
        · simp only [u,v,writeBit,Function.update_of_ne qt,
            Function.update_of_ne qy,Function.update_of_ne qd]

/-- Exact emitted prefix cost. For a255-bit tail this is510 T/M. -/
theorem counts (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y cinC cinB d target : Wire) (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length) :
    toffoliCount (program bits xs ys cs ds a y cinC cinB d target)=
      1+(2*ys.length-(if ys.length=0 then 0 else 1)) ∧
    measurementCount (program bits xs ys cs ds a y cinC cinB d target)=
      1+(2*ys.length-(if ys.length=0 then 0 else 1)) := by
  have tail := BalancedCleanupOffsetSlim.chain_counts bits xs ys cs ds cinC d target hb hx hc hd
  simp only [program,toffoliCount_append,measurementCount_append,tail.1,tail.2]
  constructor <;> simp [majority,eraseCarry,toffoliCount,measurementCount,Nat.add_comm]


/-- Independent old/new record lists give the same complete State. The old
unused offset-carry site c0 is supplied clean by the existing bank contract. -/
theorem chain_equiv (bits : List MappedBit) (xs ys cs ds : List Wire)
    (a y c0 d cinC cinB target : Wire)
    (hn : (target::cinC::cinB::((a::xs)++(y::ys)++(c0::cs)++(d::ds))).Nodup)
    (ha : ∀w∈mappedWires bits,w∉target::cinC::cinB::((a::xs)++(y::ys)++(c0::cs)++(d::ds)))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (mOld mNew : List Bool) (hz : s.basis cinC=false)
    (hcc : ∀q∈c0::cs,s.basis q=false) (hdd : ∀q∈d::ds,s.basis q=false) :
    run (BalancedCleanupOffsetSlim.chain (⟨none,false⟩::bits) (a::xs) (y::ys)
      (c0::cs) (d::ds) cinC cinB target) mOld s =
    run (program bits xs ys cs ds a y cinC cinB d target) mNew s := by
  have nd : ([a,y,cinC,cinB,d,target]++(xs++ys++cs++ds)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp hn q
    simp only [List.count_append,List.count_cons,List.count_nil] at h ⊢
    omega
  have fresh : ∀w∈mappedWires bits,w∉[a,y,cinC,cinB,d,target]++(xs++ys++cs++ds) := by
    intro w hw hm
    apply ha w hw
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm ⊢
    tauto
  have old := BalancedCleanupOffsetSlim.chain_run (⟨none,false⟩::bits) (a::xs) (y::ys)
    (c0::cs) (d::ds) cinC cinB target hn (by
      intro w hw
      apply ha w
      simpa [mappedWires] using hw)
    (by simpa using hb) (by simpa using hx) (by simpa using hc) (by simpa using hd) s mOld hcc hdd
  have freshRun := run_correct bits xs ys cs ds a y cinC cinB d target nd fresh hb hx hc hd
    s mNew hz (hdd d (by simp)) (fun q hq => hcc q (by simp [hq])) (fun q hq => hdd q (by simp [hq]))
  rw [old,freshRun]
  simp [MappedBit.value,hz]
end ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroHead
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroHead.run_correct
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroHead.counts
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffsetZeroHead.chain_equiv
