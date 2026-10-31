import ECDSAAdd.Submission.Entrant.Prelude

/-! Ported from the 0b701a2 record line (TickGapBudget, ticks 255-286 narrowTop): the top carry
of the integer adder on ticks 255-286 is dropped under the strict fixed-modulus sum cap. -/

section
-- ===== TickGapBudget =====
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ECDSAAdd.Entrant.TickGap

theorem scaled_budget (p x i : Nat) (hx : x  ≤  p) :
    ∃ j k : Nat, j+k=i  ∧ 
      (SkywalkNat.step^[i] (SkywalkNat.init x p)).u * 2^j  ≤  p  ∧ 
      (SkywalkNat.step^[i] (SkywalkNat.init x p)).v * 2^k  ≤  p := by
  induction i with
  | zero => exact ⟨0,0,rfl,by simpa [SkywalkNat.init] using hx,by simp [SkywalkNat.init]⟩
  | succ i ih =>
    obtain ⟨j,k,hjk,hu,hv⟩ := ih
    rw [Function.iterate_succ_apply']
    generalize SkywalkNat.step^[i] (SkywalkNat.init x p)=z at hu hv ⊢
    by_cases hz : z.u=0
    · refine ⟨j+1,k,by omega,?_,?_⟩
      · simp [SkywalkNat.step,hz]
      · simpa [SkywalkNat.step,hz] using hv
    · by_cases he : z.u%2=0
      · refine ⟨j+1,k,by omega,?_,?_⟩
        · simp only [SkywalkNat.step,if_neg hz,if_pos he,pow_succ]
          have hhalf : z.u/2*2 ≤ z.u := by omega
          nlinarith [Nat.mul_le_mul_right (2^j) hhalf]
        · simpa [SkywalkNat.step,hz,he] using hv
      · by_cases hle : z.v ≤ z.u
        · refine ⟨j+1,k,by omega,?_,?_⟩
          · simp only [SkywalkNat.step,if_neg hz,if_neg he,if_pos hle,pow_succ]
            have hhalf : (z.u-z.v)/2*2 ≤ z.u := by omega
            nlinarith [Nat.mul_le_mul_right (2^j) hhalf]
          · simpa [SkywalkNat.step,hz,he,hle] using hv
        · refine ⟨k+1,j,by omega,?_,?_⟩
          · simp only [SkywalkNat.step,if_neg hz,if_neg he,if_neg hle,pow_succ]
            have hhalf : (z.v-z.u)/2*2 ≤ z.v := by omega
            nlinarith [Nat.mul_le_mul_right (2^k) hhalf]
          · simpa [SkywalkNat.step,hz,he,hle] using hu

private theorem two_pow_sum (a b : Nat) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2^a+2^b ≤ 2^(a+b-1) := by
  obtain ⟨c,rfl⟩ : ∃ c, a=c+2 := ⟨a-2,by omega⟩
  obtain ⟨d,rfl⟩ : ∃ d, b=d+2 := ⟨b-2,by omega⟩
  have he : c+2+(d+2)-1=c+d+3 := by omega
  rw [he, pow_add, pow_add, pow_add]
  norm_num
  rw [pow_add]
  have hc : 1 ≤ 2^c := Nat.one_le_two_pow
  have hd : 1 ≤ 2^d := Nat.one_le_two_pow
  nlinarith [Nat.mul_le_mul hc hd]

private theorem scaled_lt (u p j : Nat) (hp : p < 2^256) (hu : u*2^j ≤ p) (hj : j ≤ 256) :
    u < 2^(256-j) := by
  have he : 2^(256-j)*2^j=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
  by_contra h
  have hle := Nat.mul_le_mul_right (2^j) (Nat.le_of_not_gt h)
  omega

/-- A strict fixed-modulus sum cap across the late 32-stage band. -/
theorem strict_sum_band (x p i : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p)
    (cop : x.Coprime p) (hi : 256 ≤ i  ∧  i ≤ 287) :
    let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
    z.u+z.v < 2^(511-i) := by
  dsimp only
  obtain ⟨j,k,hjk,hu,hv⟩ := scaled_budget p x i (Nat.le_of_lt hx)
  have valid := SkywalkNat.iter_valid i (SkywalkNat.init x p) hp0 hpo
  let z := SkywalkNat.step^[i] (SkywalkNat.init x p)
  change z.u*2^j ≤ p at hu
  change z.v*2^k ≤ p at hv
  change 0 < z.v  ∧  z.v%2=1  ∧  z.u.gcd z.v=x.gcd p at valid
  change z.u+z.v < _
  by_cases hz : z.u=0
  · have hv1 : z.v=1 := by
      have hg := valid.2.2.trans cop
      rw [hz,Nat.gcd_zero_left] at hg
      exact hg
    have hi' : 1 ≤ 511-i := by omega
    have pow := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) hi'
    simp only [pow_one] at pow
    omega
  have hu0 : 1 ≤ z.u := by omega
  have hv0 : 1 ≤ z.v := by omega
  have hj : j ≤ 255 := by
    by_contra h
    have hpw := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) (show 256 ≤ j by omega)
    nlinarith
  have hk : k ≤ 255 := by
    by_contra h
    have hpw := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) (show 256 ≤ k by omega)
    nlinarith
  have ju := scaled_lt z.u p j hp hu (by omega)
  have kv := scaled_lt z.v p k hp hv (by omega)
  by_cases hje : j=255
  · have ue : z.u=1 := by simp only [hje] at ju; norm_num at ju; omega
    have kk : k=i-255 := by omega
    have kp : k ≤ 32 := by omega
    have kp32 := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) kp
    have ep : 2^(256-k)*2^k=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
    have ek : 511-i=256-k := by omega
    rw [ue,ek]
    by_contra h
    have hbig : 2^(256-k) ≤ z.v+1 := by omega
    have mul := Nat.mul_le_mul_right (2^k) hbig
    nlinarith
  · by_cases hke : k=255
    · have ve : z.v=1 := by simp only [hke] at kv; norm_num at kv; omega
      have jj : j=i-255 := by omega
      have jp : j ≤ 32 := by omega
      have jp32 := Nat.pow_le_pow_right (by norm_num : 1 ≤ (2:Nat)) jp
      have ep : 2^(256-j)*2^j=(2:Nat)^256 := by rw [←pow_add]; congr 1; omega
      have ek : 511-i=256-j := by omega
      rw [ve,ek]
      by_contra h
      have hbig : 2^(256-j) ≤ z.u+1 := by omega
      have mul := Nat.mul_le_mul_right (2^j) hbig
      nlinarith
    · have a : 2 ≤ 256-j := by omega
      have b : 2 ≤ 256-k := by omega
      have bound := two_pow_sum (256-j) (256-k) a b
      have e : (256-j)+(256-k)-1=511-i := by omega
      rw [e] at bound
      omega
end ECDSAAdd.Entrant.TickGap

end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def signedAddTop (q : Wire) (x y carry : List Wire) : Program :=
  signComplement q x ++ TopCarry.addInPlaceTop x y carry q ++ signComplement q x

def Shape (n V : Nat) : Prop := V < 2^n ∨ 3*2^n ≤ V

theorem shape_complement (n V : Nat) (hv : V < 2^(n+2)) (h : Shape n V) :
    Shape n (2^(n+2)-1-V) := by
  have pow : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  unfold Shape at *
  omega

theorem shape_of_signed (n V : Nat) (hv : V < 2^(n+2))
    (lo : -((2^n:Nat):Int) ≤ signedDecode (n+2) V)
    (hi : signedDecode (n+2) V < ((2^n:Nat):Int)) : Shape n V := by
  have p2 : 2^(n+2) = 4*2^n := by rw [pow_add]; norm_num; ring
  have p1 : 2^(n+2-1) = 2*2^n := by rw [show n+2-1=n+1 by omega,pow_succ]; ring
  unfold signedDecode at lo hi
  split_ifs at lo hi <;> unfold Shape <;> omega

theorem signedAddTop_eq (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (s : State) (m : List Bool)
    (clean : ∀ w ∈ cs, s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Shape n (regValue y (run (signedAdd q x y cs) [] s).basis)) :
    run (signedAddTop q x y cs) m s=run (signedAdd q x y cs) m s := by
  have hxnd : x.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp (List.nodup_cons.mp hn).2).1).1
  have qx : q∉x := fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  have dis : List.Disjoint x (y++cs) := by
    have h : (x++(y++cs)).Nodup := by simpa only [List.append_assoc] using (List.nodup_cons.mp hn).2
    exact (List.nodup_append'.mp h).2.2
  have zx := (signComplement_counts q x).2
  let u := run (signComplement q x) [] s
  have fan := signComplement_correct q x hxnd qx s []
  have ux : Shape n (regValue x u.basis) := by
    change Shape n (regValue x (run (signComplement q x) [] s).basis)
    rw [fan.2.2]
    cases hs : s.basis q
    · exact source
    · simpa only [hx,if_true] using shape_complement n _ (by simpa [hx] using regValue_lt x s.basis) source
  have clean' : ∀ w ∈ cs, u.basis w=false := by
    intro w hw
    exact (fan.2.1 w (fun h => List.disjoint_left.mp dis h (List.mem_append_right _ hw))).trans (clean w hw)
  have out (r : List Bool) :
      regValue y (run (signComplement q x) r (run (addInPlace x y cs q) r u)).basis =
      regValue y (run (addInPlace x y cs q) r u).basis := by
    have h := signComplement_correct q x hxnd qx (run (addInPlace x y cs q) r u) r
    apply regValue_congr
    intro w hw
    exact h.2.1 w (fun hxw => List.disjoint_left.mp dis hxw (List.mem_append_left _ hw))
  have old : regValue y (run (signedAdd q x y cs) [] s).basis =
      regValue y (run (addInPlace x y cs q) [] u).basis := by
    simp only [signedAdd,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  have add := addInPlace_correct x y cs q hn (hx.trans hy.symm) hc u [] clean'
  have us : Shape n ((regValue x u.basis+regValue y u.basis+(u.basis q).toNat)%2^(n+2)) := by
    rw [old,add.2.2,hy] at sum
    exact sum
  have eq (r : List Bool) := TopCarry.addInPlaceTop_eq n x y cs q hy (hx.trans hy.symm)
    hc hn u r clean' ux us
  simp only [signedAddTop,signedAdd,List.append_assoc]
  rw [TopCarry.run_zero_head _ _ m s zx,TopCarry.run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq]
  have mc := TopCarry.addInPlaceTop_counts n x y cs q hy (hx.trans hy.symm) hc
  have mo := addInPlace_counts x y cs q (hx.trans hy.symm) hc
  rw [mc.2,mo.2,hy]
  rfl
end ECDSAAdd.Entrant.TickGap
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def recordTop (sx sy q : Wire) (x y cs : List Wire) : Program :=
  skywalkSignToggle sx sy q ++ signedAddTop q x y cs ++ skywalkSignToggle sx sy q

theorem signedAddTop_counts (n : Nat) (q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length) :
    toffoliCount (signedAddTop q x y cs)=n ∧ measurementCount (signedAddTop q x y cs)=n+1 := by
  have h := TopCarry.addInPlaceTop_counts n x y cs q hy (hx.trans hy.symm) hc
  simp only [signedAddTop,toffoliCount_append,measurementCount_append,
    (signComplement_counts q x).1,(signComplement_counts q x).2,h.1,h.2]
  exact ⟨by omega,by omega⟩

theorem toggle_frame (sx sy q : Wire) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (w : Wire) (hw : w≠q) :
    (run (skywalkSignToggle sx sy q) m s).basis w=s.basis w := by
  rw [skywalkSignToggle_correct sx sy q hqx hqy]
  simp [writeBit,hw]

theorem recordTop_eq (n : Nat) (sx sy q : Wire) (x y cs : List Wire)
    (hx : x.length=n+2) (hy : y.length=n+2) (hc : cs.length+1=y.length)
    (hn : (q::(x++y++cs)).Nodup) (hqx : sx≠q) (hqy : sy≠q)
    (s : State) (m : List Bool) (clean : ∀w∈cs,s.basis w=false)
    (source : Shape n (regValue x s.basis))
    (sum : Shape n (regValue y (run (signedRecord sx sy q x y cs) [] s).basis)) :
    run (recordTop sx sy q x y cs) m s=run (signedRecord sx sy q x y cs) m s := by
  have qrest := (List.nodup_cons.mp hn).1
  have away (w : Wire) (hw : w∈x++y++cs) : w≠q := by
    intro he; subst w; exact qrest hw
  let u := run (skywalkSignToggle sx sy q) [] s
  have ut (w : Wire) (hw : w≠q) : u.basis w=s.basis w := toggle_frame sx sy q hqx hqy s [] w hw
  have ux : regValue x u.basis=regValue x s.basis :=
    regValue_congr _ _ _ (fun w hw => ut w (away w (by simp [hw])))
  have uc : ∀w∈cs,u.basis w=false := by
    intro w hw
    exact (ut w (away w (by simp [hw]))).trans (clean w hw)
  have zx := (skywalkSignToggle_counts sx sy q).2
  have out (r : List Bool) :
      regValue y (run (skywalkSignToggle sx sy q) r (run (signedAdd q x y cs) r u)).basis =
      regValue y (run (signedAdd q x y cs) r u).basis :=
    regValue_congr _ _ _ (fun w hw => toggle_frame sx sy q hqx hqy _ r w (away w (by simp [hw])))
  have old : regValue y (run (signedRecord sx sy q x y cs) [] s).basis =
      regValue y (run (signedAdd q x y cs) [] u).basis := by
    simp only [signedRecord,List.append_assoc]
    rw [TopCarry.run_zero_head _ _ [] s zx,run_append,run_take]
    simpa only [List.drop_nil,u] using out []
  rw [old] at sum
  have eq (r : List Bool) := signedAddTop_eq n q x y cs hx hy hc hn u r uc (ux ▸ source) sum
  have mc := (signedAddTop_counts n q x y cs hx hy hc).2
  have mo := (signedWord_counts q x y cs (hx.trans hy.symm) hc).2.1
  simp only [recordTop,signedRecord,List.append_assoc]
  rw [TopCarry.run_zero_head _ _ m s zx,TopCarry.run_zero_head _ _ m s zx]
  rw [run_append,run_append,run_take,run_take,eq,mc,mo,hy]
  rfl
end ECDSAAdd.Entrant.TickGap
end
section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def narrowTop (L : NarrowSignedRecordLayout) (n : Nat) : Program :=
  recordTop L.sx L.sy L.q (L.x.take n) (L.y.take n) (L.carry.take (n-1)) ++
    signComplement L.q (L.y.drop n)

theorem record_source (L : NarrowSignedRecordLayout) (n : Nat) (hw : L.Widths n) (hn : L.wires.Nodup)
    (s : State) (m : List Bool) (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0) :
    regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) m s).basis = regValue L.xp s.basis := by
  have h := signedRecord_spec L.xlo L.ylo L.sx L.sy L.q L.carryLow (L.short_nodup hn)
    (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
    (signedRegValue L.xp s.basis) (signedRegValue L.yp s.basis) s m ⟨hq,rfl,rfl,clean⟩
  have eq := (signedRegValue_eq_iff L.xp _ _).mp h.2.2.1
  exact regValue_congr _ _ _ eq

theorem narrowTop_eq (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) (s : State) (m : List Bool)
    (hq : s.basis L.q=false) (clean : regValue L.carryLow s.basis=0)
    (source : Shape n (regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis))
    (sum : Shape n (regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis)) :
    run (narrowTop L (n+2)) m s=run (narrowSignedRecord L (n+2)) m s := by
  have views := L.views (n+2) hw
  have clean' : ∀w∈L.carryLow,s.basis w=false := (regValue_zero _ _).mp clean
  have qx : L.sx≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he
    exact (List.nodup_cons.mp (L.short_nodup hn)).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have fan (r : List Wire) (hr : ∀w∈r,w∉L.yhigh) (v : State) (record : List Bool) :
      regValue r (run (signComplement L.q L.yhigh) record v).basis=regValue r v.basis := by
    have f := signComplement_correct L.q L.yhigh (L.high_nodup hn) (L.q_high hn) v record
    exact regValue_congr _ _ _ (fun w hw => f.2.1 w (hr w hw))
  have xaway : ∀w∈L.xp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp only [NarrowSignedRecordLayout.x,List.mem_append] at *; tauto)
  have yaway : ∀w∈L.yp,w∉L.yhigh := by
    intro w hw'
    exact L.other_away_high hn w (by simp [hw'])
  have outx : regValue L.xp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.xp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.xp xaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  have outy : regValue L.yp (run (narrowSignedRecord L (n+2)) [] s).basis=
      regValue L.yp (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s).basis := by
    simp only [narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
    rw [run_append,run_take]
    simpa using fan L.yp yaway (run (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) [] s) []
  rw [outx,record_source L (n+2) hw hn s [] hq clean] at source
  rw [outy] at sum
  have eq (r : List Bool) := recordTop_eq n L.sx L.sy L.q L.xp L.yp L.carryLow
    hw.x hw.y (hw.carry.trans hw.y.symm) (L.short_nodup hn) qx qy s r clean' source sum
  have mc := signedAddTop_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have rz := (skywalkSignToggle_counts L.sx L.sy L.q).2
  have old := (signedWord_counts L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)).2.1
  have counts : measurementCount (recordTop L.sx L.sy L.q L.xp L.yp L.carryLow)=
      measurementCount (signedRecord L.sx L.sy L.q L.xp L.yp L.carryLow) := by
    simp only [recordTop,signedRecord,measurementCount_append,rz,mc.2,old,hw.y]
    omega
  simp only [narrowTop,narrowSignedRecord,views.1,views.2.1,views.2.2.1,views.2.2.2]
  rw [run_append,run_append,run_take,run_take,eq,counts]
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic Baselines Challenge RecordedQuantum

theorem signedAddTop_support (q : Wire) (x y cs : List Wire)
    (hx : x.length=y.length) (hc : cs.length+1=y.length) :
    wires (signedAddTop q x y cs) ⊆ wires (signedAdd q x y cs) := by
  rw [(signedWord_wires q x y cs hx hc).1]
  have fan : wires (signComplement q x) ⊆ (q::(x++y++cs)).toFinset := by
    intro w hw
    have h := signComplement_wires_subset q x hw
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
    tauto
  simp only [signedAddTop,wires_append,Finset.union_subset_iff]
  exact ⟨⟨fan,TopCarry.addInPlaceTop_wires x y cs q⟩,fan⟩

theorem narrowTop_counts (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    toffoliCount (narrowTop L (n+2))+1=toffoliCount (narrowSignedRecord L (n+2)) ∧
      measurementCount (narrowTop L (n+2))=measurementCount (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have h := signedAddTop_counts n L.q L.xp L.yp L.carryLow hw.x hw.y (hw.carry.trans hw.y.symm)
  have old := narrowSignedRecord_counts L (n+2) hw
  have z := skywalkSignToggle_counts L.sx L.sy L.q
  have f := signComplement_counts L.q L.yhigh
  simp only [narrowTop,recordTop,v.1,v.2.1,v.2.2.1,v.2.2.2,
    toffoliCount_append,measurementCount_append,z.1,z.2,h.1,h.2,f.1,f.2,old.1,old.2.1]
  exact ⟨by omega,by omega⟩

theorem narrowTop_support (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    wires (narrowTop L (n+2)) ⊆ wires (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have sub := signedAddTop_support L.q L.xp L.yp L.carryLow (hw.x.trans hw.y.symm) (hw.carry.trans hw.y.symm)
  simp only [narrowTop,narrowSignedRecord,recordTop,signedRecord,v.1,v.2.1,v.2.2.1,v.2.2.2,wires_append]
  exact Finset.union_subset_union (Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) sub)
    (Finset.Subset.refl _)) (Finset.Subset.refl _)

theorem signedAddTop_physical (q : Wire) (x y cs : List Wire) (hn : (q::(x++y++cs)).Nodup) :
    GatePhysical (signedAddTop q x y cs) := by
  have qx : q∉x := fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
  have fan := signComplement_physical q x qx
  have top := TopCarry.addInPlaceTop_physical x y cs q hn
  simp only [signedAddTop,gatePhysical_append]
  exact ⟨⟨fan,top⟩,fan⟩

theorem narrowTop_physical (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2))
    (hn : L.wires.Nodup) : GatePhysical (narrowTop L (n+2)) := by
  have v := L.views (n+2) hw
  have nd := L.short_nodup hn
  have qx : L.sx≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.xp,←he])
  have qy : L.sy≠L.q := by
    intro he; exact (List.nodup_cons.mp nd).1 (by simp [NarrowSignedRecordLayout.yp,←he])
  have toggle : GatePhysical (skywalkSignToggle L.sx L.sy L.q) := by
    simp [skywalkSignToggle,GatePhysical,PhysicalInstr,ProperGate,qx,qy]
  have top := signedAddTop_physical L.q L.xp L.yp L.carryLow nd
  have fan := signComplement_physical L.q L.yhigh (L.q_high hn)
  simp only [narrowTop,recordTop,v.1,v.2.1,v.2.2.1,v.2.2.2,gatePhysical_append]
  exact ⟨⟨⟨toggle,top⟩,toggle⟩,fan⟩

theorem top_slots_le_old (x y cs : List Wire) (c : Wire) :
    gateSlots (TopCarry.addInPlaceTop x y cs c) ≤ gateSlots (addInPlace x y cs c) := by
  induction x generalizing y cs c with
  | nil => simp [TopCarry.addInPlaceTop,addInPlace]
  | cons a as ih =>
    cases as with
    | nil =>
      cases y with
      | nil => simp [TopCarry.addInPlaceTop,addInPlace]
      | cons b bs => cases bs <;> simp [TopCarry.addInPlaceTop,addInPlace]
    | cons a' as =>
      cases y with
      | nil => simp [TopCarry.addInPlaceTop,addInPlace]
      | cons b bs =>
        cases bs with
        | nil => simp [TopCarry.addInPlaceTop,addInPlace]
        | cons b' bs =>
          cases cs with
          | nil => simp [TopCarry.addInPlaceTop,addInPlace]
          | cons d ds =>
            have h := ih (b'::bs) ds d
            simp only [TopCarry.addInPlaceTop,addInPlace,gateSlots_append] at h ⊢
            split_ifs <;> simp only [majority_gateSlots,gateSlots_cons,gateSlots_nil,instructionSlots] at h ⊢ <;> omega

theorem narrowTop_slots (n : Nat) (L : NarrowSignedRecordLayout) (hw : L.Widths (n+2)) :
    gateSlots (narrowTop L (n+2)) ≤ gateSlots (narrowSignedRecord L (n+2)) := by
  have v := L.views (n+2) hw
  have top := top_slots_le_old L.xp L.yp L.carryLow L.q
  simp only [narrowTop,narrowSignedRecord,recordTop,signedRecord,signedAddTop,signedAdd,
    v.1,v.2.1,v.2.2.1,v.2.2.2,gateSlots_append]
  omega
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

/-- The two post-tick signed values fit below the strict late-stage cap. -/
theorem band_step_values (x p i : Nat) (hp0 : 0 < p) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p)
    (hi : 255 ≤ i  ∧  i ≤ 286) :
    let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int));
    let n := W.compactSkywalkTickPostWidth i-2;
    -((2^n:Nat):Int)  ≤  (SkywalkRails.step r).h  ∧  (SkywalkRails.step r).h  <  ((2^n:Nat):Int)  ∧ 
    -((2^n:Nat):Int)  ≤  (SkywalkRails.step r).k  ∧  (SkywalkRails.step r).k  <  ((2^n:Nat):Int) := by
  dsimp only
  have nw : W.compactSkywalkTickPostWidth i-2=510-i := by
    unfold W.compactSkywalkTickPostWidth W.narrowSkywalkWidth
    omega
  rw [nw]
  have cap := strict_sum_band x p (i+1) hp0 hpo hp gap hx cop (by omega)
  obtain ⟨G,S,enc⟩ := SkywalkTrace.iter_encoded (i+1) false false (SkywalkNat.init x p) hp0 hpo
  simp only [SkywalkNat.init] at enc
  rw [Function.iterate_succ_apply'] at enc
  let r := SkywalkTrace.next^[i] (SkywalkRails.encode false false (x:Int) (p:Int))
  let z := SkywalkNat.step^[i+1] (SkywalkNat.init x p)
  change SkywalkTrace.next r=SkywalkRails.encode G S (z.u:Int) (z.v:Int) at enc
  change z.u+z.v < 2^(511-(i+1)) at cap
  have exp : 511-(i+1)=510-i := by omega
  rw [exp] at cap
  have abs := SkywalkRails.encode_abs_sum_bound G S z.u z.v (z.u+z.v) (Nat.le_refl _)
  rw [←enc] at abs
  change |(SkywalkRails.step r).h|  ≤  ((z.u+z.v:Nat):Int)  ∧ 
    |(SkywalkRails.step r).k|  ≤  ((z.u+z.v:Nat):Int) at abs
  have cap' : ((z.u+z.v:Nat):Int) < ((2^(510-i):Nat):Int) := by exact_mod_cast cap
  have ah := abs_le.mp abs.1
  have ak := abs_le.mp abs.2
  dsimp only [r] at ah ak
  exact ⟨by omega,by omega,by omega,by omega⟩

theorem repaired_output_shape (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p)
    (hi : 255 ≤ i  ∧  i ≤ 286) (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    let L := W.compactSkywalkTickLayout w i;
    let n := W.compactSkywalkTickPostWidth i;
    Shape (n-2) (regValue (L.half.take n) (run (W.repairedTick w i) m s).basis)  ∧ 
      Shape (n-2) (regValue (L.b.take n) (run (W.repairedTick w i) m s).basis) := by
  dsimp only
  have hgap : p+2^32 ≤ 2^256 := Nat.le_of_lt gap
  rw [W.repairedTick_eq w hn x p i hp0 hx0 hpo hp hgap hx cop (by omega) s m hs]
  have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp hgap hx cop (by omega) s hs
  have fit := W.narrowSkywalk_iter_fit x p i hp0 hx0 hpo hp hgap hx cop (by omega)
  have out := W.compactSkywalkTickOutput_spec w i (by omega) hn _ _ _ fit.1 fit.2.1 fit.2.2.1 fit.2.2.2.1 fit.2.2.2.2 s [] input
  have bounds := band_step_values x p i hp0 hpo hp gap hx cop hi
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have ns : n-2+2=n := by
    have width := W.compactSkywalkTick_width_bounds i (by omega)
    dsimp only [n]
    omega
  have lenA : n ≤ L.half.length := by
    rw [W.compactSkywalkTick_half w i (by omega),wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i (by omega)).2.2.1
  have lenB : n ≤ L.b.length := by
    rw [W.compactSkywalkTick_b w i (by omega),wireBlock_length]
    exact (W.compactSkywalkTick_width_bounds i (by omega)).2.2.1
  have aview : (W.compactSkywalkTickARelease w i).retained=L.half.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenA
  have bview : (W.compactSkywalkTickBRelease w i).retained=L.b.take n :=
    compactSkywalkSignWord_retained _ _ (by omega) lenB
  have a := out.2.1
  have b := out.2.2.1
  rw [aview] at a
  rw [bview] at b
  have lenA' : (L.half.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenA]
  have lenB' : (L.b.take n).length=n := by simp [List.length_take,Nat.min_eq_left lenB]
  unfold signedRegValue at a b
  rw [lenA'] at a
  rw [lenB'] at b
  change Shape (n-2) (regValue (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis) ∧
    Shape (n-2) (regValue (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
  constructor
  · apply shape_of_signed (n-2) _ (by simpa [ns,lenA'] using regValue_lt (L.half.take n) (run (W.compactSkywalkTick w i) [] s).basis)
    · rw [ns,a]; exact bounds.1
    · rw [ns,a]; exact bounds.2.1
  · apply shape_of_signed (n-2) _ (by simpa [ns,lenB'] using regValue_lt (L.b.take n) (run (W.compactSkywalkTick w i) [] s).basis)
    · rw [ns,b]; exact bounds.2.2.1
    · rw [ns,b]; exact bounds.2.2.2
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

def head (w : Nat → Wire) (i : Nat) : Program :=
  let L := W.compactSkywalkTickLayout w i
  (if i=224 ∨ (256 ≤ i  ∧  i ≤ 509) then W.repairedRoute L
    else skywalkRoute L.a0 L.b0 L.ah L.bh) ++ skywalkSignedHalf L.aSign L.ext

def tail (w : Nat → Wire) (i : Nat) : Program :=
  [.CX (W.compactSkywalkTickLayout w i).previous (W.compactSkywalkTickLayout w i).a0] ++
    W.compactSkywalkTickCleanup w i

def tick (w : Nat → Wire) (i : Nat) : Program :=
  if 255 ≤ i  ∧  i ≤ 286 then
    head w i ++ narrowTop (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
      (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i
  else W.repairedTick w i

theorem old_split (w : Nat → Wire) (i : Nat) :
    W.repairedTick w i = head w i ++
      narrowSignedRecord (narrowSkywalkRecordLayout (W.compactSkywalkTickLayout w i)
        (W.compactSkywalkTickPostWidth i)) (W.compactSkywalkTickPostWidth i) ++ tail w i := by
  simp only [W.repairedTick,head,tail,W.compactSkywalkTick,narrowSkywalkTick]
  split_ifs  <;> simp only [List.append_assoc]

theorem repairedRoute_small_support (L : SkywalkIntegerLayout) (hv : L.Valid) (hpos : 0 < L.bMid.length) :
    wires (W.repairedRoute L) ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
  have lo := swapRegisters_wires L.a0 L.aMid L.bMid hv.mids
  have tm : L.bMid.getD (L.bMid.length-1) 0∈L.bMid := W.repair_member_getD _ _ (by omega)
  have ls : wires (swapRegisters L.a0 L.aMid L.bMid) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    have h := lo hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh] at h ⊢
    tauto
  have ss : wires (W.signRepair L.aSign L.bSign L.previous (L.bMid.getD (L.bMid.length-1) 0)) ⊆
      (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [W.signRepair,wires,Instr.wires,correctionWires,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,SkywalkIntegerLayout.bh,
      List.not_mem_nil,or_false]
    have ht : q=L.bMid.getD (L.bMid.length-1) 0 → q∈L.bMid := fun he => he ▸ tm
    tauto
  have cx : wires [.CX L.a0 L.b0] ⊆ (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    intro q hq
    simp only [wires,Instr.wires,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at hq
    simp only [List.mem_toFinset,List.mem_cons,List.mem_append]
    tauto
  simp only [W.repairedRoute,W.repairedSwap,wires_append,Finset.union_subset_iff]
  exact ⟨⟨ls,ss⟩,cx⟩

theorem head_aux (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).history::(W.compactSkywalkTickLayout w i).carry) :
    (run (head w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have hpos : 0 < L.bMid.length := by
    change 0 < (wireBlock w 771 (W.compactSkywalkTickPreWidth i-2)).length
    rw [wireBlock_length]
    have width := W.compactSkywalkTick_width_bounds i hi
    omega
  have dis : List.Disjoint (L.history::L.carry) (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)) := by
    have nd : ((L.history::L.carry)++(L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh))).Nodup := by
      apply List.nodup_iff_count.mpr
      intro a
      have h := List.nodup_iff_count.mp hv.nodup a
      simp only [SkywalkIntegerLayout.wires,List.count_cons,List.count_append] at h ⊢
      omega
    exact (List.nodup_append'.mp nd).2.2
  have qaway : q∉L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh) := List.disjoint_left.mp dis hq
  have sup : wires (head w i) ⊆ (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
    have inc : (L.previous::L.a0::L.b0::(L.ah++L.bh)).toFinset ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [List.mem_toFinset,List.mem_cons] at ha ⊢
      tauto
    have repair := (repairedRoute_small_support L hv hpos).trans inc
    have full : wires (skywalkRoute L.a0 L.b0 L.ah L.bh) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      have h := skywalkRoute_wires_subset L.a0 L.b0 L.ah L.bh (L.high_lengths hv) ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append] at h ⊢
      tauto
    have half : wires (skywalkSignedHalf L.aSign L.ext) ⊆
        (L.previous::L.ext::L.a0::L.b0::(L.ah++L.bh)).toFinset := by
      intro a ha
      simp only [skywalkSignedHalf,wires,Instr.wires,Finset.mem_union,Finset.mem_insert,
        Finset.mem_singleton,Finset.notMem_empty,or_false] at ha
      simp only [List.mem_toFinset,List.mem_cons,List.mem_append,SkywalkIntegerLayout.ah,List.mem_singleton]
      tauto
    simp only [head,wires_append,Finset.union_subset_iff]
    split_ifs  <;> exact ⟨by assumption,half⟩
  exact run_preserves_outside _ _ _ _ (fun h => qaway (List.mem_toFinset.mp (sup h)))

theorem tail_prefix (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup)
    (s : State) (m : List Bool) (q : Wire)
    (hq : q∈(W.compactSkywalkTickLayout w i).half.take (W.compactSkywalkTickPostWidth i) ++
      (W.compactSkywalkTickLayout w i).b.take (W.compactSkywalkTickPostWidth i)) :
    (run (tail w i) m s).basis q=s.basis q := by
  let L := W.compactSkywalkTickLayout w i
  let n := W.compactSkywalkTickPostWidth i
  have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
  have words := W.compactSkywalkTick_words_disjoint w i hi hn
  have nd := (List.nodup_cons.mp (L.record_nodup hv)).2
  have wa : L.half.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).1
  have wb : L.b.Nodup := (List.nodup_append'.mp (List.nodup_append'.mp nd).1).2.1
  have adot : List.Disjoint (L.half.take n) (L.half.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wa
  have bdot : List.Disjoint (L.b.take n) (L.b.drop n) := by
    apply (List.nodup_append'.mp ?_).2.2
    rw [List.take_append_drop]
    exact wb
  have apart : q∉L.half.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact List.disjoint_left.mp adot hqa
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_drop h) (List.mem_of_mem_take hqb)
  have bpart : q∉L.b.drop n := by
    rcases List.mem_append.mp hq with hqa|hqb
    · exact fun h => List.disjoint_left.mp words (List.mem_of_mem_take hqa) (List.mem_of_mem_drop h)
    · exact List.disjoint_left.mp bdot hqb
  have q0 : q≠L.a0 := by
    have qm : q∈L.half++L.b := by
      rcases List.mem_append.mp hq with hqa|hqb
      · exact List.mem_append_left _ (List.mem_of_mem_take hqa)
      · exact List.mem_append_right _ (List.mem_of_mem_take hqb)
    intro he
    subst q
    have h := List.nodup_iff_count.mp hv.nodup L.a0
    have hq' := List.count_pos_iff.mpr qm
    simp only [SkywalkIntegerLayout.wires,SkywalkIntegerLayout.half,SkywalkIntegerLayout.b,List.count_nil,List.count_cons,List.count_append,
      List.count_singleton] at h hq'
    simp only [beq_self_eq_true,if_true] at h
    omega
  have valid := W.compactSkywalkTick_release_valid w i hi hn
  have af (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickARelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.1 v r).2.1 q apart
  have bf (v : State) (r : List Bool) :
      (run (compactSkywalkSignRelease (W.compactSkywalkTickBRelease w i)) r v).basis q=v.basis q :=
    (compactSkywalkSignRelease_phase_frame _ valid.2 v r).2.1 q bpart
  simp only [tail,W.compactSkywalkTickCleanup,run_append,run_take]
  rw [bf,af]
  change Function.update s.basis L.a0 (s.basis L.a0 ^^ s.basis L.previous) q = s.basis q
  exact Function.update_of_ne q0 _ _
end ECDSAAdd.Entrant.TickGap
end

section
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Entrant.TickGap
open Arithmetic

theorem tick_eq (w : Nat → Wire) (hn : (skywalkPoolWires w).Nodup)
    (x p i : Nat) (hp0 : 0 < p) (hx0 : 0 < x) (hpo : p%2=1)
    (hp : p < 2^256) (gap : p+2^32 < 2^256) (hx : x < p) (cop : x.Coprime p) (hi : i < 512)
    (s : State) (m : List Bool)
    (hs : W.CompactSkywalkStage w (SkywalkRails.encode false false (x:Int) (p:Int)) i s.basis) :
    run (tick w i) m s=run (W.repairedTick w i) m s := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    let P := head w i
    let Q := narrowSignedRecord R n
    let E := tail w i
    let u := run P (m.take (measurementCount P)) s
    let v := run Q (m.drop (measurementCount P)) u
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have width := W.compactSkywalkTick_width_bounds i hi
    have npos : 2 ≤ n := width.2.1
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have nd : R.wires.Nodup := narrowSkywalkRecord_nodup L hv n (by omega) nlen
    have n2 : n-2+2=n := by omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have whole : run (W.repairedTick w i) m s=
        run E ((m.drop (measurementCount P)).drop (measurementCount Q)) v := by
      rw [old_split,List.append_assoc,run_append,run_take,run_append,run_take]
      simp only [P,Q,E,u,v,run_take]
      rfl
    have sizes := repaired_output_shape w hn x p i hp0 hx0 hpo hp gap hx cop band s m hs
    have keep (r : List Wire) (hr : r⊆L.half.take n++L.b.take n) :
        regValue r (run (W.repairedTick w i) m s).basis=regValue r v.basis := by
      rw [whole]
      apply regValue_congr
      intro q hq
      exact tail_prefix w i hi hn v _ q (hr hq)
    have shapeX : Shape (n-2) (regValue (L.half.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_left _ hq)]
      exact sizes.1
    have shapeY : Shape (n-2) (regValue (L.b.take n) v.basis) := by
      rw [←keep _ (by intro q hq; exact List.mem_append_right _ hq)]
      exact sizes.2
    have record0 : (run Q [] u).basis=v.basis := run_basis_records Q u u [] (m.drop (measurementCount P)) rfl
    have orig := narrowSkywalkRecord_views L hv n (by omega) nlen
    have views := R.views n hw
    have xx : R.xp=L.half.take n := by rw [←views.1]; rw [orig.1]
    have yy : R.yp=L.b.take n := by rw [←views.2.1]; rw [orig.2.1]
    have input := W.compactSkywalkStage_local_input w hn x p i hp0 hx0 hpo hp (Nat.le_of_lt gap) hx cop hi s hs
    have uq : u.basis R.q=false := by
      apply (head_aux w i hi hn s _ L.history (List.mem_cons_self)).trans
      exact input.2.2.2.2.1
    have clean : regValue R.carryLow u.basis=0 := by
      apply (regValue_zero _ _).mpr
      intro q hq
      have qm : q∈L.carry := List.mem_of_mem_take hq
      apply (head_aux w i hi hn s _ q (List.mem_cons_of_mem _ qm)).trans
      exact (regValue_zero _ _).mp input.2.2.2.2.2 q qm
    have eq (r : List Bool) : run (narrowTop R n) r u=run Q r u := by
      have a : Shape (n-2) (regValue R.xp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,xx,record0]
        exact shapeX
      have b : Shape (n-2) (regValue R.yp (run (narrowSignedRecord R (n-2+2)) [] u).basis) := by
        rw [n2,yy,record0]
        exact shapeY
      simpa only [n2] using narrowTop_eq (n-2) R hw' nd u r uq clean a b
    have counts : measurementCount (narrowTop R n)=measurementCount Q := by
      simpa only [n2] using (narrowTop_counts (n-2) R hw').2
    simp only [tick,if_pos band]
    rw [old_split]
    change run ((P++narrowTop R n)++E) m s=run ((P++Q)++E) m s
    conv_lhs => rw [List.append_assoc,run_append P (narrowTop R n++E)]
    conv_rhs => rw [List.append_assoc,run_append P (Q++E)]
    change run (narrowTop R n++E) (m.drop (measurementCount P)) u = run (Q++E) (m.drop (measurementCount P)) u
    rw [run_append (narrowTop R n) E,run_append Q E]
    rw [run_take (narrowTop R n),run_take Q,eq,counts]
  · simp only [tick,if_neg band]

def due (i : Nat) : Nat := if 255 ≤ i  ∧  i ≤ 286 then 1 else 0

theorem tick_counts (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    toffoliCount (tick w i)+due i=toffoliCount (W.repairedTick w i)  ∧ 
    measurementCount (tick w i)=measurementCount (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_counts (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split]
    simp only [tick,if_pos band,due,if_pos band,toffoliCount_append,measurementCount_append]
    exact ⟨by omega,by omega⟩
  · simp only [tick,if_neg band,due,if_neg band,Nat.add_zero,and_self]

theorem tick_support (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    wires (tick w i) ⊆ wires (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_support (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split]
    simp only [tick,if_pos band,wires_append]
    exact Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) h) (Finset.Subset.refl _)
  · simp only [tick,if_neg band]
    exact Finset.Subset.refl _

theorem tick_slots (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    Challenge.gateSlots (tick w i)  ≤  Challenge.gateSlots (W.repairedTick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_slots (n-2) R hw'
    simp only [n2] at h
    dsimp only [R,n,L] at h
    rw [old_split]
    simp only [tick,if_pos band,Challenge.gateSlots_append]
    omega
  · simp only [tick,if_neg band]
    exact Nat.le_refl _

theorem tick_physical (w : Nat → Wire) (i : Nat) (hi : i < 512) (hn : (skywalkPoolWires w).Nodup) :
    GatePhysical (tick w i) := by
  by_cases band : 255 ≤ i  ∧  i ≤ 286
  · let L := W.compactSkywalkTickLayout w i
    let n := W.compactSkywalkTickPostWidth i
    let R := narrowSkywalkRecordLayout L n
    have width := W.compactSkywalkTick_width_bounds i hi
    have hv : L.Valid := W.compactSkywalkTick_valid w i hi hn
    have nlen : n ≤ L.half.length := by rw [W.compactSkywalkTick_half w i hi,wireBlock_length]; exact width.2.2.1
    have hw : R.Widths n := narrowSkywalkRecord_widths L hv n (by omega) nlen
    have n2 : n-2+2=n := by dsimp only [n]; omega
    have hw' : R.Widths (n-2+2) := by simpa only [n2] using hw
    have h := narrowTop_physical (n-2) R hw' (narrowSkywalkRecord_nodup L hv n (by omega) nlen)
    simp only [n2] at h
    dsimp only [R,n,L] at h
    have old := W.repairedTick_physical w i hi hn
    rw [old_split] at old
    simp only [tick,if_pos band,gatePhysical_append] at old ⊢
    exact ⟨⟨old.1.1,h⟩,old.2⟩
  · simpa only [tick,if_neg band] using W.repairedTick_physical w i hi hn
end ECDSAAdd.Entrant.TickGap
end
