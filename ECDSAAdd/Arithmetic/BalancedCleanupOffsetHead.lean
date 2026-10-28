import ECDSAAdd.Arithmetic.BalancedCleanupOffsetProgram
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
attribute [local irreducible] run majority mappedMajority mappedSum mappedEraseCarry eraseCarry

def prepareHead (b : MappedBit) (a y cinC cinB c d : Wire) : Program :=
  mappedMajority b y cinC c++mappedSum b y cinC++[.X y]++majority a y cinB d

def releaseHead (b : MappedBit) (a y cinC cinB c d : Wire) : Program :=
  eraseCarry a y cinB d++[.X y]++mappedSum b y cinC++mappedEraseCarry b y cinC c

theorem bit_write (b : MappedBit) (s : BasisState) (q : Wire) (v : Bool)
    (ha : ∀w∈b.wire,w≠q) : b.value (writeBit s q v)=b.value s := by
  apply mappedBit_value_congr
  intro w hw
  simp only [writeBit,Function.update_of_ne (ha w hw)]

theorem sum_involution (B Y C : Bool) : sumBit B (sumBit B Y C) C=Y := by
  cases B <;> cases Y <;> cases C <;> rfl

theorem write_twice (s : BasisState) (q : Wire) (u v : Bool) :
    writeBit (writeBit s q u) q v=writeBit s q v := by
  funext w
  by_cases h : w=q <;> simp [writeBit,h]

theorem x_run (q : Wire) (s : State) (m : List Bool) :
    run [.X q] m s=⟨s.phase,writeBit s.basis q (!s.basis q)⟩ := by simp only [run]

theorem prepareHead_run (b : MappedBit) (a y cinC cinB c d : Wire)
    (hn : [a,y,cinC,cinB,c,d].Nodup) (ha : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d])
    (s : State) (m : List Bool) (hc : s.basis c=false) (hd : s.basis d=false) :
    run (prepareHead b a y cinC cinB c d) m s=
      let K := carryBit (b.value s.basis) (s.basis y) (s.basis cinC)
      let S := sumBit (b.value s.basis) (s.basis y) (s.basis cinC)
      ⟨s.phase,writeBit (writeBit (writeBit s.basis c K) y (!S)) d
        (carryBit (s.basis a) (!S) (s.basis cinB))⟩ := by
  have nd := hn
  have nr := List.nodup_reverse.mpr hn
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd nr
  have src (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d]) : ∀w∈b.wire,w≠q :=
    fun w hw e => ha w hw (e.symm ▸ hq)
  have nc : [y,cinC,c].Nodup := by simp [List.nodup_cons,nd,nr]
  have nm : [a,y,cinB,d].Nodup := by simp [List.nodup_cons,nd,nr]
  have source : ∀w∈b.wire,w∉[y,cinC,c] := by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨src y (by simp) w hw,src cinC (by simp) w hw,src c (by simp) w hw⟩
  let K := carryBit (b.value s.basis) (s.basis y) (s.basis cinC)
  let S := sumBit (b.value s.basis) (s.basis y) (s.basis cinC)
  generalize eu : run (mappedMajority b y cinC c) m s=u
  generalize ev : run (mappedSum b y cinC) m u=v
  generalize ew : run [.X y] m v=w
  generalize et : run (majority a y cinB d) m w=t
  have us := mappedMajority_correct b y cinC c nc source s m
  rw [eu,hc,Bool.false_xor] at us
  change u=⟨s.phase,writeBit s.basis c K⟩ at us
  have uf (q : Wire) (hq : q≠c) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ub : b.value u.basis=b.value s.basis := by rw [us]; exact bit_write b s.basis c K (src c (by simp))
  have vu := mappedSum_correct b y cinC (by simp [nd,nr]) (src y (by simp)) u m
  rw [ev,ub,uf y (by simp [nd,nr]),uf cinC (by simp [nd,nr])] at vu
  change v=⟨u.phase,writeBit u.basis y S⟩ at vu
  have vf (q : Wire) (hq : q≠y) : v.basis q=u.basis q := by
    rw [vu]
    simp only [writeBit,Function.update_of_ne hq]
  have vy : v.basis y=S := by rw [vu]; simp only [writeBit,Function.update_self]
  have wv := x_run y v m
  rw [ew,vy] at wv
  have wf (q : Wire) (hq : q≠y) : w.basis q=v.basis q := by
    rw [wv]
    simp only [writeBit,Function.update_of_ne hq]
  have wa : w.basis a=s.basis a := (wf a (by simp [nd,nr])).trans
    ((vf a (by simp [nd,nr])).trans (uf a (by simp [nd,nr])))
  have wi : w.basis cinB=s.basis cinB := (wf cinB (by simp [nd,nr])).trans
    ((vf cinB (by simp [nd,nr])).trans (uf cinB (by simp [nd,nr])))
  have wy : w.basis y= !S := by rw [wv]; simp only [writeBit,Function.update_self]
  have wd : w.basis d=false := (wf d (by simp [nd,nr])).trans
    ((vf d (by simp [nd,nr])).trans ((uf d (by simp [nd,nr])).trans hd))
  have tw := majority_correct a y cinB d nm w m
  rw [et,wa,wi,wy,wd,Bool.false_xor] at tw
  have actual : run (prepareHead b a y cinC cinB c d) m s=t := by
    simp only [prepareHead,List.append_assoc,run_append]
    simp only [run_take]
    simp only [(mappedBit_counts b y cinC c).2.1,(mappedBit_counts b y cinC c).2.2.2.2.2,
      show measurementCount [.X y]=0 from rfl,List.drop_zero]
    rw [eu,ev,ew,et]
  rw [actual,tw,wv,vu,us]
  simp only [write_twice,K,S]

theorem releaseHead_run (b : MappedBit) (a y cinC cinB c d : Wire)
    (hn : [a,y,cinC,cinB,c,d].Nodup) (ha : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d])
    (B A Y C D : Bool) (s : State) (m : List Bool)
    (hb : b.value s.basis=B) (hA : s.basis a=A) (hC : s.basis cinC=C)
    (hD : s.basis cinB=D) (hy : s.basis y= !(sumBit B Y C))
    (hc : s.basis c=carryBit B Y C) (hd : s.basis d=carryBit A (!(sumBit B Y C)) D) :
    run (releaseHead b a y cinC cinB c d) m s=
      ⟨s.phase,writeBit (writeBit (writeBit s.basis d false) y Y) c false⟩ := by
  have nd := hn
  have nr := List.nodup_reverse.mpr hn
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd nr
  have src (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d]) : ∀w∈b.wire,w≠q :=
    fun w hw e => ha w hw (e.symm ▸ hq)
  have nc : [y,cinC,c].Nodup := by simp [List.nodup_cons,nd,nr]
  have source : ∀w∈b.wire,w∉[y,cinC,c] := by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨src y (by simp) w hw,src cinC (by simp) w hw,src c (by simp) w hw⟩
  let tail := m.drop 1
  generalize eu : run (eraseCarry a y cinB d) m s=u
  generalize ev : run [.X y] tail u=v
  generalize ew : run (mappedSum b y cinC) tail v=w
  generalize et : run (mappedEraseCarry b y cinC c) tail w=t
  have us := eraseCarry_correct a y cinB d (by simp [nd,nr]) (by simp [nd,nr])
    (by simp [nd,nr]) s (by rw [hA,hy,hD]; exact hd) m
  rw [eu] at us
  have uf (q : Wire) (hq : q≠d) : u.basis q=s.basis q := by
    rw [us]
    simp only [writeBit,Function.update_of_ne hq]
  have ub : b.value u.basis=B := by
    rw [us,bit_write b s.basis d false (src d (by simp))]
    exact hb
  have uy : u.basis y= !(sumBit B Y C) := (uf y (by simp [nd,nr])).trans hy
  have ucin : u.basis cinC=C := (uf cinC (by simp [nd,nr])).trans hC
  have vu := x_run y u tail
  rw [ev,uy,Bool.not_not] at vu
  have vf (q : Wire) (hq : q≠y) : v.basis q=u.basis q := by
    rw [vu]
    simp only [writeBit,Function.update_of_ne hq]
  have vb : b.value v.basis=B := by
    rw [vu,bit_write b u.basis y (sumBit B Y C) (src y (by simp))]
    exact ub
  have vy : v.basis y=sumBit B Y C := by rw [vu]; simp only [writeBit,Function.update_self]
  have vcin : v.basis cinC=C := (vf cinC (by simp [nd,nr])).trans ucin
  have vc : v.basis c=carryBit B Y C := (vf c (by simp [nd,nr])).trans
    ((uf c (by simp [nd,nr])).trans hc)
  have wv := mappedSum_correct b y cinC (by simp [nd,nr]) (src y (by simp)) v tail
  rw [ew,vb,vy,vcin,sum_involution] at wv
  have wf (q : Wire) (hq : q≠y) : w.basis q=v.basis q := by
    rw [wv]
    simp only [writeBit,Function.update_of_ne hq]
  have wb : b.value w.basis=B := by
    rw [wv,bit_write b v.basis y Y (src y (by simp))]
    exact vb
  have wy : w.basis y=Y := by rw [wv]; simp only [writeBit,Function.update_self]
  have wcin : w.basis cinC=C := (wf cinC (by simp [nd,nr])).trans vcin
  have wc : w.basis c=carryBit B Y C := (wf c (by simp [nd,nr])).trans vc
  have tw := mappedEraseCarry_correct b y cinC c nc source w tail
    (by rw [wb,wy,wcin]; exact wc)
  rw [et] at tw
  have actual : run (releaseHead b a y cinC cinB c d) m s=t := by
    simp only [releaseHead,List.append_assoc,run_append]
    simp only [run_take]
    simp only [show measurementCount (eraseCarry a y cinB d)=1 from by unfold eraseCarry; rfl,
      show measurementCount [.X y]=0 from rfl,(mappedBit_counts b y cinC c).2.2.2.2.2,List.drop_zero]
    simp only [tail] at ev ew et
    rw [eu,ev,ew,et]
  rw [actual,tw,wv,vu,us]
  simp only [write_twice]

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.prepareHead_run
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.releaseHead_run
