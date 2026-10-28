import ECDSAAdd.Arithmetic.TerminalParityMeasure
import ECDSAAdd.Arithmetic.BalancedCleanupOffsetSlimLeafProof
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace ECDSAAdd.Arithmetic.TerminalParityMeasure
open BalancedCleanupOffset
attribute [local irreducible] run mappedSum majority eraseCarry

def leaf (b : MappedBit) (a y cinC cinB d target : Wire) : Program :=
  mappedSum b y cinC++[.X y]++program a y cinB target++
    [.X y]++mappedSum b y cinC

private theorem zero_records (P : Program) (h : measurementCount P=0)
    (s : State) (m n : List Bool) : run P m s=run P n s := by
  have x := run_take P m s
  have z := run_take P n s
  rw [h,List.take_zero] at x z
  exact x.symm.trans z
private theorem run_zero (P Q : Program) (h : measurementCount P=0) (s : State) (m : List Bool) :
    run (P++Q) m s=run Q m (run P m s) := by
  rw [run_append,h,List.take_zero,List.drop_zero,zero_records P h s [] m]
private theorem threshold (a b c : Bool) :
    decide (2 ≤ (if a then 1 else 0)+(if b then 1 else 0)+c.toNat)=carryBit a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem leaf_correct (b : MappedBit) (a y cinC cinB c d target : Wire)
    (hn : [a,y,cinC,cinB,c,d,target].Nodup)
    (ha : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d,target])
    (s : State) (m : List Bool) (hd : s.basis d=false)
    (ht : s.basis target= !(carryBit (s.basis a)
      (!(sumBit (b.value s.basis) (s.basis y) (s.basis cinC))) (s.basis cinB))) :
    run (leaf b a y cinC cinB d target) m s=
      ⟨s.phase,writeBit s.basis target false⟩ := by
  have nd := hn
  have nr := List.nodup_reverse.mpr hn
  simp only [List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append,
    List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    not_or,not_false_eq_true,and_true] at nd nr
  have src (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d,target]) : ∀w∈b.wire,w≠q :=
    fun w hw e => ha w hw (e.symm ▸ hq)
  have sm : measurementCount (mappedSum b y cinC)=0 := (mappedBit_counts b y cinC c).2.2.2.2.2
  have xm : measurementCount [.X y]=0 := rfl
  have pm : measurementCount (mappedSum b y cinC++[.X y])=0 := by
    rw [measurementCount_append,sm,xm]
  have cm : measurementCount (program a y cinB target)=1 := (counts a y cinB target).2
  let B := b.value s.basis
  let Y := s.basis y
  let C := s.basis cinC
  let S := sumBit B Y C
  let u := run (mappedSum b y cinC++[.X y]) m s
  have pu : u=⟨s.phase,writeBit s.basis y (!S)⟩ := by
    dsimp only [u]
    rw [run_zero _ _ sm,mappedSum_correct b y cinC (by simp [nd,nr]) (src y (by simp)),x_run]
    apply State.extensionality
    · rfl
    · funext q
      by_cases eq : q=y <;> simp [writeBit,Function.update,eq,S,B,Y,C]
  let v := run (program a y cinB target) m u
  have uf (q : Wire) (hq : q≠y) : u.basis q=s.basis q := by
    rw [pu]
    simp [writeBit,hq]
  have uy : u.basis y= !S := by rw [pu]; simp [writeBit]
  have input : u.basis target= !(carryBit (u.basis a) (u.basis y) (u.basis cinB)) := by
    rw [uf target (by simp [nd,nr]),uf a (by simp [nd,nr]),uy,
      uf cinB (by simp [nd,nr])]
    exact ht
  have actualMeasure := correct a y cinB target (by simp [nd,nr])
    (by simp [nd,nr]) (by simp [nd,nr]) u m input
  change v=⟨u.phase,writeBit u.basis target false⟩ at actualMeasure
  have comp : v.phase=u.phase ∧ (∀q,q≠target → v.basis q=u.basis q) ∧
      v.basis target=false := by
    rw [actualMeasure]
    exact ⟨rfl,fun q hq => by simp [writeBit,hq],by simp [writeBit]⟩
  have value : v.basis target=false := comp.2.2
  have vy : v.basis y= !S := (comp.2.1 y (by simp [nd,nr])).trans uy
  have vc : v.basis cinC=C := (comp.2.1 cinC (by simp [nd,nr])).trans (uf cinC (by simp [nd,nr]))
  have vb : b.value v.basis=B := by
    apply mappedBit_value_congr
    intro w hw
    exact (comp.2.1 w (src target (by simp) w hw)).trans (uf w (src y (by simp) w hw))
  have done : run (mappedSum b y cinC) (m.drop 1) (run [.X y] (m.drop 1) v)=
      ⟨v.phase,writeBit v.basis y Y⟩ := by
    rw [x_run,mappedSum_correct b y cinC (by simp [nd,nr]) (src y (by simp))]
    have source := (bit_write b v.basis y (!v.basis y) (src y (by simp))).trans vb
    have restored : sumBit (b.value (writeBit v.basis y (!v.basis y)))
        (!v.basis y) (v.basis cinC)=Y := by
      rw [source,vy,Bool.not_not,vc]
      exact sum_involution B Y C
    apply State.extensionality
    · rfl
    · funext q
      by_cases eq : q=y
      · rw [eq]
        simp only [writeBit,Function.update_self,
          Function.update_of_ne (show cinC≠y by simp [nd,nr])]
        exact restored
      · simp [writeBit,Function.update,eq]
  have shape : leaf b a y cinC cinB d target=(mappedSum b y cinC++[.X y])++
      (program a y cinB target++([.X y]++mappedSum b y cinC)) := by
    simp only [leaf,List.append_assoc]
  have actual : run (leaf b a y cinC cinB d target) m s=
      run (mappedSum b y cinC) (m.drop 1) (run [.X y] (m.drop 1) v) := by
    rw [shape,run_zero _ _ pm,run_append]
    have take := run_take (program a y cinB target) m u
    rw [cm] at take
    rw [cm,take,run_zero _ _ xm]
  rw [actual,done]
  apply State.extensionality
  · exact comp.1.trans (by rw [pu])
  · funext q
    by_cases qt : q=target
    · subst q
      simp [writeBit,show target≠y by simp [nd,nr],value,B,Y,C,S]
    · by_cases qy : q=y
      · subst q
        simp [writeBit,show y≠target by simp [nd,nr],Y]
      · simp [writeBit,qy,qt,comp.2.1 q qt,uf q qy]

theorem leaf_counts (b : MappedBit) (a y cinC cinB d target : Wire) :
    toffoliCount (leaf b a y cinC cinB d target)=0 ∧
    measurementCount (leaf b a y cinC cinB d target)=1 := by
  have c := mappedBit_counts b y cinC d
  have p := counts a y cinB target
  simp only [leaf,toffoliCount_append,measurementCount_append,
    c.2.2.2.2.1,c.2.2.2.2.2,p.1,p.2]
  norm_num [toffoliCount,measurementCount]

end ECDSAAdd.Arithmetic.TerminalParityMeasure
#print axioms ECDSAAdd.Arithmetic.TerminalParityMeasure.leaf_correct

#print axioms ECDSAAdd.Arithmetic.TerminalParityMeasure.leaf_counts
