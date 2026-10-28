import ECDSAAdd.Arithmetic.BalancedCleanupOffsetHead
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset

def decision : List Bool → List Bool → List Bool → Bool → Bool → Bool
  | b::bs,a::as,y::ys,cinC,cinB =>
      decision bs as ys (carryBit b y cinC) (carryBit a (!(sumBit b y cinC)) cinB)
  | [],[],[],_,cinB => !cinB
  | _,_,_,_,_ => false

theorem mapped_member (b : MappedBit) (bits : List MappedBit) (w : Wire) (hw : w∈b.wire) :
    w∈mappedWires (b::bits) := by
  cases hb : b.wire with
  | none => simp [hb] at hw
  | some a =>
    have e : a=w := by simpa [hb] using hw
    subst w
    simp [mappedWires,hb]

theorem mapped_tail_member (b : MappedBit) (bits : List MappedBit) (w : Wire)
    (hw : w∈mappedWires bits) : w∈mappedWires (b::bits) := by
  change w ∈ b.wire.toList ++ mappedWires bits
  exact List.mem_append.mpr (Or.inr hw)

theorem head_tail_nd (target cinC cinB a y c d : Wire) (as ys cs ds : List Wire)
    (hn : (target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds))).Nodup) :
    ([a,y,cinC,cinB,c,d,target]++(as++ys++cs++ds)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem head_six_nd (a y cinC cinB c d target : Wire)
    (hn : [a,y,cinC,cinB,c,d,target].Nodup) : [a,y,cinC,cinB,c,d].Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_nil] at h ⊢
  omega

theorem recursive_nd (target cinC cinB a y c d : Wire) (as ys cs ds : List Wire)
    (hn : (target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds))).Nodup) :
    (target::c::d::(as++ys++cs++ds)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem head_mem_scope (target cinC cinB a y c d q : Wire) (as ys cs ds : List Wire)
    (hq : q∈[a,y,cinC,cinB,c,d,target]) :
    q∈target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds)) := by
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  tauto

theorem tail_mem_scope (target cinC cinB a y c d q : Wire) (as ys cs ds : List Wire)
    (hq : q∈target::c::d::(as++ys++cs++ds)) :
    q∈target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds)) := by
  simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hq ⊢
  tauto

theorem tail_away_head (target cinC cinB a y c d q h : Wire) (as ys cs ds : List Wire)
    (hn : (target::cinC::cinB::((a::as)++(y::ys)++(c::cs)++(d::ds))).Nodup)
    (hq : q∈as++ys++cs++ds) (hh : h∈[a,y,cinC,cinB,c,d,target]) : q≠h := by
  have dis := (List.nodup_append'.mp (head_tail_nd target cinC cinB a y c d as ys cs ds hn)).2.2
  exact fun e => List.disjoint_left.mp dis hh (e ▸ hq)

theorem chain_cons (b : MappedBit) (bits : List MappedBit) (a y c d cinC cinB target : Wire)
    (as ys cs ds : List Wire) :
    chain (b::bits) (a::as) (y::ys) (c::cs) (d::ds) cinC cinB target=
      prepareHead b a y cinC cinB c d++
        (chain bits as ys cs ds c d target++releaseHead b a y cinC cinB c d) := by
  simp only [chain,prepareHead,releaseHead,List.append_assoc]

theorem prepareHead_measurements (b : MappedBit) (a y cinC cinB c d : Wire) :
    measurementCount (prepareHead b a y cinC cinB c d)=0 := by
  simp only [prepareHead,measurementCount_append,(mappedBit_counts b y cinC c).2.1,
    (mappedBit_counts b y cinC c).2.2.2.2.2]
  rfl

end ECDSAAdd.Arithmetic.BalancedCleanupOffset
