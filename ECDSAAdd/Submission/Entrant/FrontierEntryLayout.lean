import ECDSAAdd.Submission.Entrant.FrontierEntryProgram

set_option maxRecDepth 8192
set_option maxHeartbeats 100000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.EntryRetained5
open Arithmetic BalancedCircuit BalancedField

theorem y_cons (L : Layout) (hw : L.Widths) : L.y=lowY L::L.y.tail := by
  cases hy : L.ylow with
  | nil => have h := hw.2.1;simp [hy] at h
  | cons a as => simp [BalancedCleanup.Layout.y,lowY,hy]

theorem r_cons (L : Layout) : L.r=L.r0::L.r.tail := rfl

theorem data_member (L : Layout) (q : Wire) (hq : q∈L.r++L.y++L.carry) : q∈L.wires := by
  simp only [Layout.wires,BalancedCleanup.Layout.wires,BalancedCleanup.Layout.r,
    BalancedCleanup.Layout.low,BalancedCleanup.Layout.y,List.mem_append,List.mem_cons,List.mem_singleton] at hq ⊢
  tauto

theorem copyND (L : Layout) (hn : L.wires.Nodup) : (L.r.tail++L.y.tail).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (allND L hn) q
  have r := (List.tail_sublist L.r).count_le q
  have y := (List.tail_sublist L.y).count_le q
  simp only [List.count_append] at h ⊢
  omega

theorem arithmeticND (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    (lowY L::(L.r++L.carry.take 255)).Nodup := by
  have hy := y_cons L hw
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp (allND L hn) q
  have c := (List.take_sublist 255 L.carry).count_le q
  rw [hy] at h
  simp only [List.count_cons,List.count_append] at h ⊢
  omega

theorem source_sites (L : Layout) (i : Nat) :
    (source L i).wires⊆[L.parity,L.lower,L.one,L.sign] := by
  intro q hq
  unfold source at hq
  split_ifs at hq <;> simp_all [Affine.Bit.wires] <;> tauto

theorem sources_sites (L : Layout) (q : Wire) (hq : q∈Affine.sites (sources L)) :
    q∈[L.parity,L.lower,L.one,L.sign] := by
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
  exact source_sites L i hq

theorem sources_valid (L : Layout) (hn : L.wires.Nodup) :
    ∀b∈sources L,b.Valid := by
  have nd : [L.parity,L.lower,L.one,L.sign].Nodup := by
    apply List.nodup_iff_count.mpr
    intro q
    have h := List.nodup_iff_count.mp (scalarND L hn) q
    simp only [List.count_cons,List.count_nil] at h ⊢
    omega
  simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or,List.nodup_nil,and_true] at nd
  rcases nd with ⟨⟨n01,n02,n03⟩,⟨n12,n13⟩,n23⟩
  have n10 := Ne.symm n01
  have n21 := Ne.symm n12
  intro b hb
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hb
  unfold source
  split_ifs <;> simp_all [Affine.Bit.Valid]

theorem sources_away (L : Layout) (hw : L.Widths) (hn : L.wires.Nodup) :
    ∀q∈Affine.sites (sources L),q∉lowY L::(L.r++L.carry.take 255) := by
  intro q hq bad
  have member := sources_sites L q hq
  have f := flagAway L hn q (by simp only [List.mem_cons,List.mem_singleton] at member ⊢;tauto)
  have y0 : lowY L∈L.y := by rw [y_cons L hw];simp
  have h : q∈L.r++L.y++L.carry := by
    simp only [List.mem_cons,List.mem_append] at bad ⊢
    rcases bad with rfl|hr|hc
    · simp [y0]
    · simp [hr]
    · simp [List.mem_of_mem_take hc]
  exact f h

end ECDSAAdd.Entrant.EntryRetained5
