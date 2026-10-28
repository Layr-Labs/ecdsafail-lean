import ECDSAAdd.Arithmetic.Paper935.HistoricalSlotTotal

namespace ECDSAAdd.Arithmetic.Paper935

private theorem zeroPorts_subset (xs ws : List Wire) :
    ∀ q∈(List.zipWith ZeroBit.mk xs ws).flatMap ZeroBit.wires,q∈xs++ws := by
  induction xs generalizing ws with
  | nil => simp
  | cons x xs ih =>
    cases ws with
    | nil => simp
    | cons w ws =>
      intro q hq
      simp only [List.zipWith_cons_cons,List.flatMap_cons,ZeroBit.wires,List.cons_append,List.nil_append,List.mem_cons] at hq
      rcases hq with rfl|rfl|hq
      · simp
      · simp
      · have hm := ih ws q hq
        simp only [List.mem_append] at hm
        rcases hm with hm|hm <;> simp [hm]

/-- Shared detector scratch may occur in several blocks; the emitted ports
still belong to the supplied flags, input chunks and one shared scratch pool. -/
theorem chunkPorts_subset (xs : List (Wire × List Wire)) (scratch : List Wire) :
    ∀ q∈BlockedZero.ports (BlockedZero.chunks xs scratch),
      q∈xs.map Prod.fst++xs.flatMap Prod.snd++scratch := by
  intro q hq
  obtain ⟨b,hb,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  rcases List.mem_cons.mp hq with rfl|hq
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hp))
  · have hm := zeroPorts_subset p.2 scratch q hq
    rcases List.mem_append.mp hm with hm|hm
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨p,hp,hm⟩))
    · exact List.mem_append_right _ hm

/-- A global separation condition for flags, input chunks and shared scratch
implies every local blocked-zero layout condition. -/
theorem chunks_valid_of_distinct (one target : Wire) (xs : List (Wire × List Wire)) (scratch : List Wire)
    (distinct : ([one,target]++xs.map Prod.fst++xs.flatMap Prod.snd++scratch).Nodup) :
    BlockedZero.Valid one target (BlockedZero.chunks xs scratch) := by
  induction xs generalizing one with
  | nil => simpa [BlockedZero.chunks,BlockedZero.Valid] using
      (show one≠target from by simp_all )
  | cons p xs ih =>
    simp only [List.map_cons,List.flatMap_cons] at distinct
    have localDistinct : ([one,p.1]++p.2++scratch).Nodup := by
      clear ih
      simp_all only [List.nodup_append',List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,List.disjoint_cons_left,List.disjoint_cons_right,List.disjoint_nil_left,List.disjoint_append_left,List.disjoint_append_right,and_true,true_and,eq_comm]
    have tailDistinct : ([p.1,target]++xs.map Prod.fst++xs.flatMap Prod.snd++scratch).Nodup := by
      clear ih
      simp_all only [List.nodup_append',List.nodup_cons,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,List.disjoint_cons_left,List.disjoint_cons_right,List.disjoint_nil_left,List.disjoint_append_left,List.disjoint_append_right,and_true,true_and,eq_comm]
    have bitsDistinct : (p.2++scratch).Nodup := (List.nodup_cons.mp (List.nodup_cons.mp localDistinct).2).2
    have bitPorts := (zeroViews_distinct p.2 scratch bitsDistinct).2
    have targetAway : target∉one::p.1::(p.2++scratch) := by
      clear ih
      simp_all only [List.nodup_append',List.nodup_cons,List.mem_append,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,List.disjoint_cons_left,List.disjoint_cons_right,List.disjoint_nil_left,List.disjoint_append_left,List.disjoint_append_right,and_true,true_and,eq_comm]
    have flagAway : p.1∉xs.map Prod.fst++xs.flatMap Prod.snd++scratch := by
      clear ih
      simp_all only [List.nodup_append',List.nodup_cons,List.mem_append,List.mem_cons,List.not_mem_nil,not_false_eq_true,not_or,List.disjoint_cons_left,List.disjoint_cons_right,List.disjoint_nil_left,List.disjoint_append_left,List.disjoint_append_right,and_true,true_and]
    change (one::p.1::(List.zipWith ZeroBit.mk p.2 scratch).flatMap ZeroBit.wires).Nodup ∧
      target∉one::p.1::(List.zipWith ZeroBit.mk p.2 scratch).flatMap ZeroBit.wires ∧
      p.1∉BlockedZero.ports (BlockedZero.chunks xs scratch) ∧
      BlockedZero.Valid p.1 target (BlockedZero.chunks xs scratch)
    refine ⟨zeroViews_prefixed_distinct [one,p.1] p.2 scratch (by simpa only [List.append_assoc] using localDistinct),?_,?_,ih p.1 tailDistinct⟩
    · intro ht
      rcases List.mem_cons.mp ht with ht|ht
      · exact targetAway (List.mem_cons.mpr (Or.inl ht))
      · rcases List.mem_cons.mp ht with ht|ht
        · exact targetAway (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl ht)))
        · exact targetAway (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (bitPorts target ht)))
    · exact fun ht => flagAway (chunkPorts_subset xs scratch p.1 ht)

end ECDSAAdd.Arithmetic.Paper935
