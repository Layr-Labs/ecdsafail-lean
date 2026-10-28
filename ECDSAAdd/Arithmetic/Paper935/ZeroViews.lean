import ECDSAAdd.Arithmetic.Paper935.HistoryCompiler

namespace ECDSAAdd.Arithmetic.Paper935

theorem zeroViews_inputs (xs ws : List Wire) (h : xs.length≤ws.length) :
    (List.zipWith ZeroBit.mk xs ws).map ZeroBit.input=xs := by
  induction xs generalizing ws with
  | nil => simp
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      simp only [List.zipWith_cons_cons,List.map_cons]
      congr 1
      exact ih ws (by simpa using h)

/-- Disjoint clean work and input registers imply uniqueness of the actual
interleaved detector wires; unequal lengths only truncate the zip. -/
theorem zeroViews_distinct (xs ws : List Wire) (h : (xs++ws).Nodup) :
    ((List.zipWith ZeroBit.mk xs ws).flatMap ZeroBit.wires).Nodup ∧
    ∀ q∈(List.zipWith ZeroBit.mk xs ws).flatMap ZeroBit.wires,q∈xs++ws := by
  induction xs generalizing ws with
  | nil => simp
  | cons x xs ih =>
    cases ws with
    | nil => simp
    | cons w ws =>
      have parts := List.nodup_append'.mp h
      have tailDistinct : (xs++ws).Nodup := List.nodup_append'.mpr
        ⟨(List.nodup_cons.mp parts.1).2,(List.nodup_cons.mp parts.2.1).2,
          List.disjoint_left.mpr (fun q hx hw => List.disjoint_left.mp parts.2.2
            (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hw))⟩
      have tail := ih ws tailDistinct
      have xaway : x∉xs++(w::ws) := by
        intro hx
        rcases List.mem_append.mp hx with hx|hx
        · exact (List.nodup_cons.mp parts.1).1 hx
        · exact List.disjoint_left.mp parts.2.2 List.mem_cons_self hx
      have waway : w∉xs++ws := by
        intro hw
        rcases List.mem_append.mp hw with hw|hw
        · exact List.disjoint_left.mp parts.2.2 (List.mem_cons_of_mem _ hw) List.mem_cons_self
        · exact (List.nodup_cons.mp parts.2.1).1 hw
      simp only [List.zipWith_cons_cons,List.flatMap_cons,ZeroBit.wires,List.cons_append,List.nil_append]
      constructor
      · apply List.nodup_cons.mpr
        constructor
        · intro hx
          rcases List.mem_cons.mp hx with hx|hx
          · exact xaway (List.mem_append_right _ (by simp [hx]))
          · have hm := List.mem_append.mp (tail.2 x hx)
            exact xaway (List.mem_append.mpr (hm.imp_right (List.mem_cons_of_mem _)))
        · exact List.nodup_cons.mpr ⟨fun hw => waway (tail.2 w hw),tail.1⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl|hq
        · exact List.mem_cons_self
        · rcases List.mem_cons.mp hq with rfl|hq
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
          · rcases List.mem_append.mp (tail.2 q hq) with hx|hw
            · exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
            · exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_cons_of_mem _ hw))


theorem zeroViews_prefixed_distinct (fixed xs ws : List Wire) (h : (fixed++(xs++ws)).Nodup) :
    (fixed++(List.zipWith ZeroBit.mk xs ws).flatMap ZeroBit.wires).Nodup := by
  have parts := List.nodup_append'.mp h
  have views := zeroViews_distinct xs ws parts.2.1
  exact List.nodup_append'.mpr ⟨parts.1,views.1,List.disjoint_left.mpr
    (fun q hq hv => List.disjoint_left.mp parts.2.2 hq (views.2 q hv))⟩

end ECDSAAdd.Arithmetic.Paper935
