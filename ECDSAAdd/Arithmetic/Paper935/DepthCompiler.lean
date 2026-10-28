import ECDSAAdd.Arithmetic.Paper935.DepthArenaReady

namespace ECDSAAdd.Arithmetic.Paper935

def depthStaticCheck (L : DepthLayout) : Prop :=
  ((L.flag::L.pos::L.one::L.zz::L.zb.flatMap ZeroBit.wires).Nodup) ∧
  ((L.one::L.flag::(L.frozen::L.positive::L.low).flatMap ZeroBit.wires).Nodup) ∧
  (L.sign∈L.zb.map ZeroBit.input) ∧
  (L.positive.input=L.pos) ∧
  (L.frozen.input≠L.pos) ∧
  (∀ b∈L.low,b.input≠L.pos) ∧
  (∀ b∈L.frozen::L.positive::L.low,b.work≠L.pos) ∧
  ((L.flag::L.output::L.address::((L.fdata++L.qbits)++L.scratch++[L.tmp])).Nodup) ∧
  (L.fdata.length=4) ∧
  (L.qbits.length=5) ∧
  (L.scratch.length=9) ∧
  (L.flag∉[L.one,L.zz,L.pos,L.sign]++L.zb.flatMap ZeroBit.wires++(L.frozen::L.positive::L.low).flatMap ZeroBit.wires) ∧
  (L.output∉[L.one,L.zz,L.pos,L.sign]++L.zb.flatMap ZeroBit.wires++(L.frozen::L.positive::L.low).flatMap ZeroBit.wires) ∧
  (L.zb.map ZeroBit.input=L.zlo++[L.sign]) ∧
  (L.vtail≠[]) ∧
  (2≤L.low.length) ∧
  (L.low.length≤6) ∧
  (L.slice.length=L.low.length) ∧
  (L.ftail≠[]) ∧
  (L.qtail≠[]) ∧
  (L.vlow::(L.low.map ZeroBit.input++L.vtail)=L.slice++(L.qlow::(L.qbits++L.qtail))) ∧
  (L.output∉L.readWires)

theorem depthStaticCheck_iff (L : DepthLayout) : depthStaticCheck L ↔ L.Static := by
  constructor
  · rintro ⟨hnz,hnf,hsg,hpos,hfr,hlow,hworkpos,hnlookup,hflen,hqlen,hs,hflag,hout,hzview,hvtail,hmin,hmax,hslen,hftail,hqtail,hcoeffview,outputAway⟩
    exact ⟨hnz,hnf,hsg,hpos,hfr,hlow,hworkpos,hnlookup,hflen,hqlen,hs,hflag,hout,hzview,hvtail,hmin,hmax,hslen,hftail,hqtail,hcoeffview,outputAway⟩
  · intro h
    exact ⟨h.hnz,h.hnf,h.hsg,h.hpos,h.hfr,h.hlow,h.hworkpos,h.hnlookup,h.hflen,h.hqlen,h.hs,h.hflag,h.hout,h.hzview,h.hvtail,h.hmin,h.hmax,h.hslen,h.hftail,h.hqtail,h.hcoeffview,h.outputAway⟩

instance (L : DepthLayout) : Decidable (L.Static) :=
  have : Decidable (depthStaticCheck L) := by unfold depthStaticCheck; infer_instance
  decidable_of_iff (depthStaticCheck L) (depthStaticCheck_iff L)


/-- Eleven physical scratch addresses are shared between predicate work and
lookup work. These stages execute sequentially and return the shared bits
clean. In particular this does not reserve their sizes additively. -/
def depthLayoutCandidate (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) : DepthLayout where
  one := one
  zz := work.getD 2 0
  pos := work.getD 1 0
  sign := z.getLastD 0
  flag := work.getD 0 0
  address := f.getD 1 0
  tmp := work.getD 10 0
  output := output
  zb := List.zipWith ZeroBit.mk z (work.drop 3)
  frozen := ⟨frozen,work.getD 2 0⟩
  positive := ⟨work.getD 1 0,work.getD 3 0⟩
  low := List.zipWith ZeroBit.mk ((v.drop 1).take depth) (work.drop 4)
  fdata := (f.drop 2).take 4
  qbits := (v.drop (depth+1)).take 5
  scratch := (work.drop 1).take 9
  flow := f.getD 0 0
  vlow := v.getD 0 0
  qlow := v.getD depth 0
  zlo := z.dropLast
  vtail := v.drop (depth+1)
  ftail := f.drop 6
  slice := v.take depth
  qtail := v.drop (depth+6)

/-- This compiler checks all alias and physical view obligations. A failed
check is explicit; default list accesses cannot authorize fictitious wires. -/
def compileDepth (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) : Option DepthLayout :=
  let L := depthLayoutCandidate one frozen output z f v work depth
  if L.Static ∧ work.length=11 ∧ L.zb.map ZeroBit.input=z ∧
    L.flow::((L.address::L.fdata)++L.ftail)=f ∧
    L.vlow::(L.low.map ZeroBit.input++L.vtail)=v ∧ L.low.length=depth then some L else none

theorem compileDepth_contract (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) (L : DepthLayout) (h : compileDepth one frozen output z f v work depth=some L) :
    L.Static ∧ work.length=11 ∧ L.zb.map ZeroBit.input=z ∧
    L.flow::((L.address::L.fdata)++L.ftail)=f ∧
    L.vlow::(L.low.map ZeroBit.input++L.vtail)=v ∧ L.low.length=depth := by
  unfold compileDepth at h
  dsimp only at h
  split at h
  next valid => cases h; exact valid
  next invalid => simp at h

private theorem getD_member (xs : List Wire) (i : Nat) (h : i<xs.length) : xs.getD i 0∈xs := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
  exact List.getElem_mem h

private theorem zeroBit_work_member (xs ws : List Wire) (b : ZeroBit)
    (h : b∈List.zipWith ZeroBit.mk xs ws) : b.work∈ws := by
  induction xs generalizing ws with
  | nil => simp at h
  | cons x xs ih =>
    cases ws with
    | nil => simp at h
    | cons w ws =>
      simp only [List.zipWith_cons_cons,List.mem_cons] at h
      rcases h with rfl|h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ws h)

/-- All predicate and lookup scratch comes from the same eleven addresses. -/
theorem depthLayoutCandidate_clean_subset (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) (len : work.length=11) :
    (depthLayoutCandidate one frozen output z f v work depth).cleanWires.toFinset⊆work.toFinset := by
  intro q hq
  have bitAt (i : Nat) (hi : i<11) : work.getD i 0∈work := getD_member work i (by omega)
  simp only [List.mem_toFinset,DepthLayout.cleanWires,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq
  change q∈work.toFinset
  apply List.mem_toFinset.mpr
  rcases hq with ((hq|hq)|hq)|hq
  · rcases hq with rfl|rfl|rfl|rfl
    · exact bitAt 2 (by decide)
    · exact bitAt 1 (by decide)
    · exact bitAt 0 (by decide)
    · exact bitAt 10 (by decide)
  · obtain ⟨bit,hb,rfl⟩ := List.mem_map.mp hq
    exact List.mem_of_mem_drop (zeroBit_work_member z (work.drop 3) bit hb)
  · obtain ⟨bit,hb,rfl⟩ := List.mem_map.mp hq
    simp only [List.mem_cons] at hb
    rcases hb with rfl|rfl|hb
    · exact bitAt 2 (by decide)
    · exact bitAt 3 (by decide)
    · exact List.mem_of_mem_drop (zeroBit_work_member ((v.drop 1).take depth) (work.drop 4) bit hb)
  · exact List.mem_of_mem_drop (List.mem_of_mem_take hq)

theorem compileDepth_clean_subset (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) (L : DepthLayout) (h : compileDepth one frozen output z f v work depth=some L) :
    L.cleanWires.toFinset⊆work.toFinset := by
  have contract := compileDepth_contract one frozen output z f v work depth L h
  unfold compileDepth at h
  dsimp only at h
  split at h
  next valid => cases h; exact depthLayoutCandidate_clean_subset one frozen output z f v work depth contract.2.1
  next invalid => simp at h

theorem compileDepth_work_bound (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) (L : DepthLayout) (h : compileDepth one frozen output z f v work depth=some L) :
    L.cleanWires.toFinset.card≤11 := by
  have sub := compileDepth_clean_subset one frozen output z f v work depth L h
  have len := (compileDepth_contract one frozen output z f v work depth L h).2.1
  exact le_trans (Finset.card_le_card sub) (by simpa only [len] using List.toFinset_card_le work)

theorem compileDepth_identity (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) (L : DepthLayout) (h : compileDepth one frozen output z f v work depth=some L) :
    L.one=one ∧ L.frozen.input=frozen ∧ L.output=output := by
  unfold compileDepth at h
  dsimp only at h
  split at h
  next valid => cases h; exact ⟨rfl,rfl,rfl⟩
  next invalid => simp at h

end ECDSAAdd.Arithmetic.Paper935
