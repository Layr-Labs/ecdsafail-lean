import ECDSAAdd.Arithmetic.PointFlagLayout
import ECDSAAdd.Arithmetic.PointClassification

namespace ECDSAAdd.Arithmetic

theorem equalPorts_correct (c t : Wire) (src work : List Wire) (k : Nat)
    (hl : src.length=work.length) (hn : (c::t::src++work).Nodup)
    (hk : k<2^src.length) (s : State) (m : List Bool) (hz : regValue work s.basis=0) :
    run (equalConstant c t (zeroPorts src work) k) m s=
      ⟨s.phase,writeBit s.basis t (s.basis t ^^ (s.basis c && decide (regValue src s.basis=k)))⟩ := by
  obtain ⟨hx,hw⟩ := zeroPorts_maps src work hl
  have hlen : (zeroPorts src work).length=src.length := by
    simpa using congrArg List.length hx
  have hnd : (c::t::(zeroPorts src work).flatMap ZeroBit.wires).Nodup :=
    ((zeroPorts_perm src work hl).cons t |>.cons c).nodup_iff.mpr hn
  have hz' : ∀ b∈zeroPorts src work,s.basis b.work=false := by
    intro b hb
    apply (regValue_zero _ _).mp hz
    rw [← hw]
    exact List.mem_map.mpr ⟨b,hb,rfl⟩
  simpa only [hx] using equalConstant_correct c t (zeroPorts src work) k hnd (hlen ▸ hk) s m hz'

/-- 四个标志与输入、输出、工作池等其余线路互异。 -/
theorem PointAddLayout.flags_disjoint (L : PointAddLayout) (hn : L.wires.Nodup) :
    L.flags.Nodup ∧ L.flags.Disjoint
      (L.input.finite::L.input.x++L.input.y++PointAddLayout.pointWires L.output++
        L.words.flatten++L.divisor++L.inverse++[L.inputXHigh,L.inputYHigh]++L.pool) := by
  have h : (L.flags++(L.input.finite::L.input.x++L.input.y++PointAddLayout.pointWires L.output++
        L.words.flatten++L.divisor++L.inverse++[L.inputXHigh,L.inputYHigh]++L.pool)).Nodup := by
    apply List.nodup_iff_count.mpr; intro w
    have hh := List.nodup_iff_count.mp hn w
    simpa [PointAddLayout.wires,PointAddLayout.work,PointAddLayout.pointWires,
      List.count_append,List.count_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
  exact ⟨(List.nodup_append'.mp h).1,(List.nodup_append'.mp h).2.2⟩

private theorem flag_not_input_pool (L : PointAddLayout) (hn : L.wires.Nodup) (w : Wire)
    (hw : w∈L.flags) : w≠L.input.finite ∧ w∉L.input.x ∧ w∉L.input.y ∧ w∉L.pool := by
  have hd := List.disjoint_left.mp (L.flags_disjoint hn).2 hw
  simp only [List.mem_cons,List.mem_append,not_or] at hd
  tauto

private theorem regValue_write_away (r : List Wire) (s : BasisState) (w : Wire) (v : Bool)
    (hw : w∉r) : regValue r (writeBit s w v)=regValue r s := by
  apply regValue_congr; intro a ha
  simp [writeBit,show a≠w from fun he => hw (he ▸ ha)]

def pointFlagState (L : PointAddLayout) (s : BasisState) (ex ey g d : Bool) : BasisState :=
  writeBit (writeBit (writeBit (writeBit s L.equalX ex) L.equalNegY ey) L.generic g) L.double d

/-- 检测链在每次调用后清零，四个分支标志之外每一根线都保持。 -/
theorem pointFlagsCompute_correct (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (s : State) (m : List Bool) (hz : regValue L.pool s.basis=0)
    (hf : ∀ w∈L.flags,s.basis w=false) :
    let ex := s.basis L.input.finite && decide (regValue L.input.x s.basis=cx.val)
    let ey := s.basis L.input.finite && decide (regValue L.input.y s.basis=(-cy).val)
    run (pointFlagsCompute L cx cy) m s=
      ⟨s.phase,pointFlagState L s.basis ex ey (s.basis L.input.finite && !ex) (ex && !ey)⟩ := by
  dsimp only
  obtain ⟨nx,ny,nb⟩ := L.flag_interfaces hn
  have hxlen : L.input.x.length=(L.pool.take 256).length := by simp [h.inputX,h.pool]
  have hylen : L.input.y.length=(L.pool.take 256).length := by simp [h.inputY,h.pool]
  have hp : regValue (L.pool.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp hz w (List.mem_of_mem_take hw))
  have hcx : cx.val<2^L.input.x.length := by rw [h.inputX]; exact lt_trans (ZMod.val_lt cx) (by norm_num [p])
  have hcy : (-cy).val<2^L.input.y.length := by rw [h.inputY]; exact lt_trans (ZMod.val_lt (-cy)) (by norm_num [p])
  have hex := flag_not_input_pool L hn L.equalX (by simp [PointAddLayout.flags])
  have hey := flag_not_input_pool L hn L.equalNegY (by simp [PointAddLayout.flags])
  have hxy : L.equalNegY≠L.equalX := by
    have hh := (L.flags_disjoint hn).1
    simp only [PointAddLayout.flags,List.nodup_cons,List.mem_cons,List.not_mem_nil,
      or_false,not_or] at hh
    exact Ne.symm hh.1.1
  have hfx := hf L.equalX (by simp [PointAddLayout.flags])
  have hfy := hf L.equalNegY (by simp [PointAddLayout.flags])
  have hfg := hf L.generic (by simp [PointAddLayout.flags])
  have hfd := hf L.double (by simp [PointAddLayout.flags])
  let ex := s.basis L.input.finite && decide (regValue L.input.x s.basis=cx.val)
  let ey := s.basis L.input.finite && decide (regValue L.input.y s.basis=(-cy).val)
  let u : State := ⟨s.phase,writeBit s.basis L.equalX ex⟩
  have hu (m : List Bool) : run (equalConstant L.input.finite L.equalX L.zeroX cx.val) m s=u := by
    simpa only [hfx,Bool.false_xor] using equalPorts_correct L.input.finite L.equalX L.input.x (L.pool.take 256) cx.val hxlen nx hcx s m hp
  have hup : regValue (L.pool.take 256) u.basis=0 := by
    rw [show u.basis=writeBit s.basis L.equalX ex from rfl,
      regValue_write_away _ _ _ _ (fun hm => hex.2.2.2 (List.mem_of_mem_take hm))]
    exact hp
  let v : State := ⟨s.phase,writeBit u.basis L.equalNegY ey⟩
  have hv (m : List Bool) : run (equalConstant L.input.finite L.equalNegY L.zeroY (-cy).val) m u=v := by
    have hy := equalPorts_correct L.input.finite L.equalNegY L.input.y (L.pool.take 256) (-cy).val hylen ny hcy u m hup
    have huy : regValue L.input.y u.basis=regValue L.input.y s.basis := regValue_write_away _ _ _ _ hex.2.2.1
    rw [huy] at hy
    simpa [u,v,ey,writeBit,hxy,hfy,Ne.symm hex.1] using hy
  have hb (m : List Bool) := pointBranchFlags_correct _ _ _ _ _ nb v m
  have hnb := nb
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,not_false_eq_true,and_true] at hnb
  have hgex : L.generic≠L.equalX ∧ L.generic≠L.equalNegY :=
    ⟨Ne.symm hnb.2.1.2.1,Ne.symm hnb.2.2.1.1⟩
  have hdex : L.double≠L.equalX ∧ L.double≠L.equalNegY :=
    ⟨Ne.symm hnb.2.1.2.2,Ne.symm hnb.2.2.1.2⟩
  rw [pointFlagsCompute,run_append,run_take,run_append,run_take]
  simp only [measurementCount_append,(equalConstant_counts _ _ _ _).2]
  rw [hu,hv,hb]
  simp [pointFlagState,u,v,ex,ey,writeBit,Ne.symm hxy,hfg,hfd,hgex.1,hgex.2,
    hdex.1,hdex.2,Ne.symm hex.1,Ne.symm hey.1]


theorem equalPorts_cancel (c t : Wire) (src work : List Wire) (k : Nat)
    (hl : src.length=work.length) (hn : (c::t::src++work).Nodup)
    (hk : k<2^src.length) (s : State) (m : List Bool) (hz : regValue work s.basis=0) :
    run (equalConstant c t (zeroPorts src work) k) m
      (run (equalConstant c t (zeroPorts src work) k) m s)=s := by
  have hct : c≠t := by exact fun he => (List.nodup_cons.mp hn).1 (by simp [he])
  have ht := (List.nodup_cons.mp (List.nodup_cons.mp hn).2).1
  have hts : t∉src := fun hm => ht (List.mem_append_left _ hm)
  have htw : t∉work := fun hm => ht (List.mem_append_right _ hm)
  rw [equalPorts_correct c t src work k hl hn hk s m hz]
  have hz' : regValue work (writeBit s.basis t
      (s.basis t ^^ (s.basis c && decide (regValue src s.basis=k))))=0 := by
    rw [regValue_write_away _ _ _ _ htw]; exact hz
  rw [equalPorts_correct c t src work k hl hn hk _ m hz']
  rw [regValue_write_away _ _ _ _ hts]
  simp [writeBit,hct,Function.update_idem]

theorem pointBranchFlags_cancel (f ex ey g d : Wire) (hn : [f,ex,ey,g,d].Nodup)
    (s : State) (m : List Bool) :
    run (pointBranchFlags f ex ey g d) m (run (pointBranchFlags f ex ey g d) m s)=s := by
  rw [pointBranchFlags_correct _ _ _ _ _ hn,pointBranchFlags_correct _ _ _ _ _ hn]
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,not_false_eq_true,and_true] at hn
  rcases hn with ⟨⟨hfe,hfy,hfg,hfd⟩,⟨hey,heg,hed⟩,⟨hyg,hyd⟩,hgd⟩
  apply congrArg (State.mk s.phase)
  funext w
  by_cases hwg : w=g
  · subst w; simp [writeBit, *]
  · by_cases hwd : w=d
    · subst w; simp [writeBit, *]
    · simp [writeBit, *]

/-- 清理按模块逆序重算零检测，未倒放其测量工作链。 -/
theorem pointFlags_roundtrip (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (s : State) (m : List Bool) (hz : regValue L.pool s.basis=0) :
    run (pointFlagsClear L cx cy) m (run (pointFlagsCompute L cx cy) m s)=s := by
  obtain ⟨nx,ny,nb⟩ := L.flag_interfaces hn
  have hxlen : L.input.x.length=(L.pool.take 256).length := by simp [h.inputX,h.pool]
  have hylen : L.input.y.length=(L.pool.take 256).length := by simp [h.inputY,h.pool]
  have hp : regValue (L.pool.take 256) s.basis=0 :=
    (regValue_zero _ _).mpr (fun w hw => (regValue_zero _ _).mp hz w (List.mem_of_mem_take hw))
  have hcx : cx.val<2^L.input.x.length := by rw [h.inputX]; exact lt_trans (ZMod.val_lt cx) (by norm_num [p])
  have hcy : (-cy).val<2^L.input.y.length := by rw [h.inputY]; exact lt_trans (ZMod.val_lt (-cy)) (by norm_num [p])
  let u := run (equalConstant L.input.finite L.equalX (zeroPorts L.input.x (L.pool.take 256)) cx.val) m s
  have hup : regValue (L.pool.take 256) u.basis=0 := by
    dsimp [u,PointAddLayout.zeroX]
    rw [equalPorts_correct _ _ _ _ _ hxlen nx hcx s m hp]
    have hex := flag_not_input_pool L hn L.equalX (by simp [PointAddLayout.flags])
    rw [regValue_write_away _ _ _ _ (fun hm => hex.2.2.2 (List.mem_of_mem_take hm))]
    exact hp
  have heq (c t : Wire) (src work : List Wire) (k : Nat)
      (hl : src.length=work.length) (nd : (c::t::src++work).Nodup)
      (hk : k<2^src.length) (st : State) (m' : List Bool)
      (hz' : regValue work st.basis=0) :
      run (equalConstant c t (zeroPorts src work) k) m' st =
        run (equalConstant c t (zeroPorts src work) k) m st := by
    rw [equalPorts_correct _ _ _ _ _ hl nd hk st m' hz',
      equalPorts_correct _ _ _ _ _ hl nd hk st m hz']
  have hb (st : State) (m' : List Bool) :
      run (pointBranchFlags L.input.finite L.equalX L.equalNegY L.generic L.double) m' st =
        run (pointBranchFlags L.input.finite L.equalX L.equalNegY L.generic L.double) m st := by
    rw [pointBranchFlags_correct _ _ _ _ _ nb,pointBranchFlags_correct _ _ _ _ _ nb]
  simp only [pointFlagsClear,pointFlagsCompute,run_append,run_take]
  simp only [PointAddLayout.zeroX,PointAddLayout.zeroY]
  rw [heq _ _ _ _ _ hxlen nx hcx s m hp]
  change run (equalConstant L.input.finite L.equalX L.zeroX cx.val) _
    (run (equalConstant L.input.finite L.equalNegY L.zeroY (-cy).val) _
      (run (pointBranchFlags L.input.finite L.equalX L.equalNegY L.generic L.double) _
        (run (pointBranchFlags L.input.finite L.equalX L.equalNegY L.generic L.double) _
          (run (equalConstant L.input.finite L.equalNegY L.zeroY (-cy).val) _ u))))=s
  simp only [hb]
  rw [pointBranchFlags_cancel _ _ _ _ _ nb]
  simp only [PointAddLayout.zeroX,PointAddLayout.zeroY]
  rw [heq _ _ _ _ _ hylen ny hcy u _ hup]
  have hvp : regValue (L.pool.take 256)
      (run (equalConstant L.input.finite L.equalNegY L.zeroY (-cy).val) m u).basis=0 := by
    simp only [PointAddLayout.zeroY]
    rw [equalPorts_correct _ _ _ _ _ hylen ny hcy u m hup]
    have hey := flag_not_input_pool L hn L.equalNegY (by simp [PointAddLayout.flags])
    rw [regValue_write_away _ _ _ _ (fun hm => hey.2.2.2 (List.mem_of_mem_take hm))]
    exact hup
  simp only [PointAddLayout.zeroY] at hvp
  rw [heq _ _ _ _ _ hylen ny hcy _ _ hvp,
    equalPorts_cancel _ _ _ _ _ hylen ny hcy u m hup,
    heq _ _ _ _ _ hxlen nx hcx u _ hup]
  exact equalPorts_cancel _ _ _ _ _ hxlen nx hcx s m hp



theorem pointFlagState_outside (L : PointAddLayout) (s : BasisState) (ex ey g d : Bool)
    (w : Wire) (hw : w∉L.flags) : pointFlagState L s ex ey g d w=s w := by
  simp only [PointAddLayout.flags,List.mem_cons,List.not_mem_nil,or_false,not_or] at hw
  simp [pointFlagState,writeBit,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2]

theorem pointFlagState_flags (L : PointAddLayout) (hn : L.flags.Nodup)
    (s : BasisState) (ex ey g d : Bool) :
    pointFlagState L s ex ey g d L.equalX=ex ∧
    pointFlagState L s ex ey g d L.equalNegY=ey ∧
    pointFlagState L s ex ey g d L.generic=g ∧
    pointFlagState L s ex ey g d L.double=d := by
  simp only [PointAddLayout.flags,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,not_false_eq_true,and_true] at hn
  rcases hn with ⟨⟨hxy,hxg,hxd⟩,⟨hyg,hyd⟩,hgd⟩
  simp [pointFlagState,writeBit, *]

theorem pointFlagsClear_correct (L : PointAddLayout) (h : L.Widths) (hn : L.wires.Nodup)
    (cx cy : Fp) (s : State) (m : List Bool) (hz : regValue L.pool s.basis=0)
    (hex : s.basis L.equalX=(s.basis L.input.finite && decide (regValue L.input.x s.basis=cx.val)))
    (hey : s.basis L.equalNegY=(s.basis L.input.finite && decide (regValue L.input.y s.basis=(-cy).val)))
    (hg : s.basis L.generic=(s.basis L.input.finite && !s.basis L.equalX))
    (hd : s.basis L.double=(s.basis L.equalX && !s.basis L.equalNegY)) :
    run (pointFlagsClear L cx cy) m s=
      ⟨s.phase,pointFlagState L s.basis false false false false⟩ := by
  let b : State := ⟨s.phase,pointFlagState L s.basis false false false false⟩
  have hfn := (L.flags_disjoint hn).1
  have hb := pointFlagState_flags L hfn s.basis false false false false
  have hbz : ∀ w∈L.flags,b.basis w=false := by
    intro w hw
    simp only [PointAddLayout.flags,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl <;> tauto
  have hbf : b.basis L.input.finite=s.basis L.input.finite :=
    pointFlagState_outside L _ _ _ _ _ _ (fun hw => (flag_not_input_pool L hn _ hw).1 rfl)
  have hbx : regValue L.input.x b.basis=regValue L.input.x s.basis := by
    apply regValue_congr; intro w hw
    exact pointFlagState_outside L _ _ _ _ _ _ (fun hf => (flag_not_input_pool L hn _ hf).2.1 hw)
  have hby : regValue L.input.y b.basis=regValue L.input.y s.basis := by
    apply regValue_congr; intro w hw
    exact pointFlagState_outside L _ _ _ _ _ _ (fun hf => (flag_not_input_pool L hn _ hf).2.2.1 hw)
  have hbp : regValue L.pool b.basis=0 := by
    apply Eq.trans (regValue_congr _ _ _ ?_) hz
    intro w hw
    exact pointFlagState_outside L _ _ _ _ _ _ (fun hf => (flag_not_input_pool L hn _ hf).2.2.2 hw)
  have hc := pointFlagsCompute_correct L h hn cx cy b m hbp hbz
  dsimp only at hc
  rw [hbf,hbx,hby,← hex,← hey,← hg,← hd] at hc
  have hrestore : pointFlagState L b.basis (s.basis L.equalX) (s.basis L.equalNegY)
      (s.basis L.generic) (s.basis L.double)=s.basis := by
    have hh := pointFlagState_flags L hfn b.basis (s.basis L.equalX) (s.basis L.equalNegY)
      (s.basis L.generic) (s.basis L.double)
    funext w
    by_cases hw : w∈L.flags
    · simp only [PointAddLayout.flags,List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl|rfl|rfl|rfl <;> tauto
    · rw [pointFlagState_outside L _ _ _ _ _ _ hw]
      exact pointFlagState_outside L _ _ _ _ _ _ hw
  rw [hrestore] at hc
  have he : run (pointFlagsCompute L cx cy) m b=s := hc
  calc
    run (pointFlagsClear L cx cy) m s = run (pointFlagsClear L cx cy) m
        (run (pointFlagsCompute L cx cy) m b) := congrArg (run (pointFlagsClear L cx cy) m) he.symm
    _ = b := pointFlags_roundtrip L h hn cx cy b m hbp

end ECDSAAdd.Arithmetic
