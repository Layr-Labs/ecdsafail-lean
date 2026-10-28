import ECDSAAdd.Arithmetic.Paper935.DepthListCompiler
import ECDSAAdd.Arithmetic.Paper935.ZeroViews

namespace ECDSAAdd.Arithmetic.Paper935

private theorem cons_of_positive (xs : List Wire) (h : 0<xs.length) :
    ∃ x rest,xs=x::rest := List.exists_cons_of_ne_nil (by intro he; simp [he] at h)

private theorem depth2_separated (one frozen output : Wire) (z f v work : List Wire)
    (hz : z.length=7) (hf : 7≤f.length) (hv : 13≤v.length)
    (hw : work.length=11)
    (hn : ([one,frozen,output]++z++f++v++work).Nodup) :
    ∃ L,compileDepth one frozen output z f v work 2=some L := by
  refine ⟨depthLayoutCandidate one frozen output z f v work 2,?_⟩
  obtain ⟨z0,zt0,rfl⟩ := cons_of_positive z (by omega)
  obtain ⟨z1,zt1,rfl⟩ := cons_of_positive zt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z2,zt2,rfl⟩ := cons_of_positive zt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z3,zt3,rfl⟩ := cons_of_positive zt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z4,zt4,rfl⟩ := cons_of_positive zt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z5,zt5,rfl⟩ := cons_of_positive zt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z6,zt6,rfl⟩ := cons_of_positive zt5 (by
    simp_all only [List.length_cons]
    omega)
  have zt6eq : zt6=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst zt6
  obtain ⟨f0,ft0,rfl⟩ := cons_of_positive f (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f1,ft1,rfl⟩ := cons_of_positive ft0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f2,ft2,rfl⟩ := cons_of_positive ft1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f3,ft3,rfl⟩ := cons_of_positive ft2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f4,ft4,rfl⟩ := cons_of_positive ft3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f5,ft5,rfl⟩ := cons_of_positive ft4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f6,ft6,rfl⟩ := cons_of_positive ft5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v0,vt0,rfl⟩ := cons_of_positive v (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v1,vt1,rfl⟩ := cons_of_positive vt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v2,vt2,rfl⟩ := cons_of_positive vt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v3,vt3,rfl⟩ := cons_of_positive vt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v4,vt4,rfl⟩ := cons_of_positive vt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v5,vt5,rfl⟩ := cons_of_positive vt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v6,vt6,rfl⟩ := cons_of_positive vt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v7,vt7,rfl⟩ := cons_of_positive vt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v8,vt8,rfl⟩ := cons_of_positive vt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v9,vt9,rfl⟩ := cons_of_positive vt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v10,vt10,rfl⟩ := cons_of_positive vt9 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v11,vt11,rfl⟩ := cons_of_positive vt10 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v12,vt12,rfl⟩ := cons_of_positive vt11 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work0,workt0,rfl⟩ := cons_of_positive work (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work1,workt1,rfl⟩ := cons_of_positive workt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work2,workt2,rfl⟩ := cons_of_positive workt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work3,workt3,rfl⟩ := cons_of_positive workt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work4,workt4,rfl⟩ := cons_of_positive workt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work5,workt5,rfl⟩ := cons_of_positive workt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work6,workt6,rfl⟩ := cons_of_positive workt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work7,workt7,rfl⟩ := cons_of_positive workt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work8,workt8,rfl⟩ := cons_of_positive workt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work9,workt9,rfl⟩ := cons_of_positive workt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work10,workt10,rfl⟩ := cons_of_positive workt9 (by
    simp_all only [List.length_cons]
    omega)
  have workt10eq : workt10=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst workt10
  unfold compileDepth
  apply if_pos
  simp_all [depthLayoutCandidate,← depthStaticCheck_iff,depthStaticCheck,
      DepthLayout.readWires,ZeroBit.wires,List.nodup_append',List.disjoint_append_right,
      eq_comm]


private theorem depth3_separated (one frozen output : Wire) (z f v work : List Wire)
    (hz : z.length=7) (hf : 7≤f.length) (hv : 13≤v.length)
    (hw : work.length=11)
    (hn : ([one,frozen,output]++z++f++v++work).Nodup) :
    ∃ L,compileDepth one frozen output z f v work 3=some L := by
  refine ⟨depthLayoutCandidate one frozen output z f v work 3,?_⟩
  obtain ⟨z0,zt0,rfl⟩ := cons_of_positive z (by omega)
  obtain ⟨z1,zt1,rfl⟩ := cons_of_positive zt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z2,zt2,rfl⟩ := cons_of_positive zt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z3,zt3,rfl⟩ := cons_of_positive zt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z4,zt4,rfl⟩ := cons_of_positive zt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z5,zt5,rfl⟩ := cons_of_positive zt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z6,zt6,rfl⟩ := cons_of_positive zt5 (by
    simp_all only [List.length_cons]
    omega)
  have zt6eq : zt6=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst zt6
  obtain ⟨f0,ft0,rfl⟩ := cons_of_positive f (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f1,ft1,rfl⟩ := cons_of_positive ft0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f2,ft2,rfl⟩ := cons_of_positive ft1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f3,ft3,rfl⟩ := cons_of_positive ft2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f4,ft4,rfl⟩ := cons_of_positive ft3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f5,ft5,rfl⟩ := cons_of_positive ft4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f6,ft6,rfl⟩ := cons_of_positive ft5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v0,vt0,rfl⟩ := cons_of_positive v (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v1,vt1,rfl⟩ := cons_of_positive vt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v2,vt2,rfl⟩ := cons_of_positive vt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v3,vt3,rfl⟩ := cons_of_positive vt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v4,vt4,rfl⟩ := cons_of_positive vt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v5,vt5,rfl⟩ := cons_of_positive vt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v6,vt6,rfl⟩ := cons_of_positive vt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v7,vt7,rfl⟩ := cons_of_positive vt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v8,vt8,rfl⟩ := cons_of_positive vt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v9,vt9,rfl⟩ := cons_of_positive vt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v10,vt10,rfl⟩ := cons_of_positive vt9 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v11,vt11,rfl⟩ := cons_of_positive vt10 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v12,vt12,rfl⟩ := cons_of_positive vt11 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work0,workt0,rfl⟩ := cons_of_positive work (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work1,workt1,rfl⟩ := cons_of_positive workt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work2,workt2,rfl⟩ := cons_of_positive workt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work3,workt3,rfl⟩ := cons_of_positive workt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work4,workt4,rfl⟩ := cons_of_positive workt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work5,workt5,rfl⟩ := cons_of_positive workt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work6,workt6,rfl⟩ := cons_of_positive workt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work7,workt7,rfl⟩ := cons_of_positive workt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work8,workt8,rfl⟩ := cons_of_positive workt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work9,workt9,rfl⟩ := cons_of_positive workt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work10,workt10,rfl⟩ := cons_of_positive workt9 (by
    simp_all only [List.length_cons]
    omega)
  have workt10eq : workt10=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst workt10
  unfold compileDepth
  apply if_pos
  simp_all [depthLayoutCandidate,← depthStaticCheck_iff,depthStaticCheck,
      DepthLayout.readWires,ZeroBit.wires,List.nodup_append',List.disjoint_append_right,
      eq_comm]


private theorem depth4_separated (one frozen output : Wire) (z f v work : List Wire)
    (hz : z.length=7) (hf : 7≤f.length) (hv : 13≤v.length)
    (hw : work.length=11)
    (hn : ([one,frozen,output]++z++f++v++work).Nodup) :
    ∃ L,compileDepth one frozen output z f v work 4=some L := by
  refine ⟨depthLayoutCandidate one frozen output z f v work 4,?_⟩
  obtain ⟨z0,zt0,rfl⟩ := cons_of_positive z (by omega)
  obtain ⟨z1,zt1,rfl⟩ := cons_of_positive zt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z2,zt2,rfl⟩ := cons_of_positive zt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z3,zt3,rfl⟩ := cons_of_positive zt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z4,zt4,rfl⟩ := cons_of_positive zt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z5,zt5,rfl⟩ := cons_of_positive zt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z6,zt6,rfl⟩ := cons_of_positive zt5 (by
    simp_all only [List.length_cons]
    omega)
  have zt6eq : zt6=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst zt6
  obtain ⟨f0,ft0,rfl⟩ := cons_of_positive f (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f1,ft1,rfl⟩ := cons_of_positive ft0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f2,ft2,rfl⟩ := cons_of_positive ft1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f3,ft3,rfl⟩ := cons_of_positive ft2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f4,ft4,rfl⟩ := cons_of_positive ft3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f5,ft5,rfl⟩ := cons_of_positive ft4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f6,ft6,rfl⟩ := cons_of_positive ft5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v0,vt0,rfl⟩ := cons_of_positive v (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v1,vt1,rfl⟩ := cons_of_positive vt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v2,vt2,rfl⟩ := cons_of_positive vt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v3,vt3,rfl⟩ := cons_of_positive vt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v4,vt4,rfl⟩ := cons_of_positive vt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v5,vt5,rfl⟩ := cons_of_positive vt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v6,vt6,rfl⟩ := cons_of_positive vt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v7,vt7,rfl⟩ := cons_of_positive vt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v8,vt8,rfl⟩ := cons_of_positive vt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v9,vt9,rfl⟩ := cons_of_positive vt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v10,vt10,rfl⟩ := cons_of_positive vt9 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v11,vt11,rfl⟩ := cons_of_positive vt10 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v12,vt12,rfl⟩ := cons_of_positive vt11 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work0,workt0,rfl⟩ := cons_of_positive work (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work1,workt1,rfl⟩ := cons_of_positive workt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work2,workt2,rfl⟩ := cons_of_positive workt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work3,workt3,rfl⟩ := cons_of_positive workt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work4,workt4,rfl⟩ := cons_of_positive workt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work5,workt5,rfl⟩ := cons_of_positive workt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work6,workt6,rfl⟩ := cons_of_positive workt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work7,workt7,rfl⟩ := cons_of_positive workt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work8,workt8,rfl⟩ := cons_of_positive workt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work9,workt9,rfl⟩ := cons_of_positive workt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work10,workt10,rfl⟩ := cons_of_positive workt9 (by
    simp_all only [List.length_cons]
    omega)
  have workt10eq : workt10=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst workt10
  unfold compileDepth
  apply if_pos
  simp_all [depthLayoutCandidate,← depthStaticCheck_iff,depthStaticCheck,
      DepthLayout.readWires,ZeroBit.wires,List.nodup_append',List.disjoint_append_right,
      eq_comm]


private theorem depth5_separated (one frozen output : Wire) (z f v work : List Wire)
    (hz : z.length=7) (hf : 7≤f.length) (hv : 13≤v.length)
    (hw : work.length=11)
    (hn : ([one,frozen,output]++z++f++v++work).Nodup) :
    ∃ L,compileDepth one frozen output z f v work 5=some L := by
  refine ⟨depthLayoutCandidate one frozen output z f v work 5,?_⟩
  obtain ⟨z0,zt0,rfl⟩ := cons_of_positive z (by omega)
  obtain ⟨z1,zt1,rfl⟩ := cons_of_positive zt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z2,zt2,rfl⟩ := cons_of_positive zt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z3,zt3,rfl⟩ := cons_of_positive zt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z4,zt4,rfl⟩ := cons_of_positive zt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z5,zt5,rfl⟩ := cons_of_positive zt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z6,zt6,rfl⟩ := cons_of_positive zt5 (by
    simp_all only [List.length_cons]
    omega)
  have zt6eq : zt6=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst zt6
  obtain ⟨f0,ft0,rfl⟩ := cons_of_positive f (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f1,ft1,rfl⟩ := cons_of_positive ft0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f2,ft2,rfl⟩ := cons_of_positive ft1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f3,ft3,rfl⟩ := cons_of_positive ft2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f4,ft4,rfl⟩ := cons_of_positive ft3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f5,ft5,rfl⟩ := cons_of_positive ft4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f6,ft6,rfl⟩ := cons_of_positive ft5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v0,vt0,rfl⟩ := cons_of_positive v (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v1,vt1,rfl⟩ := cons_of_positive vt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v2,vt2,rfl⟩ := cons_of_positive vt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v3,vt3,rfl⟩ := cons_of_positive vt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v4,vt4,rfl⟩ := cons_of_positive vt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v5,vt5,rfl⟩ := cons_of_positive vt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v6,vt6,rfl⟩ := cons_of_positive vt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v7,vt7,rfl⟩ := cons_of_positive vt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v8,vt8,rfl⟩ := cons_of_positive vt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v9,vt9,rfl⟩ := cons_of_positive vt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v10,vt10,rfl⟩ := cons_of_positive vt9 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v11,vt11,rfl⟩ := cons_of_positive vt10 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v12,vt12,rfl⟩ := cons_of_positive vt11 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work0,workt0,rfl⟩ := cons_of_positive work (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work1,workt1,rfl⟩ := cons_of_positive workt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work2,workt2,rfl⟩ := cons_of_positive workt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work3,workt3,rfl⟩ := cons_of_positive workt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work4,workt4,rfl⟩ := cons_of_positive workt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work5,workt5,rfl⟩ := cons_of_positive workt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work6,workt6,rfl⟩ := cons_of_positive workt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work7,workt7,rfl⟩ := cons_of_positive workt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work8,workt8,rfl⟩ := cons_of_positive workt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work9,workt9,rfl⟩ := cons_of_positive workt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work10,workt10,rfl⟩ := cons_of_positive workt9 (by
    simp_all only [List.length_cons]
    omega)
  have workt10eq : workt10=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst workt10
  unfold compileDepth
  apply if_pos
  simp_all [depthLayoutCandidate,← depthStaticCheck_iff,depthStaticCheck,
      DepthLayout.readWires,ZeroBit.wires,List.nodup_append',List.disjoint_append_right,
      eq_comm]


private theorem depth6_separated (one frozen output : Wire) (z f v work : List Wire)
    (hz : z.length=7) (hf : 7≤f.length) (hv : 13≤v.length)
    (hw : work.length=11)
    (hn : ([one,frozen,output]++z++f++v++work).Nodup) :
    ∃ L,compileDepth one frozen output z f v work 6=some L := by
  refine ⟨depthLayoutCandidate one frozen output z f v work 6,?_⟩
  obtain ⟨z0,zt0,rfl⟩ := cons_of_positive z (by omega)
  obtain ⟨z1,zt1,rfl⟩ := cons_of_positive zt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z2,zt2,rfl⟩ := cons_of_positive zt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z3,zt3,rfl⟩ := cons_of_positive zt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z4,zt4,rfl⟩ := cons_of_positive zt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z5,zt5,rfl⟩ := cons_of_positive zt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨z6,zt6,rfl⟩ := cons_of_positive zt5 (by
    simp_all only [List.length_cons]
    omega)
  have zt6eq : zt6=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst zt6
  obtain ⟨f0,ft0,rfl⟩ := cons_of_positive f (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f1,ft1,rfl⟩ := cons_of_positive ft0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f2,ft2,rfl⟩ := cons_of_positive ft1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f3,ft3,rfl⟩ := cons_of_positive ft2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f4,ft4,rfl⟩ := cons_of_positive ft3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f5,ft5,rfl⟩ := cons_of_positive ft4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨f6,ft6,rfl⟩ := cons_of_positive ft5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v0,vt0,rfl⟩ := cons_of_positive v (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v1,vt1,rfl⟩ := cons_of_positive vt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v2,vt2,rfl⟩ := cons_of_positive vt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v3,vt3,rfl⟩ := cons_of_positive vt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v4,vt4,rfl⟩ := cons_of_positive vt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v5,vt5,rfl⟩ := cons_of_positive vt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v6,vt6,rfl⟩ := cons_of_positive vt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v7,vt7,rfl⟩ := cons_of_positive vt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v8,vt8,rfl⟩ := cons_of_positive vt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v9,vt9,rfl⟩ := cons_of_positive vt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v10,vt10,rfl⟩ := cons_of_positive vt9 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v11,vt11,rfl⟩ := cons_of_positive vt10 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨v12,vt12,rfl⟩ := cons_of_positive vt11 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work0,workt0,rfl⟩ := cons_of_positive work (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work1,workt1,rfl⟩ := cons_of_positive workt0 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work2,workt2,rfl⟩ := cons_of_positive workt1 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work3,workt3,rfl⟩ := cons_of_positive workt2 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work4,workt4,rfl⟩ := cons_of_positive workt3 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work5,workt5,rfl⟩ := cons_of_positive workt4 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work6,workt6,rfl⟩ := cons_of_positive workt5 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work7,workt7,rfl⟩ := cons_of_positive workt6 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work8,workt8,rfl⟩ := cons_of_positive workt7 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work9,workt9,rfl⟩ := cons_of_positive workt8 (by
    simp_all only [List.length_cons]
    omega)
  obtain ⟨work10,workt10,rfl⟩ := cons_of_positive workt9 (by
    simp_all only [List.length_cons]
    omega)
  have workt10eq : workt10=[] := List.length_eq_zero_iff.mp (by
    simp_all only [List.length_cons]
    omega)
  subst workt10
  unfold compileDepth
  apply if_pos
  simp_all [depthLayoutCandidate,← depthStaticCheck_iff,depthStaticCheck,
      DepthLayout.readWires,ZeroBit.wires,List.nodup_append',List.disjoint_append_right,
      eq_comm]


theorem compileDepth_separated (one frozen output : Wire) (z f v work : List Wire)
    (depth : Nat) (hz : z.length=7) (hf : 7≤f.length) (hv : 13≤v.length)
    (hw : work.length=11) (hd : 2≤depth ∧ depth≤6)
    (hn : ([one,frozen,output]++z++f++v++work).Nodup) :
    ∃ L,compileDepth one frozen output z f v work depth=some L := by
  obtain ⟨lo,hi⟩ := hd
  interval_cases depth
  · exact depth2_separated one frozen output z f v work hz hf hv hw hn
  · exact depth3_separated one frozen output z f v work hz hf hv hw hn
  · exact depth4_separated one frozen output z f v work hz hf hv hw hn
  · exact depth5_separated one frozen output z f v work hz hf hv hw hn
  · exact depth6_separated one frozen output z f v work hz hf hv hw hn

end ECDSAAdd.Arithmetic.Paper935
