import ECDSAAdd.Arithmetic.BalancedCleanupOffsetLogic
set_option maxRecDepth 8192
set_option maxHeartbeats 900000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedCleanupOffset
attribute [local irreducible] run chain prepareHead releaseHead

/-- Actual two-prefix circuit, with no tail-circuit premise. The explicit
Boolean recurrence is the offset carry followed by the comparison carry.
Every physical bit except target is restored, including both full banks. -/
theorem chain_run (bits : List MappedBit) (xs ys cs ds : List Wire) (cinC cinB target : Wire)
    (hn : (target::cinC::cinB::(xs++ys++cs++ds)).Nodup)
    (ha : ∀w∈mappedWires bits,w∉target::cinC::cinB::(xs++ys++cs++ds))
    (hb : bits.length=ys.length) (hx : xs.length=ys.length)
    (hc : cs.length=ys.length) (hd : ds.length=ys.length)
    (s : State) (m : List Bool) (hcc : ∀q∈cs,s.basis q=false) (hdd : ∀q∈ds,s.basis q=false) :
    run (chain bits xs ys cs ds cinC cinB target) m s=
      ⟨s.phase,writeBit s.basis target (s.basis target ^^
        decision (bits.map (fun b => b.value s.basis)) (xs.map s.basis) (ys.map s.basis)
          (s.basis cinC) (s.basis cinB))⟩ := by
  induction ys generalizing bits xs cs ds cinC cinB s m with
  | nil =>
    have eb := List.eq_nil_of_length_eq_zero (by simpa using hb)
    have ex := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have ec := List.eq_nil_of_length_eq_zero (by simpa using hc)
    have ed := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst bits xs cs ds
    have ne : target≠cinB := by
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
        not_or,not_false_eq_true,and_true] at hn
      tauto
    simpa only [chain,decision,List.map_nil,controlValue,Bool.true_and] using
      flipBelow_correct none cinB target ne (by simp) s m
  | cons y ys ih =>
    cases bits with
    | nil => simp at hb
    | cons b bits =>
      cases xs with
      | nil => simp at hx
      | cons a xs =>
        cases cs with
        | nil => simp at hc
        | cons c cs =>
          cases ds with
          | nil => simp at hd
          | cons d ds =>
            have full := head_tail_nd target cinC cinB a y c d xs ys cs ds hn
            have hs := (List.nodup_append'.mp full).1
            have six := head_six_nd a y cinC cinB c d target hs
            have nd := hs
            simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
              not_or,not_false_eq_true,and_true] at nd
            rcases nd with ⟨⟨a_y,a_iC,a_iB,a_c,a_d,a_t⟩,
              ⟨y_iC,y_iB,y_c,y_d,y_t⟩,⟨iC_iB,iC_c,iC_d,iC_t⟩,
              ⟨iB_c,iB_d,iB_t⟩,⟨c_d,c_t⟩,d_t⟩
            have sourceHead (w : Wire) (hw : w∈mappedWires (b::bits))
                (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d,target]) : w≠q :=
              fun e => ha w hw (head_mem_scope target cinC cinB a y c d w xs ys cs ds (e.symm ▸ hq))
            have srcB (q : Wire) (hq : q∈[a,y,cinC,cinB,c,d,target]) : ∀w∈b.wire,w≠q :=
              fun w hw => sourceHead w (mapped_member b bits w hw) q hq
            have headSource : ∀w∈b.wire,w∉[a,y,cinC,cinB,c,d] := by
              intro w hw hq
              have hq' : w∈[a,y,cinC,cinB,c,d,target] := by
                simp only [List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto
              exact sourceHead w (mapped_member b bits w hw) w hq' rfl
            let B := b.value s.basis
            let A := s.basis a
            let Y := s.basis y
            let C := s.basis cinC
            let E := s.basis cinB
            let K := carryBit B Y C
            let S := sumBit B Y C
            let D := carryBit A (!S) E
            let u : State := ⟨s.phase,writeBit (writeBit (writeBit s.basis c K) y (!S)) d D⟩
            have pre : run (prepareHead b a y cinC cinB c d) m s=u :=
              prepareHead_run b a y cinC cinB c d six headSource s m
                (hcc c (by simp)) (hdd d (by simp))
            have uf (q : Wire) (n1 : q≠c) (n2 : q≠y) (n3 : q≠d) : u.basis q=s.basis q := by
              simp only [u,writeBit,Function.update_of_ne n1,Function.update_of_ne n2,
                Function.update_of_ne n3]
            have tailNe (q : Wire) (hq : q∈xs++ys++cs++ds) (t : Wire)
                (ht : t∈[a,y,cinC,cinB,c,d,target]) : q≠t :=
              tail_away_head target cinC cinB a y c d q t xs ys cs ds hn hq ht
            have tailSame (q : Wire) (hq : q∈xs++ys++cs++ds) : u.basis q=s.basis q :=
              uf q (tailNe q hq c (by simp)) (tailNe q hq y (by simp)) (tailNe q hq d (by simp))
            have mapA : xs.map u.basis=xs.map s.basis := by
              apply List.map_congr_left
              intro q hq
              exact tailSame q (by simp [hq])
            have mapY : ys.map u.basis=ys.map s.basis := by
              apply List.map_congr_left
              intro q hq
              exact tailSame q (by simp [hq])
            have sourceSame (w : Wire) (hw : w∈mappedWires (b::bits)) : u.basis w=s.basis w :=
              uf w (sourceHead w hw c (by simp)) (sourceHead w hw y (by simp))
                (sourceHead w hw d (by simp))
            have mapBits : bits.map (fun b => b.value u.basis)=bits.map (fun b => b.value s.basis) := by
              apply List.map_congr_left
              intro bit hbit
              apply mappedBit_value_congr
              intro w hw
              have mem : w∈mappedWires bits := by
                apply List.mem_flatMap.mpr
                refine ⟨bit,hbit,?_⟩
                cases he : bit.wire with
                | none => simp [he] at hw
                | some wire =>
                  have eq : wire=w := by simpa [he] using hw
                  subst w
                  simp [he]
              exact sourceSame w (mapped_tail_member b bits w mem)
            have uk : u.basis c=K := by simp only [u,writeBit,Function.update_of_ne
              c_d,Function.update_of_ne
              (Ne.symm y_c),Function.update_self]
            have ud : u.basis d=D := by simp only [u,writeBit,Function.update_self]
            have nt := recursive_nd target cinC cinB a y c d xs ys cs ds hn
            have tailSource : ∀w∈mappedWires bits,w∉target::c::d::(xs++ys++cs++ds) := by
              intro w hw hm
              exact ha w (mapped_tail_member b bits w hw)
                (tail_mem_scope target cinC cinB a y c d w xs ys cs ds hm)
            have cc : ∀q∈cs,u.basis q=false := fun q hq =>
              (tailSame q (by simp [hq])).trans (hcc q (by simp [hq]))
            have dd : ∀q∈ds,u.basis q=false := fun q hq =>
              (tailSame q (by simp [hq])).trans (hdd q (by simp [hq]))
            have tail := ih bits xs cs ds c d nt tailSource (by simpa using hb) (by simpa using hx)
              (by simpa using hc) (by simpa using hd) u m cc dd
            rw [mapBits,mapA,mapY,uk,ud] at tail
            let V := decision (bits.map (fun b => b.value s.basis)) (xs.map s.basis)
              (ys.map s.basis) K D
            let v : State := ⟨u.phase,writeBit u.basis target (u.basis target ^^ V)⟩
            change run (chain bits xs ys cs ds c d target) m u=v at tail
            have vf (q : Wire) (hq : q≠target) : v.basis q=u.basis q := by
              simp only [v,writeBit,Function.update_of_ne hq]
            have bu : b.value u.basis=B := mappedBit_value_congr b u.basis s.basis
              (fun w hw => sourceSame w (mapped_member b bits w hw))
            have bv : b.value v.basis=B := by
              apply Eq.trans _ bu
              apply mappedBit_value_congr
              intro w hw
              exact vf w (srcB target (by simp) w hw)
            have va : v.basis a=A := (vf a a_t).trans (uf a a_c a_y a_d)
            have vc : v.basis cinC=C := (vf cinC iC_t).trans (uf cinC iC_c (Ne.symm y_iC) iC_d)
            have ve : v.basis cinB=E := (vf cinB iB_t).trans (uf cinB iB_c (Ne.symm y_iB) iB_d)
            have vy : v.basis y= !S := by
              rw [vf y y_t]
              simp only [u,writeBit,Function.update_of_ne y_d,Function.update_self]
            have vk : v.basis c=K := (vf c c_t).trans uk
            have vd : v.basis d=D := (vf d d_t).trans ud
            let rest := m.drop (measurementCount (chain bits xs ys cs ds c d target))
            have post := releaseHead_run b a y cinC cinB c d six headSource B A Y C E v rest
              bv va vc ve vy vk vd
            rw [chain_cons,run_append,run_take,pre,prepareHead_measurements,List.drop_zero,
              run_append,run_take,tail,post]
            apply State.extensionality
            · rfl
            · funext q
              have cz : s.basis c=false := hcc c (by simp)
              have dz : s.basis d=false := hdd d (by simp)
              by_cases qt : q=target
              · subst q
                simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                  Function.update_of_ne (Ne.symm c_t),Function.update_of_ne (Ne.symm y_t),
                  Function.update_of_ne (Ne.symm d_t),Function.update_self]
              · by_cases qc : q=c
                · subst q
                  simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                    Function.update_self,Function.update_of_ne c_t,cz]
                · by_cases qy : q=y
                  · subst q
                    simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                      Function.update_of_ne y_c,Function.update_of_ne y_t,Function.update_self]
                  · by_cases qd : q=d
                    · subst q
                      simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                        Function.update_of_ne (Ne.symm c_d),Function.update_of_ne (Ne.symm y_d),
                        Function.update_of_ne d_t,Function.update_self,dz]
                    · simp only [u,v,V,B,A,Y,C,E,K,S,D,decision,List.map_cons,writeBit,
                        Function.update_of_ne qt,Function.update_of_ne qc,
                        Function.update_of_ne qy,Function.update_of_ne qd]


end ECDSAAdd.Arithmetic.BalancedCleanupOffset
#print axioms ECDSAAdd.Arithmetic.BalancedCleanupOffset.chain_run
