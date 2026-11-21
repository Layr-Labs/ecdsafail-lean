import ECDSAAdd.Submission.Entrant.Window
import ECDSAAdd.Submission.Entrant.ShadowBounds
import ECDSAAdd.Submission.Entrant.ShadowParts

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open SkywalkNat

theorem reduced_values_shadow7 (b k : Nat) (z:SkywalkNat.State) (sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    let T:=reduced b k z
    let f:=far b k z
    let h:=limb b k
    let d:=if f then gap b k z else 0
    let lu:=decide (f ∧ 2^b≤z.u)
    T.u=z.u-(if lu then d else 0) ∧ (T.u+T.v=z.u+z.v-d) ∧ T.u+T.v<3*h ∧
    PortalValues.negative sg T.u=PortalValues.negative sg z.u ∧
    (T.u-(PortalValues.negative sg T.u).toNat)=
      (z.u-(PortalValues.negative sg z.u).toNat)-(if lu then d else 0) := by
  by_cases f : far b k z
  · exact reduced_values b k z sg (small f)
  · have hu : 0 < limb b k := by simp [limb]
    have lt : z.u+z.v < 3*limb b k := (Nat.div_lt_iff_lt_mul hu).mp (Nat.lt_of_not_ge f)
    simp [reduced,f,lt]

end ECDSAAdd.Entrant.StairPacket.Shadow

namespace ECDSAAdd.Entrant.StairPacket.Shadow
open EnterProof

theorem actual_residue_shadow7 (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    let T:=reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative sg z.u
    (T.u+T.v)%V=(z.u+z.v)%V ∧ (T.u-e.toNat)%V=(z.u-e.toNat)%V := by
  by_cases f : far b k z
  · exact actual_residue b k z sg (small f)
  · simp [reduced,f]

end ECDSAAdd.Entrant.StairPacket.Shadow

namespace ECDSAAdd.Entrant.StairPacket.EnterProof


theorem shadow_digits_shadow7 (b k:Nat) (z:SkywalkNat.State) (sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    let X:=z.u+z.v; let e:=PortalValues.negative sg z.u; let M:=z.u-e.toNat
    let V:=cutUnit b k; let A:=nibble X V; let B:=nibble M V
    let mode:=decide (Shadow.far b k z); let long:=decide (Shadow.far b k z ∧ 2^b≤z.u)
    let T:=Shadow.reduced b k z
    let AA:=nibble (T.u+T.v) V; let BB:=nibble (T.u-e.toNat) V
    updateA A mode=AA ∧ updateM A B mode long=BB ∧ AA<8 ∧ BB<8 := by
  dsimp only
  let V:=cutUnit b k
  let U:=Shadow.limb b k
  let T:=Shadow.reduced b k z
  let e:=PortalValues.negative sg z.u
  have vn:0<V:=by simp [V,cutUnit]
  have mul:2*V=U:=by simp [V,U,cutUnit,Shadow.limb,pow_succ,Nat.mul_comm]
  have limit:2^b≤V:=by unfold V cutUnit;apply Nat.pow_le_pow_right (by decide);omega
  have eu:e.toNat≤z.u:=by
    by_cases pos:0<z.u <;> cases sg <;> simp_all [e,PortalValues.negative];omega
  obtain ⟨tu,tx,hi,_sign,_tm⟩:=Shadow.reduced_values_shadow7 b k z sg small
  change T.u+T.v<3*U at hi
  have less (n:Nat) (h:n≤T.u+T.v):nibble n V<8:=by
    have div:n/V<8:=(Nat.div_lt_iff_lt_mul vn).mpr (by rw [←mul] at hi; omega)
    exact (Nat.mod_le _ _).trans_lt div
  have bound2:=less (T.u-e.toNat) (by omega)
  suffices parts:updateA (nibble (z.u+z.v) V) (decide (Shadow.far b k z))=nibble (T.u+T.v) V ∧
      updateM (nibble (z.u+z.v) V) (nibble (z.u-e.toNat) V) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u))=nibble (T.u-e.toNat) V by
    exact ⟨parts.1,parts.2,less _ (le_refl _),bound2⟩
  dsimp only [T]
  by_cases hf:Shadow.far b k z
  · have h:3≤(z.u+z.v)/(2*V):=mul ▸ hf
    have gap:Shadow.gap b k z=((z.u+z.v)/(2*V)-2)*(2*V):=by rw [mul];rfl
    by_cases hl:2^b≤z.u
    · let X:=z.u+z.v;let M:=z.u-e.toNat
      let w:=borrow (nibble X V) (nibble M V) true
      have bw:w≤1:=by unfold w borrow;cases _ && _ && _ <;> decide
      have rel:X/(2*V)=M/(2*V)+w:=by
        rw [show X=M+(z.v+e.toNat) by dsimp [X,M];omega]
        have add:z.v+e.toNat≤V := by
          change z.v+e.toNat≤V
          have hv:z.v<2^b:=by have hs := small hf; omega
          have ee:e.toNat≤1:=by cases e <;> decide
          omega
        have hh:=half_limb_borrow V M (z.v+e.toNat) vn add
        change (M+(z.v+e.toNat))/(2*V)=M/(2*V)+_ at hh
        change _=M/(2*V)+borrow (nibble X V) (nibble M V) true
        rw [borrowed _ _ _ vn,show X=M+(z.v+e.toNat) by dsimp [X,M];omega]
        exact hh
      have frame:=short_digits X M V w vn bw rel rfl h
      simp only [hf,hl,true_and,decide_true,ite_true] at tu tx _tm ⊢
      rw [gap] at tu tx _tm
      rw [_sign] at _tm
      change T.u+T.v=_ at tx
      change T.u-e.toNat=_ at _tm
      exact ⟨frame.1.trans (congrArg (fun q=>nibble q V) tx.symm),frame.2.trans (congrArg (fun q=>nibble q V) _tm.symm)⟩
    · have frame:=short_other (z.u+z.v) (z.u-e.toNat) V vn h
      simp only [hf,hl,true_and,decide_false,decide_true,ite_true] at tu tx ⊢
      rw [gap] at tx
      exact ⟨frame.1.trans (congrArg (fun q=>nibble q V) tx.symm),frame.2.trans (congrArg (fun q=>nibble (q-e.toNat) V) tu.symm)⟩
  · have dst:Shadow.reduced b k z=z:=by simp [Shadow.reduced,hf]
    simp only [hf,false_and,decide_false,dst]
    exact near_digits (z.u+z.v) (z.u-e.toNat) V

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof


theorem rows_shadow7 (b k:Nat) (z:SkywalkNat.State) (g sg:Bool) (small : Shadow7.SmallIfFar b k z) :
    initialRow b k z g sg<4096 ∧ result (initialRow b k z g sg)=shadowRow b k z g sg := by
  let V:=cutUnit b k
  let U:=Shadow.limb b k
  let e:=PortalValues.negative sg z.u
  let f:=decide (Shadow.far b k z)
  let u:=decide (Shadow.far b k z ∧ 2^b≤z.u)
  let T:=Shadow.reduced b k z
  let A:=nibble (z.u+z.v) V;let M:=nibble (z.u-e.toNat) V
  let A':=nibble (T.u+T.v) V;let M':=nibble (T.u-e.toNat) V
  have sh:=shape ⟨A,Nat.mod_lt _ (by decide)⟩ ⟨M,Nat.mod_lt _ (by decide)⟩ g e f u
  refine ⟨sh.1,sh.2.trans ?_⟩
  obtain ⟨dA,dM,a0,m0⟩:=shadow_digits_shadow7 b k z sg small
  change updateA A f=A' at dA
  change updateM A M f u=M' at dM
  change A'<8 at a0;change M'<8 at m0
  have top (j:Nat) (h:j<8):j.testBit 3=false:=Nat.testBit_lt_two_pow (by simpa only [show 2^3=8 by decide] using h)
  have signedTop : (signedNibble e M').testBit 3=e:=by
    cases e <;> simp [signedNibble,Nat.testBit_xor,top _ m0,show Nat.testBit 15 3=true by decide]
  have head:A/2=Shadow.high b k z%8:=by
    rw [show A=nibble (z.u+z.v) V by rfl,digit,show 2*V=U by simp [V,U,cutUnit,Shadow.limb,pow_succ,Nat.mul_comm]]
    rfl
  change expected A M g e f u=_
  unfold expected
  rw [dA,dM]
  dsimp only
  rw [top _ a0,signedTop,head]
  simp [shadowRow,f,u,e,T,V,A',M']

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
set_option maxRecDepth 10000

theorem actual_shadow_shadow7 (map:Wire→Wire) (P:Program) (inv:Bool) (b k:Nat) (z:SkywalkNat.State)
    (g s:Bool) (small : Shadow7.SmallIfFar b k z)
    (injective:∀a c:Fin width,map a=map c→a=c) (emitted:P=renameProgram map (step inv))
    (origin:State) (tape:List Bool)
    (data:∀q∈wires (step inv),origin.basis (map q)=(rowBefore inv b k z g s).testBit q) :
    (run P tape origin).phase=origin.phase ∧
    (∀q∈wires (step inv),(run P tape origin).basis (map q)=(rowAfter inv b k z g s).testBit q) ∧
    ∀q∉wires P,(run P tape origin).basis q=origin.basis q := by
  have h:=rows_shadow7 b k z g s small
  let row:Fin 4096:=⟨initialRow b k z g s,h.1⟩
  have each (q:Wire) (hq:q∈wires (step inv)):origin.basis (map q)=(initial inv row).testBit q:=by
    cases inv <;> simpa [initial,row,h.2,rowBefore] using data q hq
  rw [emitted]
  have act:=apply_guard map inv row injective tape origin each
  refine ⟨act.1,?_,act.2.2⟩
  intro q hq
  have value:=act.2.1 q hq
  cases inv <;> simpa [finalValue,row,h.2,rowAfter] using value

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic RailPair
set_option maxRecDepth 12000

theorem short_rails_shadow7 {lo hi g n f u rs L net b k} {A:Aperture lo hi g n f u rs L net (b+k)}
    (P:Program) (place:WordPlacement A P) (z:SkywalkNat.State) (G S:Bool) (small : Shadow7.SmallIfFar b k z)
    (raw pre post:State)
    (cut:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) pre)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (data:∀q∈wires forward,post.basis (rs.getD q 0)=(shadowRow b k z G S).testBit q)
    (outside:∀q∉wires P,post.basis q=pre.basis q) :
    let T:=Shadow.reduced b k z
    signedRegValue (place.lowA++A.a) post.basis=(SkywalkRails.encode G S T.u T.v).a ∧
    signedRegValue (place.lowB++A.b) post.basis=(SkywalkRails.encode G S T.u T.v).b := by
  let T:=Shadow.reduced b k z;let V:=cutUnit b k;let e:=PortalValues.negative S z.u
  let X:=T.u+T.v;let M:=T.u-e.toNat
  have num:=PortalValues.mathematical _ _ _ _ _ _ input
  have residue:=Shadow.actual_residue_shadow7 b k z S small
  obtain ⟨_,_,pos,neg,_⟩:=Shadow.reduced_values_shadow7 b k z S small
  change PortalValues.negative S T.u=e at neg
  change X<3*Shadow.limb b k at pos
  have limb:Shadow.limb b k=2*V:=by simp [Shadow.limb,V,cutUnit,pow_succ,Nat.mul_comm]
  rw [limb] at pos
  have pv:0<V:=by simp [V,cutUnit]
  have bounded (v:Nat) (h:v≤X):v/V<16:=(Nat.div_lt_iff_lt_mul pv).mpr (by omega)
  have Xbound:X<2^(b+k+3):=by rw [pow_add]; change X<V*8; omega
  have high:=output_values rs post.basis b k z G S place.portsCount data
  rw [place.aTop,place.bTop] at high
  have same (q:Wire) (h:q∈place.lowA++place.lowB):post.basis q=raw.basis (net q):=by
    obtain ⟨hp,hn,hf,hu,hh⟩:=place.protected0 q h
    exact (outside q hp).trans (cut.unchanged q hn hf hu hh)
  have valueLo (w full:List Wire) (sub:∀q∈w,q∈place.lowA++place.lowB)
      (shape:w.map net=full.take (b+k)) (size:b+k≤full.length) (flip:Bool) :
      regValue w (fun q=>post.basis q ^^ flip)=regValue full (fun q=>raw.basis q ^^ flip)%V:=by
    calc
      _=regValue w (fun q=>raw.basis (net q) ^^ flip):=regValue_congr _ _ _ (fun q h=>congrArg (· ^^ flip) (same q (sub q h)))
      _=regValue (w.map net) (fun q=>raw.basis q ^^ flip):=(PortalValues.unroute net w (fun q=>raw.basis q ^^ flip)).symm
      _=_:=by rw [shape,takeValue _ _ size];rfl
  have lowA (flag:Bool):=valueLo _ L.a (fun _ h=>List.mem_append_left _ h) place.xa (by have h:=A.na;omega) flag
  have lowB (flag:Bool):=valueLo _ L.b (fun _ h=>List.mem_append_right _ h) place.xb (by have h:=A.nb;omega) flag
  have ds:=high
  change regValue A.a post.basis=leftWord G e (nibble X V) (nibble M V) ∧
    regValue A.b post.basis=rightWord G e (nibble X V) (nibble M V) ∧ _ at ds
  have ybound:T.u≤X:=by simp [X]
  have mbound:M≤X:=Nat.le_trans (Nat.sub_le _ _) ybound
  obtain ⟨_,_,wpos,wmag⟩:=num
  change X%V=(z.u+z.v)%V ∧ M%V=(z.u-e.toNat)%V at residue
  have la:(place.lowA++A.a).length=(b+k+3)+1:=by simp [place.al,A.spec.a]
  have lb:(place.lowB++A.b).length=(b+k+3)+1:=by simp [place.bl,A.spec.b]
  cases G
  · have pl:regValue place.lowA post.basis=X%V:=by
      have v:=lowA false
      simpa only [Bool.xor_false,show regValue L.a raw.basis=z.u+z.v from wpos,←residue.1] using v
    have ml:regValue place.lowB (fun q=>post.basis q ^^ e)=M%V:=by
      rw [lowB e,show regValue L.b (fun q=>raw.basis q ^^ e)=z.u-e.toNat from wmag,←residue.2]
    have px:=join _ _ _ X _ place.al pl ds.1 (bounded _ (le_refl _))
    have mh:=norm_nibble _ A.spec.b _ e _ ds.2.1
    have py:=join _ _ _ M _ place.bl ml mh (bounded _ mbound)
    dsimp only [M] at py
    rw [←neg] at py
    exact ⟨ordinary _ _ la _ X Xbound px,signed _ _ lb _ _ S (lt_of_le_of_lt ybound Xbound) py⟩
  · have pl:regValue place.lowB post.basis=X%V:=by
      have v:=lowB false
      simpa only [Bool.xor_false,show regValue L.b raw.basis=z.u+z.v from wpos,←residue.1] using v
    have ml:regValue place.lowA (fun q=>post.basis q ^^ e)=M%V:=by
      rw [lowA e,show regValue L.a (fun q=>raw.basis q ^^ e)=z.u-e.toNat from wmag,←residue.2]
    have px:=join _ _ _ X _ place.bl pl ds.2.1 (bounded _ (le_refl _))
    have mh:=norm_nibble _ A.spec.a _ e _ ds.1
    have py:=join _ _ _ M _ place.al ml mh (bounded _ mbound)
    dsimp only [M] at py
    rw [←neg] at py
    exact ⟨signed _ _ la _ _ S (lt_of_le_of_lt ybound Xbound) py,ordinary _ _ lb _ X Xbound px⟩

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed RailPair IntegerPacket
set_option maxRecDepth 16000

structure FramePorts_shadow7 {lo hi g n f u rs L net b k P} {A:Aperture lo hi g n f u rs L net (b+k)}
    (place:WordPlacement A P) (j:Fin 23) : Prop where
  a : ((ports (Shadow7.shape j) 0).a.map (windowNet j))=place.lowA++A.a
  bSites : ((ports (Shadow7.shape j) 0).b.map (windowNet j))=place.lowB++A.b
  prev : windowNet j (ports (Shadow7.shape j) 0).previous=rs.getD 8 0
  carry : ∀q∈(ports (Shadow7.shape j) 0).carry,let v:=windowNet j q
    v∈rs.drop 15 ∨ (v∉wires P ∧ net v∈L.carry ∧ v≠n ∧ v≠f ∧ v≠u ∧ v∉sites hi)
  ext : ∀r:Fin 15,let q:=windowNet j (ports (Shadow7.shape j) r).ext
    q∉wires P ∧ q∈hi.map Prod.fst
  hist : ∀r:Fin 15,let q:=windowNet j (ports (Shadow7.shape j) r).history
    q∉wires P ∧ q≠n ∧ q≠f ∧ q≠u ∧ q∉sites hi

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed RailPair IntegerPacket
set_option maxRecDepth 16000

theorem complete_shadow7 {lo hi g n f u rs L net b k P} {A:Aperture lo hi g n f u rs L net (b+k)}
    {place:WordPlacement A P} {j:Fin 23} (frame:FramePorts_shadow7 place j)
    (z:SkywalkNat.State) (G S:Bool) (small : Shadow7.SmallIfFar b k z)
    (raw pre post:State)
    (cut:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) pre)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (data:∀q∈wires forward,post.basis (rs.getD q 0)=(shadowRow b k z G S).testBit q)
    (save:∀q∉wires P,post.basis q=pre.basis q)
    (history:∀r:Fin 15,raw.basis (net (windowNet j (ports (Shadow7.shape j) r).history))=false) :
    let T:=Shadow.reduced b k z
    Shadow7.onRails j 0 (SkywalkRails.encode G S T.u T.v) post.basis := by
  let T:=Shadow.reduced b k z
  let Z:=SkywalkRails.encode G S T.u T.v
  have values:=short_rails_shadow7 P place z G S small raw pre post cut input data save
  have move (qs:List Wire):signedRegValue qs (mappedBasis j post.basis)=signedRegValue (qs.map (windowNet j)) post.basis:=by
    simp only [signedRegValue,List.length_map,PortalValues.unroute]
    rfl
  have gval:=actual_tags rs post.basis b k z G S data
  have sc:=output_values rs post.basis b k z G S place.portsCount data
  have clean:= (regValue_zero _ _).mp sc.2.2
  have retain (q:Wire) (no:q∉wires P) (n0:q≠n) (f0:q≠f) (u0:q≠u) (hi0:q∉sites hi):
      post.basis q=raw.basis (net q):=(save _ no).trans (cut.unchanged _ n0 f0 u0 hi0)
  refine ⟨(move _).trans (frame.a ▸ values.1),(move _).trans (frame.bSites ▸ values.2),?_,?_,?_⟩
  · change post.basis (windowNet j (ports (Shadow7.shape j) 0).previous)=Z.g
    rw [frame.prev,gval.1];cases G <;> rfl
  · apply (regValue_zero _ _).mpr
    intro q hq
    rcases frame.carry q hq with hs|⟨no,qc,n0,f0,u0,hi0⟩
    · exact clean _ hs
    · exact (retain _ no n0 f0 u0 hi0).trans ((regValue_zero _ _).mp input.2.2.2.2.2 _ qc)
  · intro r _ lt
    have bound:r<15:=lt
    let i:Fin 15:=⟨r,bound⟩
    obtain ⟨no,mem⟩:=frame.ext i
    obtain ⟨p,hp,eq⟩:=List.mem_map.mp mem
    obtain ⟨nh,h0,h1,h2,hr⟩:=frame.hist i
    refine ⟨(save _ no).trans (eq ▸ (cut.upper _ hp).1),(retain _ nh h0 h1 h2 hr).trans ?_⟩
    exact history i

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.EnterProof
open Arithmetic MappedCompressed
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

theorem return_packed_shadow7 {lo hi g n f u rs L net b k} (A:Aperture lo hi g n f u rs L net (b+k))
    (map:Wire→Wire) (p r:Program) (inj:∀a c:Fin width,map a=map c→a=c)
    (map_eq:∀q:Wire,map q=rs.getD q 0) (sz:rs.length=width)
    (pf:p=renameProgram map forward) (pr:r=renameProgram map backward)
    (raw cut:State) (z:SkywalkNat.State) (G S:Bool) (small : Shadow7.SmallIfFar b k z)
    (h:PackedCut lo hi g n f u (PortalValues.negative S z.u) (decide (Shadow.far b k z))
      (decide (Shadow.far b k z ∧ 2^b≤z.u)) (pullState net raw) cut)
    (input:SkywalkIntegerInput L (SkywalkRails.encode G S z.u z.v).a (SkywalkRails.encode G S z.u z.v).b G raw.basis)
    (m t:List Bool) : run r t (run p m cut)=cut := by
  have sup : wires forward=wires backward := by decide +kernel
  have lim:wires forward ⊆ Finset.range width := by apply ArchiveFieldScratch.bounded;decide +kernel
  have src:=read_packed A raw cut z G S h input
  have initial (q:Wire) (hq:q∈wires forward):cut.basis (map q)=(initialRow b k z G S).testBit q:=by
    rw [map_eq]
    have hv:=bitAt rs cut.basis q (sz ▸ Finset.mem_range.mp (lim hq))
    rwa [src] at hv
  have first:=actual_shadow_shadow7 map p false b k z G S small inj pf cut m initial
  have last:=actual_shadow_shadow7 map r true b k z G S small inj pr (run p m cut) t
    (fun q hq=>first.2.1 q (sup ▸ hq))
  apply congrArg₂ State.mk (last.1.trans first.1)
  funext q
  have pp:wires p=(wires forward).image map:=pf ▸ JointForward1588.wires_rename_image _ _
  have rr:wires r=wires p:=by rw [pr,JointForward1588.wires_rename_image,←sup,pp]
  by_cases mem:q∈wires p
  · obtain ⟨v,vh,rfl⟩:=Finset.mem_image.mp (pp ▸ mem)
    exact (last.2.1 _ (sup ▸ vh)).trans (initial _ vh).symm
  · exact (last.2.2 q (rr ▸ mem)).trans (first.2.2 _ mem)

end ECDSAAdd.Entrant.StairPacket.EnterProof

namespace ECDSAAdd.Entrant.StairPacket.PortalValues
open Arithmetic

theorem scanRouted_shadow7 (j : Fin 23) (k a b g n : Nat) (ps : List (Wire×Wire))
    (loc : RailPair.ScanGeometry a b g n ps)
    (left : ps.map Prod.fst = ((IntegerPacket.ports (Shadow7.shape j) 15).a.drop k).map (windowNet j))
    (right : ps.map Prod.snd = ((IntegerPacket.ports (Shadow7.shape j) 15).b.drop k).map (windowNet j))
    (aTop : a=windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).aSign)
    (bTop : b=windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).bSign)
    (prev : g=windowNet j (IntegerPacket.ports (Shadow7.shape j) 15).previous)
    (s : State) (m : List Bool) (u v : Nat) (G S : Bool)
    (h : Shadow7.onRails j 15 (SkywalkRails.encode G S u v) s.basis) (fresh:s.basis n=false)
    (la : k≤(IntegerPacket.ports (Shadow7.shape j) 15).a.length) (lb : k≤(IntegerPacket.ports (Shadow7.shape j) 15).b.length) :
    let t:=run (RailPair.scan a b g n ps) m s
    let e:=negative S u
    t.basis n=e ∧ regValue (ps.map Prod.fst) t.basis=(u+v)/2^k ∧
      regValue (ps.map Prod.snd) t.basis=(u-e.toNat)/2^k := by
  let L:=IntegerPacket.ports (Shadow7.shape j) 15
  let e:=negative S u
  have gh : mappedBasis j s.basis L.previous=G := by
    have eq := h.2.2.1
    cases G <;> exact eq
  have math := signedWords L G S u v (mappedBasis j s.basis) h.1 h.2.1 gh
  have gg:s.basis g=G := prev ▸ gh
  have ss:(s.basis a ^^ s.basis b)=e := by rw [aTop,bTop];exact math.2.1
  have act:=RailPair.scan_run _ _ _ _ _ loc s m fresh
  have vals:=scan_values _ _ _ _ _ loc s m fresh
  dsimp only at vals ⊢
  refine ⟨act.2.1.trans ss,?_⟩
  rw [gg,ss] at vals
  rw [left,right] at vals ⊢
  simp only [unroute,shiftedValue,la,lb] at vals ⊢
  obtain ⟨pos,mag⟩:=math.2.2
  cases G <;> simp only [wordPos,wordSigned,ite_true,Bool.false_eq_true,ite_false] at pos mag vals
  all_goals
    exact ⟨vals.1.trans (congrArg (· /2^k) pos),vals.2.trans (congrArg (· /2^k) mag)⟩

end ECDSAAdd.Entrant.StairPacket.PortalValues
