import ECDSAAdd.Math.SkywalkTerminalLastControls

/-! The actual signed-rail swap flags telescope, including terminal zero. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Entrant.TraceParity5
open SkywalkRails SkywalkTrace Secp256k1

def smallSign (r : SkywalkRails.State) : Bool :=
  if r.g then neg r.a else neg r.b

def parity : List Bool → Bool
  | [] => false
  | b::bs => b ^^ parity bs

def swapParity (cs : List (Bool×Bool)) : Bool := parity (cs.map Prod.snd)

theorem smallSign_encode (g s : Bool) (u v : Int) :
    smallSign (encode g s u v)=neg (signed s u) := by
  cases g <;> rfl

theorem smallSign_zero (g s : Bool) (v : Int) :
    smallSign (encode g s 0 v)=false := by
  rw [smallSign_encode,zero_sign]
  rfl

theorem step_swap (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    (code (encode g s (z.u : Int) (z.v : Int))).2=
      (smallSign (encode g s (z.u : Int) (z.v : Int)) ^^
        smallSign (next (encode g s (z.u : Int) (z.v : Int)))) := by
  have hui : (0:Int)≤z.u := by omega
  have hvi : (0:Int)<z.v := by omega
  have hvoi : (z.v : Int)%2=1 := by omega
  by_cases he : z.u%2=0
  · have hei : (z.u : Int)%2=0 := by omega
    have hhalf : signed s ((z.u : Int)/2)=(signed s (z.u : Int))/2 := by
      cases s <;> simp only [signed,Bool.false_eq_true,if_false,if_true]
      omega
    have hsign : neg (signed s ((z.u : Int)/2))=neg (signed s (z.u : Int)) := by
      rw [hhalf]
      apply neg_half
      cases s <;> simp only [signed,Bool.false_eq_true,if_false,if_true] <;> omega
    simp only [code,next]
    rw [step_encode_even g s _ _ hui hvi hvoi hei,smallSign_encode]
    simp only [smallSign,railsOf,if_true]
    rw [hsign,Bool.xor_self]
  · have hei : (z.u : Int)%2≠0 := by omega
    have hlarge : ((z.u : Int)+(z.v : Int))%2=0 := by omega
    have hneg : (-(z.u : Int))%2≠0 := by omega
    have source :
        (route (encode g s (z.u : Int) (z.v : Int)).a
          (encode g s (z.u : Int) (z.v : Int)).b).2=signed s (z.u : Int) := by
      cases g <;> cases s <;> simp [encode,signed,route,odd,hei,hlarge,hneg]
    have hg : (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).g=false := by
      have h := (code_classified g s z hv hvo).1
      simpa [code,he] using h
    change (neg (route (encode g s (z.u : Int) (z.v : Int)).a
      (encode g s (z.u : Int) (z.v : Int)).b).2 ^^
      neg (SkywalkRails.step (encode g s (z.u : Int) (z.v : Int))).k)=_
    rw [source,smallSign_encode]
    simp only [next,smallSign,railsOf,hg,Bool.false_eq_true,if_false]

theorem trace_telescope (n : Nat) (g s : Bool) (z : SkywalkNat.State)
    (hv : 0<z.v) (hvo : z.v%2=1) :
    swapParity (trace n (encode g s (z.u : Int) (z.v : Int)))=
      (smallSign (encode g s (z.u : Int) (z.v : Int)) ^^
        smallSign (next^[n] (encode g s (z.u : Int) (z.v : Int)))) := by
  induction n generalizing g s z with
  | zero => simp [trace,swapParity,parity]
  | succ n ih =>
    let r := encode g s (z.u : Int) (z.v : Int)
    let t := SkywalkRails.step r
    have enc := step_reencode g s z hv hvo
    change next r=encode t.g (smallerSign t) ((SkywalkNat.step z).u : Int)
      ((SkywalkNat.step z).v : Int) at enc
    have valid := SkywalkNat.step_v_odd_pos z hv hvo
    have tail := ih t.g (smallerSign t) (SkywalkNat.step z) valid.1 valid.2
    rw [←enc] at tail
    change ((code r).2 ^^ swapParity (trace n (next r)))=_
    rw [tail,step_swap g s z hv hvo,Function.iterate_succ_apply]
    simp [r,Bool.xor_assoc,Bool.xor_comm,Bool.xor_left_comm]

theorem trace512_parity (x : Nat) (hx0 : 0<x) (hx : x<p) :
    swapParity (trace 512 (encode false false (x : Int) (p : Int)))=false := by
  have hp0 : 0<p := p_prime.pos
  have hpodd : p%2=1 := by norm_num [p]
  have hp : p<2^256 := by norm_num [p]
  have hc : x.Coprime p := by
    apply Nat.Coprime.symm
    apply p_prime.coprime_iff_not_dvd.mpr
    intro hd
    exact (Nat.not_le_of_lt hx) (Nat.le_of_dvd hx0 hd)
  have terminal := SkywalkNat.terminates_2n p x 256 hp0 hx0 hpodd hp (hx.trans hp) hc
  obtain ⟨G,S,enc⟩ := iter_encoded 512 false false (SkywalkNat.init x p) hp0 hpodd
  change next^[512] (encode false false (x : Int) (p : Int))=
    encode G S ((SkywalkNat.step^[512] (SkywalkNat.init x p)).u : Int)
      ((SkywalkNat.step^[512] (SkywalkNat.init x p)).v : Int) at enc
  rw [terminal.1,terminal.2] at enc
  have small : smallSign (next^[512] (encode false false (x : Int) (p : Int)))=false := by
    rw [enc]
    exact smallSign_zero G S 1
  have telesc := trace_telescope 512 false false (SkywalkNat.init x p) hp0 hpodd
  simp only [SkywalkNat.init] at telesc
  rw [small] at telesc
  simpa [smallSign_encode,signed,neg] using telesc

def xorRange : Nat → (Nat → Bool) → Bool
  | 0, _ => false
  | n+1, f => f 0 ^^ xorRange n (fun i => f (i+1))

theorem parity_range (n : Nat) (f : Nat → Bool) :
    parity ((List.range n).map f)=xorRange n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,parity,xorRange]
    exact congrArg (fun b => f 0 ^^ b) (ih (fun i => f (i+1)))

theorem xorRange_congr (n : Nat) (f g : Nat → Bool)
    (h : ∀i,i<n → f i=g i) : xorRange n f=xorRange n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange]
    rw [h 0 (by omega),ih (fun i => f (i+1)) (fun i => g (i+1))
      (fun i hi => h (i+1) (by omega))]

theorem xorRange_add (n m : Nat) (f : Nat → Bool) :
    xorRange (n+m) f=(xorRange n f ^^ xorRange m (fun i => f (n+i))) := by
  induction n generalizing f with
  | zero => simp [xorRange]
  | succ n ih =>
    rw [show n+1+m=(n+m)+1 by omega]
    simp only [xorRange]
    rw [ih (fun i => f (i+1))]
    simp only [Bool.xor_assoc]
    congr 2
    apply xorRange_congr
    intro i hi
    congr 1
    omega

theorem xorRange_group (n width : Nat) (f : Nat → Bool) :
    xorRange (n*width) f=
      xorRange n (fun j => xorRange width (fun i => f (width*j+i))) := by
  induction n generalizing f with
  | zero => simp only [Nat.zero_mul,xorRange]
  | succ n ih =>
    rw [show (n+1)*width=width+n*width by
      simp only [Nat.add_mul,Nat.one_mul,Nat.add_comm],xorRange_add]
    rw [ih (fun i => f (width+i))]
    simp only [xorRange,Nat.mul_zero,Nat.zero_add]
    congr 1
    apply xorRange_congr
    intro j hj
    apply xorRange_congr
    intro i hi
    congr 1
    simp only [Nat.mul_add,Nat.mul_one]
    omega

theorem swapParity_index (cs : List (Bool×Bool)) (default : Bool×Bool) :
    xorRange cs.length (fun i => (cs.getD i default).2)=swapParity cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.length_cons,xorRange,List.getD_cons_zero,swapParity,List.map_cons,parity]
    change (c.2 ^^ xorRange cs.length (fun i => (cs.getD i default).2))=_
    rw [ih]
    rfl

def rawS (x i : Nat) : Bool :=
  ((trace 512 (encode false false (x : Int) (p : Int))).getD i (false,false)).2

theorem rawS511 (x : Nat) (hx0 : 0<x) (hx : x<p) : rawS x 511=false := by
  simp only [rawS,trace512_last x hx0 hx (false,false)]

theorem rawS512_parity (x : Nat) (hx0 : 0<x) (hx : x<p) :
    xorRange 512 (rawS x)=false := by
  have indexed := swapParity_index
    (trace 512 (encode false false (x : Int) (p : Int))) (false,false)
  rw [trace_length] at indexed
  exact indexed.trans (trace512_parity x hx0 hx)

/-- The unpacked penultimate S flag supplies the parity of the packed prefix. -/
theorem rawS510_relation (x : Nat) (hx0 : 0<x) (hx : x<p) :
    xorRange 510 (rawS x)=rawS x 510 := by
  have whole := rawS512_parity x hx0 hx
  have split := xorRange_add 510 2 (rawS x)
  have last := rawS511 x hx0 hx
  have tail : xorRange 2 (fun i => rawS x (510+i))=rawS x 510 := by
    change (rawS x 510 ^^ (rawS x 511 ^^ false))=rawS x 510
    rw [last]
    simp
  have eq : xorRange 512 (rawS x)=(xorRange 510 (rawS x) ^^ rawS x 510) := by
    rw [tail] at split
    exact split
  rw [eq] at whole
  cases h : xorRange 510 (rawS x) <;> cases k : rawS x 510 <;> simp_all

/-- The local codec supplies each of these 102 equalities. No global host
cleanliness is assumed. -/
theorem encoded_payload_parity (x : Nat) (hx0 : 0<x) (hx : x<p)
    (payload : Nat → Bool)
    (packets : ∀j,j<102 →
      xorRange 8 (fun i => payload (8*j+i))=
        xorRange 5 (fun i => rawS x (5*j+i))) :
    xorRange 816 payload=rawS x 510 := by
  rw [show 816=102*8 from rfl,xorRange_group]
  rw [xorRange_congr 102 _ _ packets]
  rw [←xorRange_group 102 5]
  exact rawS510_relation x hx0 hx

end ECDSAAdd.Entrant.TraceParity5
