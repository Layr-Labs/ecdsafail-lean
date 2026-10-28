import ECDSAAdd.Arithmetic.BalancedFieldConvertProgram
import ECDSAAdd.Arithmetic.Reduction
set_option maxRecDepth 8192
set_option maxHeartbeats 500000
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
namespace ECDSAAdd.Arithmetic.BalancedConvert
open BalancedField BalancedCircuit BalancedFold Secp256k1

def wordModulus : Nat := 2^256
def wordHalf : Nat := 2^255
def threshold (x : Fp) : Bool := decide (q<(x.val : Int))
theorem convert_constants : wordModulus=2*wordHalf ∧ sparseF=2*bias+1 ∧
    0<bias ∧ bias<wordHalf ∧ p+sparseF=wordModulus ∧ 0≤q ∧
    q=(wordHalf : Int)-(bias : Int)-1 ∧ p≤wordModulus ∧ q<(wordModulus : Int) := by decide

theorem generic_bias (H K F P x : Nat) (hm : P+F=2*H)
    (hf : F=2*K+1) (hx : x<P) :
    x+K<2*H ∧ (H≤x+K ↔ H-K-1<x) := by omega

theorem generic_center (H K F P x : Nat) (hm : P+F=2*H)
    (hf : F=2*K+1) (hx : x<P) :
    (if H-K-1<x then x+F else x)<2*H ∧
    (H≤(if H-K-1<x then x+F else x) ↔ H-K-1<x) := by split_ifs <;> omega

theorem generic_unbias (M K x : Nat) (hK : K≤M) (hx : x<M) :
    (x+K+(M-K))%M=x := by
  rw [show x+K+(M-K)=x+M by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hx]

theorem generic_unshift (M F x : Nat) (hx : x<M) : (x+F+M-F)%M=x := by
  rw [show x+F+M-F=x+M by omega,Nat.add_mod_right,Nat.mod_eq_of_lt hx]

theorem generic_center_range (X P Q M : Int) (hx : 0≤X ∧ X<P)
    (hp : P≤M) :
    -M≤(if X≤Q then X else X-P) ∧ (if X≤Q then X else X-P)<M := by
  split_ifs <;> omega

theorem generic_center_encoding (X P Q M F : Int) (hx : 0≤X ∧ X<P)
    (hm : P+F=M) :
    (if X≤Q then X else X-P)+(if (if X≤Q then X else X-P)<0 then M else 0)=
      (if Q<X then X+F else X) := by
  by_cases hc : X≤Q
  · simp only [if_pos hc,if_neg (show ¬Q<X by omega),if_neg (show ¬X<0 by omega),add_zero]
  · simp only [if_neg hc,if_pos (show Q<X by omega),if_pos (show X-P<0 by omega)]
    omega

theorem canonical_bound (x : Fp) : x.val<p := by
  letI : NeZero p := ⟨p_prime.ne_zero⟩
  exact ZMod.val_lt x

theorem canonical_word_bound (x : Fp) : x.val<wordModulus := by
  rcases convert_constants with ⟨_,_,_,_,_,_,_,hp,_⟩
  exact lt_of_lt_of_le (canonical_bound x) hp

theorem biased_value (x : Fp) : x.val+bias<wordModulus ∧
    (wordHalf≤x.val+bias ↔ threshold x=true) := by
  rcases convert_constants with ⟨hm,hf,hk,hK,hp,hq,hQ,hPM,hQM⟩
  have g := generic_bias wordHalf bias sparseF p x.val (hp.trans hm) hf (canonical_bound x)
  refine ⟨by simpa only [←hm] using g.1,?_⟩
  have hi : ((wordHalf-bias-1 : Nat) : Int)=q := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hK)),
      Nat.cast_sub (Nat.le_of_lt hK),Nat.cast_one,hQ]
  simpa only [threshold,decide_eq_true_eq,←hi,Nat.cast_lt] using g.2

theorem centerWord_value (x : Fp) : centerWord x=if threshold x then x.val+sparseF else x.val := by
  rcases convert_constants with ⟨hm,hf,hk,hK,hp,hq,hQ,hPM,hQM⟩
  have hx : 0≤(x.val : Int) ∧ (x.val : Int)<(p : Int) :=
    ⟨Nat.cast_nonneg _,by exact_mod_cast canonical_bound x⟩
  have hp' : (p : Int)≤(wordModulus : Int) := by exact_mod_cast hPM
  have hm' : (p : Int)+(sparseF : Int)=(wordModulus : Int) := by exact_mod_cast hp
  have hr := generic_center_range (x.val : Int) p q wordModulus hx hp'
  have he := encode_shift 256 (centerFp x) hr
  have hv := generic_center_encoding (x.val : Int) p q wordModulus sparseF hx hm'
  change (centerWord x : Int)=_ at he
  rw [show centerFp x=(if (x.val : Int)≤q then (x.val : Int) else (x.val : Int)-(p : Int)) from rfl] at he
  have eq : (centerWord x : Int)=(if threshold x then ((x.val+sparseF : Nat) : Int) else (x.val : Int)) := by
    simpa only [threshold,Bool.cond_eq_ite,decide_eq_true_eq,Nat.cast_add] using he.trans hv
  exact_mod_cast eq

theorem center_threshold (x : Fp) : wordHalf≤centerWord x ↔ threshold x=true := by
  rcases convert_constants with ⟨hm,hf,hk,hK,hp,hq,hQ,hPM,hQM⟩
  have g := generic_center wordHalf bias sparseF p x.val (hp.trans hm) hf (canonical_bound x)
  have hi : ((wordHalf-bias-1 : Nat) : Int)=q := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr (Nat.sub_pos_of_lt hK)),
      Nat.cast_sub (Nat.le_of_lt hK),Nat.cast_one,hQ]
  rw [centerWord_value]
  simpa only [threshold,Bool.cond_eq_ite,decide_eq_true_eq,←hi,Nat.cast_lt] using g.2

theorem center_add_value (x : Fp) :
    (x.val+(if threshold x then sparseF else 0))%wordModulus=centerWord x := by
  rw [centerWord_value]
  cases ht : threshold x
  · simp only [Bool.false_eq_true,if_false,Nat.add_zero]
    exact Nat.mod_eq_of_lt (canonical_word_bound x)
  · simp only [if_true]
    apply Nat.mod_eq_of_lt
    have hb : centerWord x<wordModulus := encodeWord_bound 256 (centerFp x)
    simpa only [centerWord_value,ht,if_true] using hb

theorem canonical_sub_value (x : Fp) :
    (centerWord x+wordModulus-(if threshold x then sparseF else 0))%wordModulus=x.val := by
  rw [centerWord_value]
  cases ht : threshold x
  · simp only [Bool.false_eq_true,if_false,Nat.sub_zero]
    rw [Nat.add_mod_right,Nat.mod_eq_of_lt (canonical_word_bound x)]
  · simp only [if_true]
    exact generic_unshift _ _ _ (canonical_word_bound x)

private def virtualCorrection (b : Bool) : Nat :=
  (List.range 256).foldr (fun i n => (if sparseF.testBit i then b else false).toNat+2*n) 0
private theorem virtualCorrection_value (b : Bool) :
    virtualCorrection b=if b then sparseF else 0 := by cases b <;> decide
private theorem correction_list (is : List Nat) (L : Layout) (s : BasisState) :
    mappedValue (is.map (fun i => ({wire := (if sparseF.testBit i then some L.flag else none), flip := false} : MappedBit))) s=
    is.foldr (fun i n => (if sparseF.testBit i then s L.flag else false).toNat+2*n) 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.map_cons,mappedValue,List.foldr_cons,ih]
    cases hi : sparseF.testBit i <;> simp [MappedBit.value,hi]

theorem correction_value (L : Layout) (s : BasisState) :
    mappedValue (correction L) s=if s L.flag then sparseF else 0 := by
  rw [correction,correction_list]
  exact virtualCorrection_value _

theorem correction_sources (L : Layout) (w : Wire) (hw : w∈mappedWires (correction L)) : w=L.flag := by
  obtain ⟨b,hb,hw⟩ := List.mem_flatMap.mp hw
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
  cases hf : sparseF.testBit i
  · simp [hf] at hw
  · simpa [hf] using hw
def scratch (L : Layout) : List Wire := [L.cin,L.one]++L.carry
 def work (L : Layout) : List Wire := L.flag::scratch L

theorem word_length (L : Layout) (hw : L.Widths) : L.word.length=256 := by simp [Layout.word,hw.1]
theorem bias_le_modulus : bias≤wordModulus := by decide

theorem layout_literal (L : Layout) (hn : L.wires.Nodup) : (L.one::L.cin::(L.word++L.carry)).Nodup := by
  apply List.nodup_iff_count.mpr
  intro q
  have h := List.nodup_iff_count.mp hn q
  simp only [Layout.wires,Layout.word,List.count_cons,List.count_append,List.count_nil] at h ⊢
  omega

theorem layout_add (L : Layout) (hn : L.wires.Nodup) : (L.cin::(L.word++L.carry)).Nodup :=
  (List.nodup_cons.mp (layout_literal L hn)).2

theorem layout_away (L : Layout) (hn : L.wires.Nodup) (q : Wire)
    (hq : q∈[L.cin,L.one,L.flag]++L.carry) : q∉L.word := by
  have nd : (L.word++([L.cin,L.one,L.flag]++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have h := List.nodup_iff_count.mp hn a
    simp only [Layout.wires,Layout.word,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  exact fun h => List.disjoint_left.mp (List.nodup_append'.mp nd).2.2 h hq

theorem flag_away (L : Layout) (hn : L.wires.Nodup) : L.flag∉L.cin::(L.word++L.carry) := by
  have nd : (L.flag::L.cin::(L.word++L.carry)).Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have h := List.nodup_iff_count.mp hn a
    simp only [Layout.wires,Layout.word,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  exact (List.nodup_cons.mp nd).1

theorem scratch_away (L : Layout) (hn : L.wires.Nodup) (q : Wire) (hq : q∈scratch L) :
    q∉L.word ∧ q≠L.flag := by
  have a := layout_away L hn q (by simp only [scratch,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢; tauto)
  have nd : (L.flag::scratch L).Nodup := by
    apply List.nodup_iff_count.mpr
    intro a
    have h := List.nodup_iff_count.mp hn a
    simp only [Layout.wires,scratch,List.count_cons,List.count_append,List.count_nil] at h ⊢
    omega
  exact ⟨a,fun e => (List.nodup_cons.mp nd).1 (e ▸ hq)⟩

theorem word_msb (L : Layout) (hw : L.Widths) (s : BasisState) (v : Nat) (B : Bool)
    (hv : regValue L.word s=v) (hb : wordHalf≤v ↔ B=true) : s L.msb=B := by
  have high := regValue_highBit L.low L.msb s
  rw [hw.1] at high
  change s L.msb=true ↔ wordHalf≤regValue L.word s at high
  rw [hv] at high
  cases hs : s L.msb <;> cases B <;> simp_all

end ECDSAAdd.Arithmetic.BalancedConvert
#print axioms ECDSAAdd.Arithmetic.BalancedConvert.centerWord_value
