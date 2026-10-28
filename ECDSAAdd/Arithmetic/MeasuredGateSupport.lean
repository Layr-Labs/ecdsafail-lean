import ECDSAAdd.Arithmetic.MeasuredStreamedSquare

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace ECDSAAdd.Arithmetic

theorem mappedSub_wires_subset (bits : List MappedBit) (ys carry : List Wire) (cin : Wire) :
    wires (mappedSub bits ys carry cin)⊆(mappedWires bits++ys++carry++[cin]).toFinset := by
  have ha := mappedAdd_wires_subset bits ys carry cin
  intro q hq
  simp only [mappedSub,wires_append,Finset.mem_union,notRegister_wires] at hq
  rcases hq with (hq|hq)|hq
  · simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto
  · exact ha hq
  · simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
    tauto

theorem mappedConstAdd_wires_subset (control : Option Wire) (ys carry : List Wire)
    (cin : Wire) (k : Nat) :
    wires (mappedConstAdd control ys carry cin k)⊆(control.toList++ys++carry++[cin]).toFinset := by
  apply (mappedAdd_wires_subset _ _ _ _).trans
  intro q hq
  simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
  have hc : q∈mappedWires (mappedConstant control ys.length k) → q∈control.toList := by
    intro h
    simpa using mappedConstant_wires control ys.length k q h
  tauto

theorem constantBorrow_wires_subset (b : Bool) (x cin target : Wire) :
    wires (constantBorrow b x cin target)⊆[x,cin,target].toFinset ∧
    wires (constantBorrowErase b x cin target)⊆[x,cin,target].toFinset := by
  have h := mappedBit_wires ({wire:=none,flip:=b} : MappedBit) x cin target
  constructor
  · intro q hq
    simp only [constantBorrow,wires_append,Finset.mem_union] at hq
    have hh : q∈wires (mappedMajority {wire:=none,flip:=b} x cin target) →
        q∈[x,cin,target].toFinset := by
      intro hq
      simpa using h.1 hq
    simp [wires,Instr.wires] at hq hh ⊢
    tauto
  · intro q hq
    simp only [constantBorrowErase,wires_append,Finset.mem_union] at hq
    have hh : q∈wires (mappedEraseCarry {wire:=none,flip:=b} x cin target) →
        q∈[x,cin,target].toFinset := by
      intro hq
      simpa using h.2.1 hq
    simp [wires,Instr.wires] at hq hh ⊢
    tauto

theorem compareConstantLt_wires_subset (xs carry : List Wire) (cin target : Wire) (k : Nat) :
    wires (compareConstantLt xs carry cin target k)⊆(xs++carry++[cin,target]).toFinset := by
  induction xs generalizing carry cin k with
  | nil => simp [compareConstantLt,wires]
  | cons x xs ih =>
    cases xs with
    | nil =>
      apply (constantBorrow_wires_subset _ _ _ _).1.trans
      intro q hq
      simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
      tauto
    | cons x' xs =>
      cases carry with
      | nil => simp [compareConstantLt,wires]
      | cons c cs =>
        have head := constantBorrow_wires_subset (decide (k%2=1)) x cin c
        have tail := ih cs c (k/2)
        intro q hq
        rw [compareConstantLt] at hq
        simp only [wires_append,Finset.mem_union] at hq
        have h1 := head.1
        have h2 := head.2
        rcases hq with (hq|hq)|hq
        · have h := h1 hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
          tauto
        · have h := tail hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
          tauto
        · have h := h2 hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
          tauto

theorem compareConstantGe_wires_subset (xs carry : List Wire) (cin target : Wire) (k : Nat) :
    wires (compareConstantGe xs carry cin target k)⊆(xs++carry++[cin,target]).toFinset := by
  have h := compareConstantLt_wires_subset xs carry cin target k
  intro q hq
  simp only [compareConstantGe,wires_append,Finset.mem_union] at hq
  rcases hq with hq|hq
  · exact h hq
  · simp [wires,Instr.wires] at hq ⊢
    tauto

theorem borrowPair_wires_subset (x y cin target : Wire) :
    wires (borrowMajority x y cin target)⊆[x,y,cin,target].toFinset ∧
    wires (eraseBorrow x y cin target)⊆[x,y,cin,target].toFinset := by
  constructor <;> intro q hq <;>
    simp [borrowMajority,eraseBorrow,majority,eraseCarry,wires,Instr.wires,correctionWires] at hq ⊢ <;> tauto

theorem eraseLtChain_wires_subset (xs ys carry : List Wire) (cin target : Wire) :
    wires (eraseLtChain xs ys carry cin target)⊆(xs++ys++carry++[cin,target]).toFinset := by
  induction xs generalizing ys carry cin with
  | nil => simp [eraseLtChain,wires]
  | cons x xs ih =>
    cases ys with
    | nil => simp [eraseLtChain,wires]
    | cons y ys =>
      cases xs with
      | nil =>
        cases ys with
        | nil =>
          apply (borrowPair_wires_subset x y cin target).2.trans
          intro q hq
          simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hq ⊢
          tauto
        | cons y' ys => simp [eraseLtChain,wires]
      | cons x' xs =>
        cases ys with
        | nil => simp [eraseLtChain,wires]
        | cons y' ys =>
          cases carry with
          | nil => simp [eraseLtChain,wires]
          | cons c cs =>
            have head := borrowPair_wires_subset x y cin c
            have tail := ih (y'::ys) cs c
            intro q hq
            rw [eraseLtChain] at hq
            simp only [wires_append,Finset.mem_union] at hq
            rcases hq with (hq|hq)|hq
            · have h := head.1 hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
              tauto
            · have h := tail hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
              tauto
            · have h := head.2 hq
              simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
              tauto

theorem mappedSignedSquare_wires_subset (xs dst pad carry : List Wire) (cin : Wire)
    (hd : dst.length=2*xs.length) (hp : 1≤pad.length) (hc : dst.length-1≤carry.length) :
    wires (mappedSignedSquare xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset ∧
    wires (mappedSignedSquareClear xs dst pad carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
  have rows := signedSquareRows_wires_subset xs dst pad carry hd (Or.inr hp) (by omega)
  have top := signedSquareTop_wires_subset xs dst
  have diagSub := mappedSub_wires_subset (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin
  have diagAdd := mappedAdd_wires_subset (mappedDiagonal xs) dst (carry.take (dst.length-1)) cin
  have ds : wires (mappedDiagSub xs dst carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := diagSub hq
    rw [mappedDiagonal_wires] at h
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    have hs : q∈xs.take (xs.length-1) → q∈xs := List.mem_of_mem_take
    have hcarry : q∈carry.take (dst.length-1) → q∈carry := List.mem_of_mem_take
    tauto
  have da : wires (mappedDiagAdd xs dst carry cin)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := diagAdd hq
    rw [mappedDiagonal_wires] at h
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    have hs : q∈xs.take (xs.length-1) → q∈xs := List.mem_of_mem_take
    have hcarry : q∈carry.take (dst.length-1) → q∈carry := List.mem_of_mem_take
    tauto
  have r1 : wires (signedSquareRows xs dst pad carry)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := rows.1 hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have r2 : wires (signedSquareRowsClear xs dst pad carry)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := rows.2 hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  have t : wires (signedSquareTop xs dst)⊆(xs++dst++pad++carry++[cin]).toFinset := by
    intro q hq
    have h := top hq
    simp only [List.mem_toFinset,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at h ⊢
    tauto
  constructor <;> intro q hq
  · simp only [mappedSignedSquare,wires_append,Finset.mem_union] at hq
    tauto
  · simp only [mappedSignedSquareClear,wires_append,Finset.mem_union] at hq
    tauto

theorem copyRegister_wires_subset (control : Option Wire) (src dst : List Wire) :
    wires (copyRegister control src dst)⊆(control.toList++src++dst).toFinset := by
  induction src generalizing dst with
  | nil => simp [copyRegister,wires]
  | cons x xs ih =>
    cases dst with
    | nil => simp [copyRegister,wires]
    | cons y ys =>
      intro q hq
      simp only [copyRegister,wires_append,Finset.mem_union] at hq
      rcases hq with head|tail
      · cases control <;> simp [copyGate,wires,Instr.wires] at head ⊢ <;> tauto
      · have h := ih ys tail
        simp only [List.mem_toFinset,List.mem_append,List.mem_cons] at h ⊢
        tauto

theorem MeasuredCanonicalModLayout.program_wires_subset (L : MeasuredCanonicalModLayout) (c p : Nat) :
    ECDSAAdd.wires (L.program c p)⊆L.wires.toFinset := by
  have sum := mappedAdd_wires_subset
    (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)]) L.extended L.carry L.cin
  have read : mappedWires (mappedRead L.src false++[({wire:=none,flip:=false} : MappedBit)])=L.src := by
    simp only [mappedWires,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,Option.toList_none,List.nil_append,List.append_nil]
    exact mappedRead_wires L.src false
  rw [read] at sum
  have ge := compareConstantGe_wires_subset L.out (L.carry.take (L.out.length-1)) L.cin L.flag p
  have add := mappedConstAdd_wires_subset (some L.flag) L.extended L.carry L.cin c
  have erase := eraseLtChain_wires_subset L.out L.src (L.carry.take (L.out.length-1)) L.cin L.flag
  have embed1 : (L.src++L.extended++L.carry++[L.cin]).toFinset⊆L.wires.toFinset := by
    intro q hq
    simp [MeasuredCanonicalModLayout.wires,MeasuredCanonicalModLayout.extended] at hq ⊢
    tauto
  have embed2 : (L.out++L.carry.take (L.out.length-1)++[L.cin,L.flag]).toFinset⊆L.wires.toFinset := by
    intro q hq
    have ht : q∈L.carry.take (L.out.length-1) → q∈L.carry := List.mem_of_mem_take
    simp [MeasuredCanonicalModLayout.wires] at hq ⊢
    tauto
  have embed3 : ((some L.flag).toList++L.extended++L.carry++[L.cin]).toFinset⊆L.wires.toFinset := by
    intro q hq
    simp [MeasuredCanonicalModLayout.wires,MeasuredCanonicalModLayout.extended] at hq ⊢
    tauto
  have embed4 : (L.out++L.src++L.carry.take (L.out.length-1)++[L.cin,L.flag]).toFinset⊆L.wires.toFinset := by
    intro q hq
    have ht : q∈L.carry.take (L.out.length-1) → q∈L.carry := List.mem_of_mem_take
    simp [MeasuredCanonicalModLayout.wires] at hq ⊢
    tauto
  have s1 := sum.trans embed1
  have s2 := ge.trans embed2
  have s3 := add.trans embed3
  have s4 := erase.trans embed4
  intro q hq
  simp only [MeasuredCanonicalModLayout.program,MeasuredCanonicalModLayout.sum,
    wires_append,Finset.mem_union] at hq
  have cx1 : q∈ECDSAAdd.wires [Instr.CX L.high L.flag] → q∈L.wires.toFinset := by
    simp [ECDSAAdd.wires,Instr.wires,MeasuredCanonicalModLayout.wires]
    tauto
  have cx2 : q∈ECDSAAdd.wires [Instr.CX L.flag L.high] → q∈L.wires.toFinset := by
    simp [ECDSAAdd.wires,Instr.wires,MeasuredCanonicalModLayout.wires]
    tauto
  rcases hq with ((((hq|hq)|hq)|hq)|hq)|hq
  · exact s1 hq
  · exact s2 hq
  · exact cx1 hq
  · exact s3 hq
  · exact cx2 hq
  · exact s4 hq

end ECDSAAdd.Arithmetic
