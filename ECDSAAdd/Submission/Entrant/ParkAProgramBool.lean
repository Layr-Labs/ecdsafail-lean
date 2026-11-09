import ECDSAAdd.Framework.Syntax

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
namespace ParkAProgramBool
open ECDSAAdd

-- Direct Boolean data comparison: no DecidableEq on Correction, Instr or Program.
def corrEq : Correction → Correction → Bool
 | .Z a, .Z b => a==b
 | .CZ a b, .CZ c d => (a==c)&&(b==d)
 | _,_ => false

theorem corrEq_iff (a b : Correction) : corrEq a b=true ↔ a=b := by
 cases a <;> cases b <;> simp [corrEq]

def corrsEq : List Correction → List Correction → Bool
 | [],[] => true
 | a::as,b::bs => corrEq a b && corrsEq as bs
 | _,_ => false

theorem corrsEq_iff (as bs : List Correction) : corrsEq as bs=true ↔ as=bs := by
 induction as generalizing bs with
 | nil => cases bs <;> simp [corrsEq]
 | cons a as ih => cases bs <;> simp [corrsEq,corrEq_iff,ih]

def instrEq : Instr → Instr → Bool
 | .X a, .X b => a==b
 | .CX a b, .CX c d => (a==c)&&(b==d)
 | .CCX a b c, .CCX d e f => (a==d)&&(b==e)&&(c==f)
 | .measureX a z o, .measureX b z' o' => (a==b)&&corrsEq z z'&&corrsEq o o'
 | _,_ => false

theorem instrEq_iff (a b : Instr) : instrEq a b=true ↔ a=b := by
 cases a <;> cases b <;> simp [instrEq,corrsEq_iff,and_assoc]

def programEq : Program → Program → Bool
 | [],[] => true
 | a::as,b::bs => instrEq a b && programEq as bs
 | _,_ => false

theorem programEq_iff (a b : Program) : programEq a b=true ↔ a=b := by
 induction a generalizing b with
 | nil => cases b <;> simp [programEq]
 | cons a as ih => cases b <;> simp [programEq,instrEq_iff,ih]

theorem programEq_sound (a b : Program) (h : programEq a b=true) : a=b :=
 (programEq_iff a b).mp h

#print axioms corrEq_iff
#print axioms corrsEq_iff
#print axioms instrEq_iff
#print axioms programEq_iff
#print axioms programEq_sound
end ParkAProgramBool

namespace ParkAOptionBool
open ECDSAAdd ParkAProgramBool

def optionEq : Option Program → Option Program → Bool
 | none,none => true
 | some p,some q => programEq p q
 | _,_ => false

theorem optionEq_iff (a b : Option Program) : optionEq a b=true ↔ a=b := by
 cases a <;> cases b <;> simp [optionEq,programEq_iff]

theorem optionEq_sound (a b : Option Program) (h : optionEq a b=true) : a=b :=
 (optionEq_iff a b).mp h

#print axioms optionEq_iff
#print axioms optionEq_sound
end ParkAOptionBool
