import ECDSAAdd.Arithmetic.ModularFrame
import Mathlib.Data.List.OfFn

namespace ECDSAAdd.Arithmetic

/-- 模加减直接使用调用方的输入输出位；工作区分成五个同宽寄存器和两根进位线。 -/
def modPortBit {n : Nat} (x y out : Fin (n+1) → Wire)
    (work : Fin 5 → Fin (n+1) → Wire) (i : Fin (n+1)) : ModBit :=
  ⟨x i,y i,work 0 i,work 1 i,work 2 i,out i,work 3 i,work 4 i⟩

def modPorts {n : Nat} (x y out : Fin (n+1) → Wire)
    (work : Fin 5 → Fin (n+1) → Wire) (cinSum cinDiff : Wire) : ModLayout :=
  ⟨List.ofFn (fun i : Fin n => modPortBit x y out work i.castSucc),
    modPortBit x y out work (Fin.last n),cinSum,cinDiff⟩

theorem modPorts_width {n : Nat} (x y out : Fin (n+1) → Wire)
    (work : Fin 5 → Fin (n+1) → Wire) (a b : Wire) :
    (modPorts x y out work a b).width=n := by
  simp [modPorts,ModLayout.width]

theorem modPorts_bits {n : Nat} (x y out : Fin (n+1) → Wire)
    (work : Fin 5 → Fin (n+1) → Wire) (a b : Wire) :
    (modPorts x y out work a b).bits=List.ofFn (modPortBit x y out work) := by
  rw [List.ofFn_succ']
  simp only [modPorts,ModLayout.bits,List.concat_eq_append]

theorem modPorts_inputs {n : Nat} (x y out : Fin (n+1) → Wire)
    (work : Fin 5 → Fin (n+1) → Wire) (a b : Wire) :
    (modPorts x y out work a b).x=List.ofFn x ∧
    (modPorts x y out work a b).y=List.ofFn y ∧
    (modPorts x y out work a b).out=List.ofFn out := by
  simp only [ModLayout.x,ModLayout.y,ModLayout.out,ModLayout.reg,modPorts_bits,
    List.map_ofFn,modPortBit,ModBit.get,Function.comp_def,and_self]

theorem modPorts_work {n : Nat} (x y out : Fin (n+1) → Wire)
    (work : Fin 5 → Fin (n+1) → Wire) (a b : Wire) :
    (modPorts x y out work a b).work=
      List.ofFn (work 0)++List.ofFn (work 1)++List.ofFn (work 2)++
      List.ofFn (work 3)++List.ofFn (work 4)++[a,b] := by
  simp only [ModLayout.work,ModLayout.reg,modPorts_bits,List.map_ofFn,modPortBit,ModBit.get,Function.comp_def]
  rfl


end ECDSAAdd.Arithmetic
