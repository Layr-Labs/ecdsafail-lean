import ECDSAAdd.Arithmetic.PoolLayout

namespace ECDSAAdd.Arithmetic

private theorem indexedWord_eq (r : List Wire) (n : Nat) (h : r.length=n) :
    List.ofFn (fun i : Fin n => r.getD i 0)=r := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hj
    simp [List.getD,List.getElem?_eq_getElem hj]

private theorem block_ofFn (w : Nat → Wire) (start n : Nat) :
    List.ofFn (fun i : Fin n => w (start+i))=wireBlock w start n := by
  apply List.ext_getElem
  · simp [wireBlock]
  · intro i hi hj
    simp [wireBlock]

/-- 模减法直接连接调用方寄存器，五个工作字及两根进位共用池的前 1287 位。 -/
def poolSub (w : Nat → Wire) (x y out : List Wire) : ModLayout :=
  modPorts (n:=256) (fun i => x.getD i 0) (fun i => y.getD i 0) (fun i => out.getD i 0)
    (fun j i => w (257*j+i)) (w 1285) (w 1286)

theorem poolSub_inputs (w : Nat → Wire) (x y out : List Wire)
    (hx : x.length=257) (hy : y.length=257) (ho : out.length=257) :
    (poolSub w x y out).x=x ∧ (poolSub w x y out).y=y ∧ (poolSub w x y out).out=out := by
  have h := modPorts_inputs (n:=256) (fun i => x.getD i 0) (fun i => y.getD i 0)
    (fun i => out.getD i 0) (fun j i => w (257*j+i)) (w 1285) (w 1286)
  simpa only [indexedWord_eq x 257 hx,indexedWord_eq y 257 hy,indexedWord_eq out 257 ho] using h

theorem poolSub_work (w : Nat → Wire) (x y out : List Wire) :
    (poolSub w x y out).work=wireBlock w 0 1287 := by
  rw [poolSub,modPorts_work]
  simp only [Fin.val_zero,Fin.val_one, Nat.mul_zero,Nat.mul_one]
  rw [block_ofFn,block_ofFn,block_ofFn,block_ofFn,block_ofFn]
  change (wireBlock w 0 257++wireBlock w 257 257++wireBlock w 514 257++
    wireBlock w 771 257++wireBlock w 1028 257++wireBlock w 1285 2)=_
  rw [wireBlock_append w 0 257 257,wireBlock_append w 0 514 257,
    wireBlock_append w 0 771 257,wireBlock_append w 0 1028 257,wireBlock_append w 0 1285 2]

theorem poolSub_width (w : Nat → Wire) (x y out : List Wire) :
    (poolSub w x y out).width=256 := modPorts_width _ _ _ _ _ _

theorem poolSub_nodup (w : Nat → Wire) (x y out : List Wire)
    (hx : x.length=257) (hy : y.length=257) (ho : out.length=257)
    (h : (x++y++out++wireBlock w 0 1287).Nodup) : (poolSub w x y out).wires.Nodup := by
  apply (ModLayout.interface_perm _).nodup_iff.mp
  rw [(poolSub_inputs w x y out hx hy ho).1,(poolSub_inputs w x y out hx hy ho).2.1,
    (poolSub_inputs w x y out hx hy ho).2.2,poolSub_work]
  exact h

end ECDSAAdd.Arithmetic
