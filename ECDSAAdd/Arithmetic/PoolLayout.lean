import ECDSAAdd.Arithmetic.ModularPorts

namespace ECDSAAdd.Arithmetic

/-- 工作池的连续切片。w 把池内偏移映射到调用方线路。 -/
def wireBlock (w : Nat → Wire) (start count : Nat) : List Wire :=
  (List.range' start count).map w

theorem wireBlock_append (w : Nat → Wire) (start a b : Nat) :
    wireBlock w start a++wireBlock w (start+a) b=wireBlock w start (a+b) := by
  simp only [wireBlock,← List.map_append,← List.range'_append,Nat.one_mul]

theorem wireBlock_length (w : Nat → Wire) (start count : Nat) :
    (wireBlock w start count).length=count := by simp [wireBlock]

theorem wireBlock_flatMap (w : Nat → Wire) (start width count : Nat) :
    ((List.range count).flatMap (fun i => wireBlock w (start+width*i) width))=
      wireBlock w start (width*count) := by
  induction count with
  | zero => simp [wireBlock]
  | succ count ih =>
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,ih]
    rw [wireBlock_append,Nat.mul_succ]

def poolModBit (w : Nat → Wire) (start : Nat) : ModBit :=
  ⟨w start,w (start+1),w (start+2),w (start+3),w (start+4),
    w (start+5),w (start+6),w (start+7)⟩

def poolMod (w : Nat → Wire) (start width : Nat) : ModLayout :=
  ⟨(List.range width).map (fun i => poolModBit w (start+2+8*i)),
    poolModBit w (start+2+8*width),w start,w (start+1)⟩

theorem poolMod_bits (w : Nat → Wire) (start width : Nat) :
    (poolMod w start width).bits=
      (List.range (width+1)).map (fun i => poolModBit w (start+2+8*i)) := by
  simp [poolMod,ModLayout.bits,List.range_succ]

theorem poolMod_width (w : Nat → Wire) (start width : Nat) :
    (poolMod w start width).width=width := by simp [poolMod,ModLayout.width]

theorem poolModBit_wires (w : Nat → Wire) (start : Nat) :
    (poolModBit w start).all=wireBlock w start 8 := by
  simp [poolModBit,ModBit.all,wireBlock,List.range',Nat.add_assoc]

theorem poolMod_wires (w : Nat → Wire) (start width : Nat) :
    (poolMod w start width).wires=wireBlock w start (2+8*(width+1)) := by
  simp only [ModLayout.wires,poolMod_bits,List.flatMap_map,poolModBit_wires]
  rw [wireBlock_flatMap]
  change w start::w (start+1)::wireBlock w (start+2) (8*(width+1))=_
  rw [← wireBlock_append]
  rfl

end ECDSAAdd.Arithmetic
