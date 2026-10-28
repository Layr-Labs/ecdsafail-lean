import ECDSAAdd.Arithmetic.SquareSubLayout

namespace ECDSAAdd.Arithmetic
namespace SquareSubLayout

/-- §28 固定切片，仅使用既有 P 的前2217位。 -/
def fromPool (x out pool : List Wire) : SquareSubLayout :=
  { x := x,out := out,a := pool.take 256,d := (pool.drop 256).take 256,
    r := (pool.drop 512).take 289,z := (pool.drop 801).take 512,
    mask := (pool.drop 1313).take 256,carry := (pool.drop 1569).take 383,
    cin := pool.getD 1952 0,pad := (pool.drop 1953).take 256,
    b := pool.getD 2209 0,flag := pool.getD 2210 0,sourceHigh := pool.getD 2211 0,
    outputHigh := pool.getD 2212 0,constantHigh := pool.getD 2213 0,
    maskHigh := pool.getD 2214 0,layoutFlag := pool.getD 2215 0,sumHigh := pool.getD 2216 0 }

theorem fromPool_widths (x out pool : List Wire) (hx : x.length=256)
    (ho : out.length=256) (hp : 2217≤pool.length) : (fromPool x out pool).Widths := by
  constructor <;> simp only [fromPool,List.length_take,List.length_drop] <;> omega

private theorem slice_append (pool : List Wire) (a n m : Nat) :
    (pool.drop a).take n++(pool.drop (a+n)).take m=(pool.drop a).take (n+m) := by
  rw [List.take_add,List.drop_drop]

private theorem single_slice (pool : List Wire) (a : Nat) (ha : a<pool.length) :
    [pool.getD a 0]=(pool.drop a).take 1 := by
  have he : pool.getD a 0=pool[a] := by
    simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem ha]
  rw [he]
  conv_rhs => rw [List.drop_eq_getElem_cons ha]
  rfl

theorem fromPool_work (x out pool : List Wire) (hp : 2217≤pool.length) :
    (fromPool x out pool).work=pool.take 2217 := by
  have last : [pool.getD 2209 0,pool.getD 2210 0,pool.getD 2211 0,pool.getD 2212 0,
      pool.getD 2213 0,pool.getD 2214 0,pool.getD 2215 0,pool.getD 2216 0]=
      (pool.drop 2209).take 8 := by
    have h0 := single_slice pool 2209 (by omega)
    have h1 := single_slice pool 2210 (by omega)
    have h2 := single_slice pool 2211 (by omega)
    have h3 := single_slice pool 2212 (by omega)
    have h4 := single_slice pool 2213 (by omega)
    have h5 := single_slice pool 2214 (by omega)
    have h6 := single_slice pool 2215 (by omega)
    have h7 := single_slice pool 2216 (by omega)
    calc
      _ = [pool.getD 2209 0]++[pool.getD 2210 0]++[pool.getD 2211 0]++[pool.getD 2212 0]++
          [pool.getD 2213 0]++[pool.getD 2214 0]++[pool.getD 2215 0]++[pool.getD 2216 0] := rfl
      _ = _ := by rw [h0,h1,h2,h3,h4,h5,h6,h7];
                  repeat rw [slice_append]
  simp only [work,fromPool]
  rw [last,single_slice pool 1952 (by omega)]
  change (pool.drop 0).take 256++(pool.drop 256).take 256++(pool.drop 512).take 289++
    (pool.drop 801).take 512++(pool.drop 1313).take 256++(pool.drop 1569).take 383++
    (pool.drop 1952).take 1++(pool.drop 1953).take 256++(pool.drop 2209).take 8=pool.take 2217
  repeat rw [slice_append]
  rfl

theorem fromPool_nodup (x out pool : List Wire) (hp : 2217≤pool.length)
    (hn : (x++out++pool).Nodup) : (fromPool x out pool).wires.Nodup := by
  change (x++out++(fromPool x out pool).work).Nodup
  rw [fromPool_work x out pool hp]
  exact ((List.Sublist.refl (x++out)).append (List.take_sublist 2217 pool)).nodup hn

end SquareSubLayout
end ECDSAAdd.Arithmetic
