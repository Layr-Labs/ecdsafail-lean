import ECDSAAdd.Arithmetic.MeasuredMaskedAdder
import ECDSAAdd.Arithmetic.MontRotate
import ECDSAAdd.Arithmetic.Lookup
import ECDSAAdd.Arithmetic.InPlaceAdder
import ECDSAAdd.Math.Montgomery

namespace ECDSAAdd.Arithmetic

/-- 一个 Montgomery 段；另一段复用 table/mask/carry/pad/scratch，保留各自 acc/history/flag。 -/
structure MontStageLayout where
  acc : List Wire
  history : List Wire
  flag : Wire
  table : List Wire
  mask : List Wire
  carry : List Wire
  cin : Wire
  pad : List Wire
  scratch : List Wire

namespace MontStageLayout

def work (L : MontStageLayout) : List Wire :=
  L.table++L.mask++L.carry++[L.cin]++L.pad++L.scratch

def wires (L : MontStageLayout) : List Wire := L.acc++L.history++[L.flag]++L.work

structure Widths (L : MontStageLayout) : Prop where
  acc : L.acc.length=261
  history : L.history.length=256
  table : L.table.length=261
  mask : L.mask.length=261
  carry : L.carry.length=260
  pad : L.pad.length=5
  scratch : L.scratch.length=3

/-- 窗口 i 的独立四位记录。 -/
def record (L : MontStageLayout) (i : Nat) : List Wire := (L.history.drop (4*i)).take 4

/-- 移位源只用 x 的低256位，五根互异的零 pad 各出现一次。 -/
def source (L : MontStageLayout) (x : List Wire) (j : Nat) : List Wire :=
  L.pad.take j ++ x.take 256 ++ L.pad.drop j

end MontStageLayout

/-- 四位列表查表入口；空地址的语法分支被长度前提排除。 -/
def montLookup (L : MontStageLayout) (addr : List Wire) (K : Nat) : Program :=
  lookup (addr.headD L.flag) addr.tail L.scratch L.table (fun d => d*K)

/-- 查表值加进累加器，再用同一前向查表清空 table。 -/
def montLookupAdd (L : MontStageLayout) (addr : List Wire) (K : Nat) : Program :=
  montLookup L addr K ++ addInPlace L.table L.acc L.carry L.cin ++ montLookup L addr K

def montLookupSub (L : MontStageLayout) (addr : List Wire) (K : Nat) : Program :=
  montLookup L addr K ++ subInPlace L.table L.acc L.carry L.cin ++ montLookup L addr K

/-- 保存约减系数，加入 m*p 后物理右旋四位。 -/
def montReduce (L : MontStageLayout) (p i : Nat) : Program :=
  copyRegister none (L.acc.take 4) (L.record i) ++
  montLookupAdd L (L.record i) p ++ rotateRightBits L.acc 4

/-- 左旋恢复和，减去记录的 m*p，随后由恢复的低四位清记录。 -/
def montRestoreReduce (L : MontStageLayout) (p i : Nat) : Program :=
  rotateLeftBits L.acc 4 ++ montLookupSub L (L.record i) p ++
  copyRegister none (L.acc.take 4) (L.record i)

/-- 逐位加入一个变量四位窗口；控制值不改变门列。 -/
def montAddDigit (L : MontStageLayout) (x y : List Wire) (i : Nat) : Program :=
  (List.range 4).flatMap (fun j =>
    measuredMaskedAddInPlace (y.getD (4*i+j) L.flag) (L.source x j) L.mask L.acc L.carry L.cin)

/-- 按 j=3..0 执行前向减法，并非反转测量。 -/
def montSubDigit (L : MontStageLayout) (x y : List Wire) (i : Nat) : Program :=
  (List.range 4).reverse.flatMap (fun j =>
    measuredMaskedSubInPlace (y.getD (4*i+j) L.flag) (L.source x j) L.mask L.acc L.carry L.cin)

def montWindow (L : MontStageLayout) (x y : List Wire) (p i : Nat) : Program :=
  montAddDigit L x y i ++ montReduce L p i

def montRestoreWindow (L : MontStageLayout) (x y : List Wire) (p i : Nat) : Program :=
  montRestoreReduce L p i ++ montSubDigit L x y i

def constMontWindow (L : MontStageLayout) (y : List Wire) (p K i : Nat) : Program :=
  montLookupAdd L ((y.drop (4*i)).take 4) K ++ montReduce L p i

def constMontRestoreWindow (L : MontStageLayout) (y : List Wire) (p K i : Nat) : Program :=
  montRestoreReduce L p i ++ montLookupSub L ((y.drop (4*i)).take 4) K

def montConstantAdd (L : MontStageLayout) (K : Nat) : Program :=
  xorConstant L.table K ++ addInPlace L.table L.acc L.carry L.cin ++ xorConstant L.table K

def montConstantSub (L : MontStageLayout) (K : Nat) : Program :=
  xorConstant L.table K ++ subInPlace L.table L.acc L.carry L.cin ++ xorConstant L.table K

/-- 减 p 后保存借位，条件加回 p；保留 flag 到清理阶段。 -/
def montNormalize (L : MontStageLayout) (p : Nat) : Program :=
  montConstantSub L p ++ [.CX (L.acc.getD 260 L.flag) L.flag] ++
  maskedAddConst L.flag L.table L.acc L.carry L.cin p

/-- 先按保留借位减 p，再清 flag、加 p，恢复未经约减的累加器。 -/
def montDenormalize (L : MontStageLayout) (p : Nat) : Program :=
  maskedSubConst L.flag L.table L.acc L.carry L.cin p ++
  [.CX (L.acc.getD 260 L.flag) L.flag] ++ montConstantAdd L p

def montPrepareRounds (L : MontStageLayout) (x y : List Wire) (p : Nat) : Nat → Program
  | 0 => []
  | k+1 => montPrepareRounds L x y p k ++ montWindow L x y p k

def montRestoreRounds (L : MontStageLayout) (x y : List Wire) (p : Nat) : Nat → Program
  | 0 => []
  | k+1 => montRestoreWindow L x y p k ++ montRestoreRounds L x y p k

def constPrepareRounds (L : MontStageLayout) (y : List Wire) (p K : Nat) : Nat → Program
  | 0 => []
  | k+1 => constPrepareRounds L y p K k ++ constMontWindow L y p K k

def constRestoreRounds (L : MontStageLayout) (y : List Wire) (p K : Nat) : Nat → Program
  | 0 => []
  | k+1 => constMontRestoreWindow L y p K k ++ constRestoreRounds L y p K k

def montPrepare (L : MontStageLayout) (x y : List Wire) (p : Nat) : Program :=
  montPrepareRounds L x y p 64 ++ montNormalize L p

def montRestore (L : MontStageLayout) (x y : List Wire) (p : Nat) : Program :=
  montDenormalize L p ++ montRestoreRounds L x y p 64

def constPrepare (L : MontStageLayout) (y : List Wire) (p K : Nat) : Program :=
  constPrepareRounds L y p K 64 ++ montNormalize L p

def constRestore (L : MontStageLayout) (y : List Wire) (p K : Nat) : Program :=
  montDenormalize L p ++ constRestoreRounds L y p K 64

end ECDSAAdd.Arithmetic
