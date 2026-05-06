import Lean
import Hax

open Lean Meta Elab Tactic

/--
Generates a name based on an index (0 -> a, 1 -> b, etc.)
-/
def getAutoName (i : Nat) : Name :=
    s!"var_{i}" |>.toName

syntax (name := renameAutoN) "rename_auto_n " num : tactic

@[tactic renameAutoN]
def evalRenameAutoN : Tactic := fun stx => do
  -- Parse the number 'n' from the tactic call
  let n := stx[1].isNatLit?.getD 0

  liftMetaTactic fun mvarId => do
    let lctx ← getLCtx
    let mut mvarId := mvarId
    let mut foundCount := 0

    for ldecl in lctx do
      if foundCount >= n then break

      -- Check if the hypothesis is inaccessible (has macro scopes or is a dagger/internal name)
      if ldecl.userName.hasMacroScopes || ldecl.userName.toString.startsWith "✝" then
        let newName := getAutoName foundCount
        mvarId ← mvarId.rename ldecl.fvarId newName
        foundCount := foundCount + 1

    return [mvarId]

--Some functions to work with how the AES matrix is represented.

def zero_array : Vector u16 8 :=
  Vector.replicate 8 (UInt16.ofBitVec <| BitVec.zero 16)

def some_array : RustArray u16 8 :=
  RustArray.ofVec (#v[
    0b1000000000000000,
    0b0000000000000000,
    0b0000000000000000,
    0b0000000000000000,
    0b0000000000000000,
    0b0000000000000000,
    0b1000000000000000,
    0b0000000000000000])

-- Get an element from the bit map
def get_elem (st : Vector u16 8) (elem_indx : Nat) (h : elem_indx < 16) : BitVec 8 :=
  (8 : Nat).fold (init := 0) fun bt_indx _ elem =>
    let elem_indx_fin := elem_indx
    let elem_bt_indx := (st[bt_indx].toBitVec >>> (elem_indx_fin) &&& 1).setWidth 8
    elem ||| (elem_bt_indx <<< bt_indx : BitVec 8)

def get_elem_bv (st : Vector u16 8) (elem_indx : BitVec 4) : BitVec 8 :=
  let shift : BitVec 16 :=
    if elem_indx == 0#4  then 15#16
    else if elem_indx == 1#4  then 14#16
    else if elem_indx == 2#4  then 13#16
    else if elem_indx == 3#4  then 12#16
    else if elem_indx == 4#4  then 11#16
    else if elem_indx == 5#4  then 10#16
    else if elem_indx == 6#4  then  9#16
    else if elem_indx == 7#4  then  8#16
    else if elem_indx == 8#4  then  7#16
    else if elem_indx == 9#4  then  6#16
    else if elem_indx == 10#4 then  5#16
    else if elem_indx == 11#4 then  4#16
    else if elem_indx == 12#4 then  3#16
    else if elem_indx == 13#4 then  2#16
    else if elem_indx == 14#4 then  1#16
    else                           0#16
  let b0 := ((st[0].toBitVec >>> shift) &&& 1#16).extractLsb 0 0
  let b1 := ((st[1].toBitVec >>> shift) &&& 1#16).extractLsb 0 0
  let b2 := ((st[2].toBitVec >>> shift) &&& 1#16).extractLsb 0 0
  let b3 := ((st[3].toBitVec >>> shift) &&& 1#16).extractLsb 0 0
  let b4 := ((st[4].toBitVec >>> shift) &&& 1#16).extractLsb 0 0
  let b5 := ((st[5].toBitVec >>> shift) &&& 1#16).extractLsb 0 0
  let b6 := ((st[6].toBitVec >>> shift) &&& 1#16).extractLsb 0 0
  let b7 := ((st[7].toBitVec >>> shift) &&& 1#16).extractLsb 0 0

  (0#8
    ||| (0#7 ++ b0)
    ||| (0#6 ++ b1 ++ 0#1)
    ||| (0#5 ++ b2 ++ 0#2)
    ||| (0#4 ++ b3 ++ 0#3)
    ||| (0#3 ++ b4 ++ 0#4)
    ||| (0#2 ++ b5 ++ 0#5)
    ||| (0#1 ++ b6 ++ 0#6)
    ||| (b7 ++ 0#7))

def set_elem (st : Vector u16 8) (elem_indx : Nat) (new_elem : BitVec 8) : (Vector u16 8) :=
  (8 : Nat).fold (init := zero_array) fun bt_indx _ acc =>
    let map_bit := st[bt_indx].toBitVec
    let bt := BitVec.zeroExtend 16 ((new_elem >>> bt_indx) &&& 1)
    let clear_map := (map_bit &&& ~~~((1 : BitVec 16) <<< elem_indx))
    let new_map := clear_map ||| (bt <<< elem_indx)
    (Vector.set acc bt_indx (UInt16.ofBitVec new_map))

def set_elem_bv (st : Vector u16 8) (elem_indx : BitVec 4) (new_elem : BitVec 8) : Vector u16 8 :=
  let shift : BitVec 16 :=
    if elem_indx == 0#4  then 15#16
    else if elem_indx == 1#4  then 14#16
    else if elem_indx == 2#4  then 13#16
    else if elem_indx == 3#4  then 12#16
    else if elem_indx == 4#4  then 11#16
    else if elem_indx == 5#4  then 10#16
    else if elem_indx == 6#4  then  9#16
    else if elem_indx == 7#4  then  8#16
    else if elem_indx == 8#4  then  7#16
    else if elem_indx == 9#4  then  6#16
    else if elem_indx == 10#4 then  5#16
    else if elem_indx == 11#4 then  4#16
    else if elem_indx == 12#4 then  3#16
    else if elem_indx == 13#4 then  2#16
    else if elem_indx == 14#4 then  1#16
    else                           0#16
  let mask : BitVec 16 := 1#16 <<< shift
  let bt0 := (0#15 ++ (new_elem &&& 0x01#8).extractLsb 0 0) <<< shift
  let bt1 := (0#15 ++ ((new_elem >>> 1#8) &&& 0x01#8).extractLsb 0 0) <<< shift
  let bt2 := (0#15 ++ ((new_elem >>> 2#8) &&& 0x01#8).extractLsb 0 0) <<< shift
  let bt3 := (0#15 ++ ((new_elem >>> 3#8) &&& 0x01#8).extractLsb 0 0) <<< shift
  let bt4 := (0#15 ++ ((new_elem >>> 4#8) &&& 0x01#8).extractLsb 0 0) <<< shift
  let bt5 := (0#15 ++ ((new_elem >>> 5#8) &&& 0x01#8).extractLsb 0 0) <<< shift
  let bt6 := (0#15 ++ ((new_elem >>> 6#8) &&& 0x01#8).extractLsb 0 0) <<< shift
  let bt7 := (0#15 ++ ((new_elem >>> 7#8) &&& 0x01#8).extractLsb 0 0) <<< shift
  let new0 := (st[0].toBitVec &&& ~~~mask) ||| bt0
  let new1 := (st[1].toBitVec &&& ~~~mask) ||| bt1
  let new2 := (st[2].toBitVec &&& ~~~mask) ||| bt2
  let new3 := (st[3].toBitVec &&& ~~~mask) ||| bt3
  let new4 := (st[4].toBitVec &&& ~~~mask) ||| bt4
  let new5 := (st[5].toBitVec &&& ~~~mask) ||| bt5
  let new6 := (st[6].toBitVec &&& ~~~mask) ||| bt6
  let new7 := (st[7].toBitVec &&& ~~~mask) ||| bt7
  #v[UInt16.ofBitVec new0, UInt16.ofBitVec new1, UInt16.ofBitVec new2, UInt16.ofBitVec new3,
     UInt16.ofBitVec new4, UInt16.ofBitVec new5, UInt16.ofBitVec new6, UInt16.ofBitVec new7]

set_option maxRecDepth 100000
theorem set_elem_th_3 (el : Nat) (h : el < 16) (new : BitVec 8) :
  let vec_set := (set_elem zero_array el new)
  get_elem vec_set el h = new := by
  unfold get_elem set_elem zero_array
  simp
  match el with
  | n + 16 => omega
  | 0 | 1 | 2 | 3 | 4| 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
    bv_decide
