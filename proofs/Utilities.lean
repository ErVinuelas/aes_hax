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

def set_elem (st : Vector u16 8) (elem_indx : Nat) (new_elem : BitVec 8) : (Vector u16 8) :=
  (8 : Nat).fold (init := zero_array) fun bt_indx _ acc =>
    let map_bit := st[bt_indx].toBitVec
    let bt := BitVec.zeroExtend 16 ((new_elem >>> bt_indx) &&& 1)
    let clear_map := (map_bit &&& ~~~((1 : BitVec 16) <<< elem_indx))
    let new_map := clear_map ||| (bt <<< elem_indx)
    (Vector.set acc bt_indx (UInt16.ofBitVec new_map))

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
