
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Utilities
import gf8_lsb

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace aes_core.mix_columns_state

@[spec]
def mix_columns_state (st : (RustArray u16 8)) : RustM (RustArray u16 8) := do
  let last_col : u16 := (0 : u16);
  let ⟨last_col, st⟩ ←
    (rust_primitives.hax.folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun ⟨last_col, st⟩ _ => (do (pure true) : RustM Bool))
      (rust_primitives.hax.Tuple2.mk last_col st)
      (fun ⟨last_col, st⟩ i =>
        (do
        let col : u16 ←
          ((← st[i]_?)
            ^^^? (← ((← ((← ((← st[i]_?) &&&? (61166 : u16))) >>>? (1 : i32)))
              |||? (← ((← ((← st[i]_?) &&&? (4369 : u16))) <<<? (3 : i32))))));
        let st : (RustArray u16 8) ←
          (rust_primitives.hax.monomorphized_update_at.update_at_usize
            st
            i
            (← ((← ((← ((← st[i]_?) ^^^? last_col)) ^^^? col))
              ^^^? (← ((← ((← (col &&&? (52428 : u16))) >>>? (2 : i32)))
                |||? (← ((← (col &&&? (13107 : u16))) <<<? (2 : i32))))))));
        let last_col : u16 := col;
        (pure (rust_primitives.hax.Tuple2.mk last_col st)) :
        RustM (rust_primitives.hax.Tuple2 u16 (RustArray u16 8)))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (0 : usize)
      (← ((← st[(0 : usize)]_?) ^^^? last_col)));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (1 : usize)
      (← ((← st[(1 : usize)]_?) ^^^? last_col)));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (3 : usize)
      (← ((← st[(3 : usize)]_?) ^^^? last_col)));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (4 : usize)
      (← ((← st[(4 : usize)]_?) ^^^? last_col)));
  (pure st)

set_option maxRecDepth 1000
@[spec]
def mix_columns_state_unrolled (__st__ : (RustArray u16 8)) :
    RustM (RustArray u16 8) := do
  let col0 : u16 ←
    ((← __st__[(0 : usize)]_?)
      ^^^? (← ((← ((← ((← __st__[(0 : usize)]_?) &&&? (61166 : u16)))
          >>>? (1 : i32)))
        |||? (← ((← ((← __st__[(0 : usize)]_?) &&&? (4369 : u16)))
          <<<? (3 : i32))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (0 : usize)
      (← ((← ((← ((← __st__[(0 : usize)]_?) ^^^? (0 : u16))) ^^^? col0))
        ^^^? (← ((← ((← (col0 &&&? (52428 : u16))) >>>? (2 : i32)))
          |||? (← ((← (col0 &&&? (13107 : u16))) <<<? (2 : i32))))))));
  let col1 : u16 ←
    ((← __st__[(1 : usize)]_?)
      ^^^? (← ((← ((← ((← __st__[(1 : usize)]_?) &&&? (61166 : u16)))
          >>>? (1 : i32)))
        |||? (← ((← ((← __st__[(1 : usize)]_?) &&&? (4369 : u16)))
          <<<? (3 : i32))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (1 : usize)
      (← ((← ((← ((← __st__[(1 : usize)]_?) ^^^? col0)) ^^^? col1))
        ^^^? (← ((← ((← (col1 &&&? (52428 : u16))) >>>? (2 : i32)))
          |||? (← ((← (col1 &&&? (13107 : u16))) <<<? (2 : i32))))))));
  let col2 : u16 ←
    ((← __st__[(2 : usize)]_?)
      ^^^? (← ((← ((← ((← __st__[(2 : usize)]_?) &&&? (61166 : u16)))
          >>>? (1 : i32)))
        |||? (← ((← ((← __st__[(2 : usize)]_?) &&&? (4369 : u16)))
          <<<? (3 : i32))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (2 : usize)
      (← ((← ((← ((← __st__[(2 : usize)]_?) ^^^? col1)) ^^^? col2))
        ^^^? (← ((← ((← (col2 &&&? (52428 : u16))) >>>? (2 : i32)))
          |||? (← ((← (col2 &&&? (13107 : u16))) <<<? (2 : i32))))))));
  let col3 : u16 ←
    ((← __st__[(3 : usize)]_?)
      ^^^? (← ((← ((← ((← __st__[(3 : usize)]_?) &&&? (61166 : u16)))
          >>>? (1 : i32)))
        |||? (← ((← ((← __st__[(3 : usize)]_?) &&&? (4369 : u16)))
          <<<? (3 : i32))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (3 : usize)
      (← ((← ((← ((← __st__[(3 : usize)]_?) ^^^? col2)) ^^^? col3))
        ^^^? (← ((← ((← (col3 &&&? (52428 : u16))) >>>? (2 : i32)))
          |||? (← ((← (col3 &&&? (13107 : u16))) <<<? (2 : i32))))))));
  let col4 : u16 ←
    ((← __st__[(4 : usize)]_?)
      ^^^? (← ((← ((← ((← __st__[(4 : usize)]_?) &&&? (61166 : u16)))
          >>>? (1 : i32)))
        |||? (← ((← ((← __st__[(4 : usize)]_?) &&&? (4369 : u16)))
          <<<? (3 : i32))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (4 : usize)
      (← ((← ((← ((← __st__[(4 : usize)]_?) ^^^? col3)) ^^^? col4))
        ^^^? (← ((← ((← (col4 &&&? (52428 : u16))) >>>? (2 : i32)))
          |||? (← ((← (col4 &&&? (13107 : u16))) <<<? (2 : i32))))))));
  let col5 : u16 ←
    ((← __st__[(5 : usize)]_?)
      ^^^? (← ((← ((← ((← __st__[(5 : usize)]_?) &&&? (61166 : u16)))
          >>>? (1 : i32)))
        |||? (← ((← ((← __st__[(5 : usize)]_?) &&&? (4369 : u16)))
          <<<? (3 : i32))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (5 : usize)
      (← ((← ((← ((← __st__[(5 : usize)]_?) ^^^? col4)) ^^^? col5))
        ^^^? (← ((← ((← (col5 &&&? (52428 : u16))) >>>? (2 : i32)))
          |||? (← ((← (col5 &&&? (13107 : u16))) <<<? (2 : i32))))))));
  let col6 : u16 ←
    ((← __st__[(6 : usize)]_?)
      ^^^? (← ((← ((← ((← __st__[(6 : usize)]_?) &&&? (61166 : u16)))
          >>>? (1 : i32)))
        |||? (← ((← ((← __st__[(6 : usize)]_?) &&&? (4369 : u16)))
          <<<? (3 : i32))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (6 : usize)
      (← ((← ((← ((← __st__[(6 : usize)]_?) ^^^? col5)) ^^^? col6))
        ^^^? (← ((← ((← (col6 &&&? (52428 : u16))) >>>? (2 : i32)))
          |||? (← ((← (col6 &&&? (13107 : u16))) <<<? (2 : i32))))))));
  let col7 : u16 ←
    ((← __st__[(7 : usize)]_?)
      ^^^? (← ((← ((← ((← __st__[(7 : usize)]_?) &&&? (61166 : u16)))
          >>>? (1 : i32)))
        |||? (← ((← ((← __st__[(7 : usize)]_?) &&&? (4369 : u16)))
          <<<? (3 : i32))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (7 : usize)
      (← ((← ((← ((← __st__[(7 : usize)]_?) ^^^? col6)) ^^^? col7))
        ^^^? (← ((← ((← (col7 &&&? (52428 : u16))) >>>? (2 : i32)))
          |||? (← ((← (col7 &&&? (13107 : u16))) <<<? (2 : i32))))))));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (0 : usize)
      (← ((← __st__[(0 : usize)]_?) ^^^? col7)));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (1 : usize)
      (← ((← __st__[(1 : usize)]_?) ^^^? col7)));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (3 : usize)
      (← ((← __st__[(3 : usize)]_?) ^^^? col7)));
  let __st__ : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      __st__
      (4 : usize)
      (← ((← __st__[(4 : usize)]_?) ^^^? col7)));
  (pure __st__)

def mix_columns_state_spec (st : Vector u16 8) : Vector u16 8 :=
  (4 : Nat).fold (init := zero_array) fun group_indx _ res =>
  let s_0 := get_elem st group_indx (by omega)
  let s_1 := get_elem st (group_indx + 4) (by omega)
  let s_2 := get_elem st (group_indx + 8) (by omega)
  let s_3 := get_elem st (group_indx + 12) (by omega)

  let s_0' := (GF8.mul (0x02#8) s_0) ^^^ (GF8.mul (0x03#8) s_1) ^^^ s_2 ^^^ s_3
  let s_1' := (GF8.mul (0x02#8) s_1) ^^^ (GF8.mul (0x03#8) s_2) ^^^ s_3 ^^^ s_0
  let s_2' := (GF8.mul (0x02#8) s_2) ^^^ (GF8.mul (0x03#8) s_3) ^^^ s_0 ^^^ s_1
  let s_3' := (GF8.mul (0x02#8) s_3) ^^^ (GF8.mul (0x03#8) s_0) ^^^ s_1 ^^^ s_2

  let set_0 := set_elem res group_indx s_0'
  let set_1 := set_elem set_0 (group_indx + 4) s_1'
  let set_2 := set_elem set_1 (group_indx + 8) s_2'
  set_elem set_2 (group_indx + 12) s_3'


#eval get_elem (#v[0x0001, 0, 0, 0, 0, 0, 0, 0]) 0 (by grind)
#eval (GF8.mul (0x01#8) (0x02#8))
#eval mix_columns_state_spec #v[0x0001, 0, 0, 0, 0, 0, 0, 0]

--set_option maxRecDepth 10000
--set_option maxHeartbeats 100000000
--set_option hax_mvcgen.specset "bv" in
--theorem transpose_u16x8_correct (st : (Vector u16 8)) :
--⦃ ⌜ st.size = 8 ⌝ ⦄
--mix_columns_state_unrolled some_array
--⦃ ⇓ ⟨res⟩ =>
--    ⌜ res[0] = (mix_columns_state_spec (some_array.toVec))[0] ⌝ ⦄
--:= by
--    unfold mix_columns_state_unrolled
--    hax_mvcgen <;> simp at *
--    .
--      unfold mix_columns_state_spec some_array
--      simp
--      unfold set_elem get_elem GF8.mul
--      simp
--
--
--
--set_option maxRecDepth 10000
--set_option maxHeartbeats 100000000
--set_option hax_mvcgen.specset "bv" in
--theorem transpose_u16x8_correct_st (st : (Vector u16 8)) :
--⦃ ⌜ st.size = 8 ⌝ ⦄
--mix_columns_state_unrolled (RustArray.ofVec st)
--⦃ ⇓ ⟨res⟩ =>
--    ⌜ res[0] = (mix_columns_state_spec st)[0] ⌝ ⦄
--:= by
--    unfold mix_columns_state_unrolled
--    hax_mvcgen <;> simp at *
--    rename_auto_n 150
--    simp only [var_145, var_139, var_141, var_140, var_87, var_85, var_83, var_88, var_138, var_82, var_84, var_86, <- var_137, <- var_81]
--    unfold mix_columns_state_spec set_elem get_elem zero_array
--    simp
--    simp only [<- var_81, <- var_137, <- var_90, <- var_97, <- var_105, <- var_113, <- var_121, <- var_129]
--    bv_decide

    --all_goals grind

-- ============================================================
-- Test harness for mix_columns_state_unrolled vs mix_columns_state_spec
-- ============================================================

-- Helper to run the monadic version and extract the result
def runUnrolled (input : RustArray u16 8) : Option (RustArray u16 8) :=
  match mix_columns_state_unrolled input with
  | .ok result => some result
  | _     => none

-- Helper to convert between RustArray and Vector if needed
-- (adjust depending on your coercions)
def toVector (a : RustArray u16 8) : Vector u16 8 := a.toVec
def toRustArray (v : Vector u16 8) : RustArray u16 8 := RustArray.ofVec v

-- Core comparison: returns true if both functions agree on an input
def bothAgree (input : Vector u16 8) : Bool :=
  let specResult   := mix_columns_state_spec input
  let rustInput    := toRustArray input
  match runUnrolled rustInput with
  | none        => false  -- monadic version errored
  | some result => toVector result == specResult

-- ============================================================
-- Test cases
-- ============================================================

-- TC1: All zeros
#eval bothAgree ⟨#[0, 0, 0, 0, 0, 0, 0, 0], by decide⟩

-- TC2: All ones (0xFFFF)
#eval bothAgree ⟨#[0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF,
                   0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF], by decide⟩

#eval mix_columns_state_spec #v[0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF]
#eval match mix_columns_state_unrolled (RustArray.ofVec #v[0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF]) with
      | .ok v => v
      | _ => (RustArray.ofVec zero_array : RustArray u16 8)

-- TC3: Identity-like — only first element set
#eval bothAgree ⟨#[0x0001, 0, 0, 0, 0, 0, 0, 0], by decide⟩
#eval mix_columns_state_spec #v[0x0001, 0, 0, 0, 0, 0, 0, 0]
#eval match mix_columns_state_unrolled (RustArray.ofVec #v[0b0000000000000001, 0, 0, 0, 0, 0, 0, 0]) with
      | .ok v => v
      | _ => (RustArray.ofVec zero_array : RustArray u16 8)
-- TC4: AES standard test vector (first column of AES MixColumns example)
-- Input bytes: [0xd4, 0xbf, 0x5d, 0x30] packed into u16 pairs
#eval bothAgree ⟨#[0xbfd4, 0x305d, 0x04c7, 0x2766,
                   0x9898, 0x0101, 0xabab, 0xcdcd], by decide⟩

-- TC5: Alternating bit pattern
#eval bothAgree ⟨#[0xAAAA, 0x5555, 0xAAAA, 0x5555,
                   0x5555, 0xAAAA, 0x5555, 0xAAAA], by decide⟩

-- TC6: Single bit set in each element
#eval bothAgree ⟨#[0x0001, 0x0002, 0x0004, 0x0008,
                   0x0010, 0x0020, 0x0040, 0x0080], by decide⟩

-- TC7: High bytes only
#eval bothAgree ⟨#[0xFF00, 0xFF00, 0xFF00, 0xFF00,
                   0xFF00, 0xFF00, 0xFF00, 0xFF00], by decide⟩

-- TC8: Low bytes only
#eval bothAgree ⟨#[0x00FF, 0x00FF, 0x00FF, 0x00FF,
                   0x00FF, 0x00FF, 0x00FF, 0x00FF], by decide⟩

-- TC9: Random-looking values
#eval bothAgree ⟨#[0x1234, 0x5678, 0x9ABC, 0xDEF0,
                   0x0FED, 0xCBA9, 0x8765, 0x4321], by decide⟩

-- TC10: Powers of 2 across elements
#eval bothAgree ⟨#[0x0001, 0x0002, 0x0004, 0x0008,
                   0x0100, 0x0200, 0x0400, 0x0800], by decide⟩

-- ============================================================
-- Bulk assertion: all tests must return true
-- ============================================================
#eval do
  let tests : List (String × Vector u16 8) := [
    ("all zeros",       ⟨#[0,      0,      0,      0,      0,      0,      0,      0     ], by decide⟩),
    ("all 0xFFFF",      ⟨#[0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF], by decide⟩),
    ("only first set",  ⟨#[0x0001, 0,      0,      0,      0,      0,      0,      0     ], by decide⟩),
    ("AES vector",      ⟨#[0xbfd4, 0x305d, 0x04c7, 0x2766, 0x9898, 0x0101, 0xabab, 0xcdcd], by decide⟩),
    ("alternating",     ⟨#[0xAAAA, 0x5555, 0xAAAA, 0x5555, 0x5555, 0xAAAA, 0x5555, 0xAAAA], by decide⟩),
    ("single bits",     ⟨#[0x0001, 0x0002, 0x0004, 0x0008, 0x0010, 0x0020, 0x0040, 0x0080], by decide⟩),
    ("high bytes",      ⟨#[0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00, 0xFF00], by decide⟩),
    ("low bytes",       ⟨#[0x00FF, 0x00FF, 0x00FF, 0x00FF, 0x00FF, 0x00FF, 0x00FF, 0x00FF], by decide⟩),
    ("random-ish",      ⟨#[0x1234, 0x5678, 0x9ABC, 0xDEF0, 0x0FED, 0xCBA9, 0x8765, 0x4321], by decide⟩),
    ("powers of 2",     ⟨#[0x0001, 0x0002, 0x0004, 0x0008, 0x0100, 0x0200, 0x0400, 0x0800], by decide⟩),
  ]
  for (name, input) in tests do
    let ok := bothAgree input
    IO.println s!"[{if ok then "PASS" else "FAIL"}] {name}"



end aes_core.mix_columns_state
