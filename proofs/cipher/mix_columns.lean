
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Utilities
import gf8

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace aes_core.mix_columns

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

--Prove that unrolled is the same as original?
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
  let index := group_indx * 4
  let s_0 := get_elem st index
  let s_1 := get_elem st (index + 1)
  let s_2 := get_elem st (index + 2)
  let s_3 := get_elem st (index + 3)

  let s_0' := GF8.add (GF8.add (GF8.add (GF8.mul (0x02#8) s_0) (GF8.mul (0x03#8) s_1)) s_2) s_3
  let s_1' := GF8.add (GF8.add (GF8.add (GF8.mul (0x02#8) s_1) (GF8.mul (0x03#8) s_2)) s_3) s_0
  let s_2' := GF8.add (GF8.add (GF8.add (GF8.mul (0x02#8) s_2) (GF8.mul (0x03#8) s_3)) s_0) s_1
  let s_3' := GF8.add (GF8.add (GF8.add (GF8.mul (0x02#8) s_3) (GF8.mul (0x03#8) s_0)) s_1) s_2

  let set_0 := set_elem res index s_0'
  let set_1 := set_elem set_0 (index + 1) s_1'
  let set_2 := set_elem set_1 (index + 2) s_2'
  set_elem set_2 (index + 3) s_3'


-- ============================================================
-- Test harness for mix_columns_state_unrolled vs mix_columns_state_spec
-- ============================================================

def runUnrolled (input : RustArray u16 8) : Option (RustArray u16 8) :=
  match mix_columns_state input with
  | .ok result => some result
  | _     => none

def bothAgree (input : Vector u16 8) : Bool :=
  let specResult   := mix_columns_state_spec input
  let rustInput    := RustArray.ofVec input
  match runUnrolled rustInput with
  | none        => false  -- monadic version errored
  | some result => result.toVec == specResult

-- ============================================================
-- Test cases
-- ============================================================

#eval bothAgree ⟨#[0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF,
                   0xFFFF, 0xFFFF, 0xFFFF, 0xFFFF], by decide⟩

#eval bothAgree ⟨#[0x0001, 0, 0, 0, 0, 0, 0, 0], by decide⟩

#eval bothAgree ⟨#[0xbfd4, 0x305d, 0x04c7, 0x2766,
                   0x9898, 0x0101, 0xabab, 0xcdcd], by decide⟩

#eval bothAgree ⟨#[0xAAAA, 0x5555, 0xAAAA, 0x5555,
                   0x5555, 0xAAAA, 0x5555, 0xAAAA], by decide⟩

#eval bothAgree ⟨#[0x0001, 0x0002, 0x0004, 0x0008,
                   0x0010, 0x0020, 0x0040, 0x0080], by decide⟩

#eval bothAgree ⟨#[0xFF00, 0xFF00, 0xFF00, 0xFF00,
                   0xFF00, 0xFF00, 0xFF00, 0xFF00], by decide⟩

#eval bothAgree ⟨#[0x00FF, 0x00FF, 0x00FF, 0x00FF,
                   0x00FF, 0x00FF, 0x00FF, 0x00FF], by decide⟩

#eval bothAgree ⟨#[0x1234, 0x5678, 0x9ABC, 0xDEF0,
                   0x0FED, 0xCBA9, 0x8765, 0x4321], by decide⟩

#eval bothAgree ⟨#[0x0001, 0x0002, 0x0004, 0x0008,
                   0x0100, 0x0200, 0x0400, 0x0800], by decide⟩

end aes_core.mix_columns
