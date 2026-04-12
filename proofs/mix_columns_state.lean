
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Utilities

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

def mix_columns_state_spec (st : Vector u16 8) : Vector u16 8 :=
  (4 : Nat).fold (init := zero_array) fun group_indx _ res =>
  let s_0 := get_elem st group_indx (by omega)
  let s_1 := get_elem st (group_indx + 4) (by omega)
  let s_2 := get_elem st (group_indx + 8) (by omega)
  let s_3 := get_elem st (group_indx + 12) (by omega)

  let s_0' := (0x02#8 &&& s_0) ^^^ (0x03#8 &&& s_1) ^^^ s_2 ^^^ s_3
  let s_1' := (0x02#8 &&& s_1) ^^^ (0x03#8 &&& s_2) ^^^ s_3 ^^^ s_0
  let s_2' := (0x02#8 &&& s_2) ^^^ (0x03#8 &&& s_3) ^^^ s_0 ^^^ s_1
  let s_3' := (0x02#8 &&& s_3) ^^^ (0x03#8 &&& s_0) ^^^ s_1 ^^^ s_2

  let set_0 := set_elem res group_indx s_0'
  let set_1 := set_elem set_0 (group_indx + 4) s_1'
  let set_2 := set_elem set_1 (group_indx + 8) s_2'
  set_elem set_2 (group_indx + 12) s_3'

set_option maxHeartbeats 100000000
set_option hax_mvcgen.specset "bv" in
theorem transpose_u16x8_correct (st : (Vector u16 8)) :
⦃ ⌜ true = true ⌝ ⦄
mix_columns_state (RustArray.ofVec zero_array)
⦃ ⇓ ⟨res⟩ =>
    ⌜ res[0] = (mix_columns_state_spec zero_array)[0] ⌝ ⦄
:= by
    unfold mix_columns_state
    hax_mvcgen <;> simp at *
    rename_auto_n 14
    unfold mix_columns_state_spec set_elem get_elem zero_array
    simp
    sorry

end aes_core.mix_columns_state
