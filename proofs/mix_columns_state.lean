
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax

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

end aes_core.mix_columns_state
