
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


namespace aes_core.xor_key1_state

def xor_key1_state_spec (st : (Vector u16 8)) (k : (Vector u16 8)) : (Vector u16 8) :=
  (Vector.zip st k).map (fun (x, y) => x ^^^ y)

@[spec]
def xor_key1_state (st : (RustArray u16 8)) (k : (RustArray u16 8)) :
    RustM (RustArray u16 8) := do
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (0 : usize)
      (← ((← st[(0 : usize)]_?) ^^^? (← k[(0 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (1 : usize)
      (← ((← st[(1 : usize)]_?) ^^^? (← k[(1 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (2 : usize)
      (← ((← st[(2 : usize)]_?) ^^^? (← k[(2 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (3 : usize)
      (← ((← st[(3 : usize)]_?) ^^^? (← k[(3 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (4 : usize)
      (← ((← st[(4 : usize)]_?) ^^^? (← k[(4 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (5 : usize)
      (← ((← st[(5 : usize)]_?) ^^^? (← k[(5 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (6 : usize)
      (← ((← st[(6 : usize)]_?) ^^^? (← k[(6 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (7 : usize)
      (← ((← st[(7 : usize)]_?) ^^^? (← k[(7 : usize)]_?))));
  (pure st)


end aes_core.xor_key1_state
