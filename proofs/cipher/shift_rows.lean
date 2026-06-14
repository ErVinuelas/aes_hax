
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


namespace aes_core.shift_rows

def fst_row := [0, 4, 8, 12]
def snd_row := [1, 5, 9, 13]
def thrd_row := [2, 6, 10, 14]
def frth_row := [3, 7, 11, 15]

--For each map of bits we are moving the elements a number of positions depending
-- on the row they are in the matrix.
def shift_row_u16_spec (input : u16) : u16 :=
  let input_bitvec := input.toBitVec
  (16 : Nat).fold (init := 0) fun i _ res =>
    let bt := ((input_bitvec >>> i) &&& 1)
    res ||| UInt16.ofBitVec
      (if i ∈ fst_row then bt <<< i else
      if i ∈ snd_row then bt <<< ((i + 12) % 16) else
      if i ∈ thrd_row then bt <<< ((i + 8) % 16) else
      --if i ∈ frth_row then
      bt <<< ((i + 4) % 16))

@[spec]
def shift_row_u16 (input : u16) : RustM u16 := do
  ((← ((← ((← ((← ((← ((← (input &&&? (4369 : u16)))
              |||? (← ((← (input &&&? (8736 : u16))) >>>? (4 : i32)))))
            |||? (← ((← (input &&&? (2 : u16))) <<<? (12 : i32)))))
          |||? (← ((← (input &&&? (17408 : u16))) >>>? (8 : i32)))))
        |||? (← ((← (input &&&? (68 : u16))) <<<? (8 : i32)))))
      |||? (← ((← (input &&&? (32768 : u16))) >>>? (12 : i32)))))
    |||? (← ((← (input &&&? (2184 : u16))) <<<? (4 : i32))))

-- Apply the shift_rows to each of the map of bits.
def shift_rows_stat_spec (st : (RustArray u16 8)) : Vector u16 8 :=
  st.toVec.map (shift_row_u16_spec)

@[spec]
def shift_rows_state (st : (RustArray u16 8)) : RustM (RustArray u16 8) := do
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (0 : usize)
      (← (shift_row_u16 (← st[(0 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (1 : usize)
      (← (shift_row_u16 (← st[(1 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (2 : usize)
      (← (shift_row_u16 (← st[(2 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (3 : usize)
      (← (shift_row_u16 (← st[(3 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (4 : usize)
      (← (shift_row_u16 (← st[(4 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (5 : usize)
      (← (shift_row_u16 (← st[(5 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (6 : usize)
      (← (shift_row_u16 (← st[(6 : usize)]_?))));
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (7 : usize)
      (← (shift_row_u16 (← st[(7 : usize)]_?))));
  (pure st)

set_option maxHeartbeats 100000000
set_option hax_mvcgen.specset "bv" in
@[spec]
theorem shift_row_u16_correct (input : u16) :
⦃ ⌜ true = true ⌝ ⦄
shift_row_u16 input
⦃ ⇓ ⟨res⟩ =>
    ⌜ UInt16.ofBitVec res = (shift_row_u16_spec input) ⌝ ⦄
:= by
    unfold shift_row_u16

    hax_mvcgen
    <;> simp at *
    .
      unfold shift_row_u16_spec fst_row snd_row thrd_row
      simp
      rename_i h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      unfold UInt16.lor
      simp only [ h8, h9, h10, h11, h12, h13]
      simp
      clear h8 h9 h10 h11 h12 h13
      clear h1 h2 h3 h4 h5 h6 h7
      bv_decide

end aes_core.shift_rows
