
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

namespace playground

@[spec]
def ith_bit_mask (elem : u128) (i : usize) : RustM u128 := do
  let _ ←
    if true then do
      let _ ← (hax_lib.assert (← (i <? (128 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let bit : u16 ←
    ((← (rust_primitives.hax.cast_op
        (← (elem >>>? (← ((127 : usize) -? i)))) :
        RustM u16))
      &&&? (1 : u16));
  let bit_mask16 : u16 ←
    (core_models.num.Impl_7.wrapping_add (← (~? bit)) (1 : u16));
  let bit_mask32 : u32 ←
    ((← (rust_primitives.hax.cast_op bit_mask16 : RustM u32))
      ^^^? (← ((← (rust_primitives.hax.cast_op bit_mask16 : RustM u32))
        <<<? (16 : i32))));
  let bit_mask64 : u64 ←
    ((← (rust_primitives.hax.cast_op bit_mask32 : RustM u64))
      ^^^? (← ((← (rust_primitives.hax.cast_op bit_mask32 : RustM u64))
        <<<? (32 : i32))));
  ((← (rust_primitives.hax.cast_op bit_mask64 : RustM u128))
    ^^^? (← ((← (rust_primitives.hax.cast_op bit_mask64 : RustM u128))
      <<<? (64 : i32))))

def helper (elem : u128) (i : usize): RustM u16 := do
  let _ ←
      if true then do
        let _ ← (hax_lib.assert (← (i <? (128 : usize))));
        (pure rust_primitives.hax.Tuple0.mk)
      else do
        (pure rust_primitives.hax.Tuple0.mk);
  let bit : u16 ←
    ((← (rust_primitives.hax.cast_op
        (← (elem >>>? (← ((127 : usize) -? i)))) :
        RustM u16))
      &&&? (1 : u16));
  (pure bit)

@[simp] 
theorem UInt128.toBitVec_shiftRight (a b : UInt128) : 
  (a >>> b).toBitVec = a.toBitVec >>> (b.toBitVec % 128) := by rfl

def helper_spec (elem : UInt128) (i : Fin 128) : BitVec 16 :=
  let elem_bv := elem.toBitVec
  (elem_bv.extractLsb (127 - i) (127 - i)).zeroExtend 16

theorem helper_correct (elem : u128) (i : Nat) (h : i < 128) :
  let i_usize : usize := i.toUSize64
    ⦃ ⌜ i < 128 ⌝ ⦄
    helper elem i_usize
    ⦃ ⇓ res =>
        ⌜ res.toBitVec = helper_spec elem ⟨i, h⟩ ⌝ ⦄ := 
  by
    unfold helper
    hax_mvcgen
    .
      simp
      unfold helper_spec
      simp
      bv_decide
    .
      unfold helper_spec
      simp [UInt128.toBitVec_shiftRight]
      have hvar : ∃ (var_1 : BitVec 128), var_1 = elem.toBitVec := by grind
      obtain ⟨var_1, hvar⟩ := hvar
      have hi : (127 - i.toUSize64).toNat % 128 = 127 - i := by sorry
      simp only [<- hvar, hi]
      bv_decide
    .
      bv_decide

end playground
