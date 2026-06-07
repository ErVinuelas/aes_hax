-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Utilities
import gf128
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace gcm_core.platform.portable.gf128_core

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

def IRRED : u128 := (299076299051606071403356588563077529600 : u128)

@[spec]
def mul_x (elem : u128) : RustM u128 := do
  let mask : u128 ← (ith_bit_mask elem (127 : usize));
  let elem : u128 ← ((← (elem >>>? (1 : i32))) ^^^? (← (IRRED &&&? mask)));
  (pure elem)

@[spec]
def mul_step (x : u128) (y : u128) (i : usize) (result : u128) :
    RustM (rust_primitives.hax.Tuple2 u128 u128) := do
  let _ ←
    if true then do
      let _ ← (hax_lib.assert (← (i <? (128 : usize))));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let mask : u128 ← (ith_bit_mask x i);
  let result : u128 ← (result ^^^? (← (y &&&? mask)));
  let y : u128 ← (mul_x y);
  (pure (rust_primitives.hax.Tuple2.mk y result))

set_option maxRecDepth 10000
@[spec]
def mul_unrolled (x : u128) (y : u128) : RustM u128 := do
  let result : u128 := (0 : u128);
  let multiplicand : u128 := y;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (0 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (1 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (2 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (3 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (4 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (5 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (6 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (7 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (8 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (9 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (10 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (11 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (12 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (13 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (14 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (15 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (16 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (17 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (18 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (19 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (20 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (21 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (22 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (23 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (24 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (25 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (26 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (27 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (28 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (29 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (30 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (31 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (32 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (33 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (34 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (35 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (36 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (37 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (38 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (39 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (40 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (41 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (42 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (43 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (44 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (45 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (46 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (47 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (48 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (49 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (50 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (51 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (52 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (53 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (54 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (55 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (56 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (57 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (58 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (59 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (60 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (61 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (62 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (63 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (64 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (65 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (66 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (67 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (68 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (69 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (70 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (71 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (72 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (73 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (74 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (75 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (76 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (77 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (78 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (79 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (80 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (81 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (82 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (83 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (84 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (85 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (86 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (87 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (88 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (89 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (90 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (91 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (92 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (93 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (94 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (95 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (96 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (97 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (98 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (99 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (100 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (101 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (102 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (103 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (104 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (105 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (106 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (107 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (108 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (109 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (110 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (111 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (112 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (113 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (114 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (115 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (116 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (117 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (118 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (119 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (120 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (121 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (122 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (123 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (124 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (125 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (126 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  let ⟨tmp0, tmp1⟩ ← (mul_step x multiplicand (127 : usize) result);
  let multiplicand : u128 := tmp0;
  let result : u128 := tmp1;
  let _ := rust_primitives.hax.Tuple0.mk;
  (pure result)

@[simp] 
theorem UInt128.toBitVec_xor (a b : UInt128) :
 (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := by rfl

@[simp] 
theorem UInt64.toUInt128_xor (a b : UInt64) :
 (a ^^^ b).toUInt128 = a.toUInt128 ^^^ b.toUInt128 := 
 by 
  simp [UInt64.toUInt128]
  congr 1

@[simp] 
theorem UInt64.toUInt128_shiftLeft (a b : UInt64) :
 (a <<< b).toUInt128 = a.toUInt128 <<< (b.toUInt128) % (2^128):= 
 by 
  sorry


@[simp]
theorem UInt128.ofNat_toNat (a : UInt128) :
  UInt128.ofNat a.toNat = a :=
  by 
    simp

@[simp] 
theorem UInt128.toBitVec_and (a b : UInt128) :
 (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := by rfl

@[simp] 
theorem UInt128.toBitVec_shiftRight (a b : UInt128) : 
  (a >>> b).toBitVec = a.toBitVec >>> (b.toBitVec % 128) := by rfl

@[simp] 
theorem UInt128.toBitVec_shiftLeft (a b : UInt128) :
    (a <<< b).toBitVec = a.toBitVec <<< (b.toBitVec % 128) := rfl

@[simp] 
theorem UInt128.shiftRight_zero (n : UInt128) : 
  n >>> 0 = n := rfl

@[simp] 
theorem UInt128.toBitVec_if (b : Bool) (a c : UInt128) : 
  (bif b then a else c).toBitVec = if b then a.toBitVec else c.toBitVec := by grind

@[simp] 
theorem UInt32.toBitVec_toUInt128 (n : UInt32) :
  n.toUInt128.toBitVec = BitVec.setWidth 128 n.toBitVec := by sorry

@[simp] 
theorem UInt64.toBitVec_toUInt128 (n : UInt64) :
  n.toUInt128.toBitVec = BitVec.setWidth 128 n.toBitVec := by sorry

@[simp] 
theorem UInt128.toBitVec_toUInt64 (a : UInt128) :
  a.toUInt64.toBitVec = BitVec.setWidth 64 a.toBitVec := by sorry


theorem IRRED_eq : (IRRED : u128).toBitVec = GF128.polyRed := by
  native_decide

-- ============================================================
-- §2  Specification for ith_bit_mask
--
-- ith_bit_mask elem i reads bit (127 - i) of elem (LSB-indexed)
-- and returns either 0xFF…F (all-ones, 128 bits) or 0 depending
-- on whether that bit is set.
--
-- The result is used as a conditional mask: AND-ing with y either
-- selects all of y or zeroes it out.
-- ============================================================

/-- All-ones 128-bit mask. -/
private abbrev ones128 : u128 := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF

#eval match ith_bit_mask 1 127 with
      | .ok v => v
      | _ => 5

#eval (1#128)[0]

set_option maxHeartbeats 100000000
@[spec]
theorem ith_bit_mask_spec (elem : u128) (i : Nat) (h : i < 128) :
  let i_usize : usize := i.toUSize64
    ⦃ ⌜ True ⌝ ⦄
    ith_bit_mask elem i_usize
    ⦃ ⇓ mask =>
        ⌜ mask.toBitVec = if elem.toBitVec[127 - i] = true
                 then ones128.toBitVec
                 else 0#128 ⌝ ⦄ := by
  simp only [ith_bit_mask]
  hax_mvcgen
  ·
    expose_names
    simp
    hax_mvcgen
    .
      unfold core_models.num.Impl_7.wrapping_add
      unfold rust_primitives.arithmetic.wrapping_add_u16
      simp
      bv_decide
  · 
    simp
    rename_auto_n 20
    simp only [var_6, var_8]
    simp at *
    sorry
    --have hvar : ∃ (var_1 : BitVec 128), var_1 = (elem.toBitVec  >>> ((127 - i).toNat % 128)) := by grind 
    --obtain ⟨var_1, hv⟩ := hvar
    --simp only [<-hv]
    --clear var_8 var_6
    --expose_names
    --clear var_1_1 
    --clear var_2
    --clear var_4 var_3
    --unfold getElem BitVec.instGetElemNatBoolLt
    --bv_decide
  .
    expose_names
    simp
    hax_mvcgen
    .
      unfold core_models.num.Impl_7.wrapping_add
      unfold rust_primitives.arithmetic.wrapping_add_u16
      simp
      bv_decide
  .
    grind
    

@[spec]
theorem mul_x_spec (elem : u128) :
    ⦃ ⌜ True ⌝ ⦄
    mul_x elem
    ⦃ ⇓ r => ⌜ r.toBitVec = GF128.xtime elem.toBitVec ⌝ ⦄ := by
  simp only [mul_x, GF128.xtime]
  hax_mvcgen [ith_bit_mask_spec]
  
  --expose_names
  --simp [h, UInt128.toBitVec_if, IRRED_eq, GF128.polyRed]
  match (elem.toBitVec.getLsbD 0) with
  | true => 
    simp
    unfold IRRED GF128.polyRed 
    bv_decide
  | false => simp


@[spec]
theorem mul_step_spec (x y : u128) (i : usize) (result : u128) :
    ⦃ ⌜ i.toNat < 128 ⌝ ⦄
    mul_step x y i result
    ⦃ ⇓ p =>
        let bitIdx := 127 - i.toNat
        let (new_result, new_y) :=
          GF128.mulStep x.toBitVec (result.toBitVec, y.toBitVec) bitIdx
        ⌜ p.1.toBitVec = new_y ∧ p.2.toBitVec = new_result ⌝ ⦄ := by
  simp only [mul_step, GF128.mulStep]
  mvcgen [mul_step, ith_bit_mask_spec, mul_x_spec]
  ·
    rename_auto_n 20
    hax_mvcgen
    simp [var_4, var_6]
    simp only [ones128]
    have hsome2 :  ∀ (a b : UInt128), (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := by apply UInt128.toBitVec_and
    simp [UInt128.toBitVec_xor, UInt128.toBitVec_and]
    bv_decide
  ·  grind

set_option maxRecDepth 1000000000
set_option maxHeartbeats 10000000000000
set_option hax_mvcgen.specset "bv" in
theorem mul_correct (x : u128) (y : u128) :
    ⦃ ⌜ true ⌝ ⦄
    mul_unrolled x y
    ⦃ ⇓ ⟨res⟩ =>
        ⌜ res = GF128.mul y.toBitVec x.toBitVec  ⌝ ⦄ := by
  unfold mul_unrolled
  hax_mvcgen[mul_step_spec] <;> simp at *
  rename_auto_n 300

  simp only [var_256]
  simp only [ GF128.mul, GF128.zero, List.range, List.reverse]
  simp only [List.reverseAux_eq, List.append_nil, List.range.loop]
  simp
  congr 1
  congr 1
  have hp : ∀ (p : GF128 × GF128), (p.fst, p.snd) = p := by sorry
  simp only [var_252, hp] ;  congr 1
  simp only [var_250, hp] ;  congr 1
  simp only [var_248, hp] ;  congr 1
  simp only [var_246, hp] ;  congr 1
  simp only [var_244, hp] ;  congr 1
  simp only [var_242, hp] ;  congr 1
  simp only [var_240, hp] ;  congr 1
  simp only [var_238, hp] ;  congr 1
  simp only [var_236, hp] ;  congr 1
  simp only [var_234, hp] ;  congr 1
  simp only [var_232, hp] ;  congr 1
  simp only [var_230, hp] ;  congr 1
  simp only [var_228, hp] ;  congr 1
  simp only [var_226, hp] ;  congr 1
  simp only [var_224, hp] ;  congr 1
  simp only [var_222, hp] ;  congr 1
  simp only [var_220, hp] ;  congr 1
  simp only [var_218, hp] ;  congr 1
  simp only [var_216, hp] ;  congr 1
  simp only [var_214, hp] ;  congr 1
  simp only [var_212, hp] ;  congr 1
  simp only [var_210, hp] ;  congr 1
  simp only [var_208, hp] ;  congr 1
  simp only [var_206, hp] ;  congr 1
  simp only [var_204, hp] ;  congr 1
  simp only [var_202, hp] ;  congr 1
  simp only [var_200, hp] ;  congr 1
  simp only [var_198, hp] ;  congr 1
  simp only [var_196, hp] ;  congr 1
  simp only [var_194, hp] ;  congr 1
  simp only [var_192, hp] ;  congr 1
  simp only [var_190, hp] ;  congr 1
  simp only [var_188, hp] ;  congr 1
  simp only [var_186, hp] ;  congr 1
  simp only [var_184, hp] ;  congr 1
  simp only [var_182, hp] ;  congr 1
  simp only [var_180, hp] ;  congr 1
  simp only [var_178, hp] ;  congr 1
  simp only [var_176, hp] ;  congr 1
  simp only [var_174, hp] ;  congr 1
  simp only [var_172, hp] ;  congr 1
  simp only [var_170, hp] ;  congr 1
  simp only [var_168, hp] ;  congr 1
  simp only [var_166, hp] ;  congr 1
  simp only [var_164, hp] ;  congr 1
  simp only [var_162, hp] ;  congr 1
  simp only [var_160, hp] ;  congr 1
  simp only [var_158, hp] ;  congr 1
  simp only [var_156, hp] ;  congr 1
  simp only [var_154, hp] ;  congr 1
  simp only [var_152, hp] ;  congr 1
  simp only [var_150, hp] ;  congr 1
  simp only [var_148, hp] ;  congr 1
  simp only [var_146, hp] ;  congr 1
  simp only [var_144, hp] ;  congr 1
  simp only [var_142, hp] ;  congr 1
  simp only [var_140, hp] ;  congr 1
  simp only [var_138, hp] ;  congr 1
  simp only [var_136, hp] ;  congr 1
  simp only [var_134, hp] ;  congr 1
  simp only [var_132, hp] ;  congr 1
  simp only [var_130, hp] ;  congr 1
  simp only [var_128, hp] ;  congr 1
  simp only [var_126, hp] ;  congr 1
  simp only [var_124, hp] ;  congr 1
  simp only [var_122, hp] ;  congr 1
  simp only [var_120, hp] ;  congr 1
  simp only [var_118, hp] ;  congr 1
  simp only [var_116, hp] ;  congr 1
  simp only [var_114, hp] ;  congr 1
  simp only [var_112, hp] ;  congr 1
  simp only [var_110, hp] ;  congr 1
  simp only [var_108, hp] ;  congr 1
  simp only [var_106, hp] ;  congr 1
  simp only [var_104, hp] ;  congr 1
  simp only [var_102, hp] ;  congr 1
  simp only [var_100, hp] ;  congr 1
  simp only [var_98, hp] ;  congr 1
  simp only [var_96, hp] ;  congr 1
  simp only [var_94, hp] ;  congr 1
  simp only [var_92, hp] ;  congr 1
  simp only [var_90, hp] ;  congr 1
  simp only [var_88, hp] ;  congr 1
  simp only [var_86, hp] ;  congr 1
  simp only [var_84, hp] ;  congr 1
  simp only [var_82, hp] ;  congr 1
  simp only [var_80, hp] ;  congr 1
  simp only [var_78, hp] ;  congr 1
  simp only [var_76, hp] ;  congr 1
  simp only [var_74, hp] ;  congr 1
  simp only [var_72, hp] ;  congr 1
  simp only [var_70, hp] ;  congr 1
  simp only [var_68, hp] ;  congr 1
  simp only [var_66, hp] ;  congr 1
  simp only [var_64, hp] ;  congr 1
  simp only [var_62, hp] ;  congr 1
  simp only [var_60, hp] ;  congr 1
  simp only [var_58, hp] ;  congr 1
  simp only [var_56, hp] ;  congr 1
  simp only [var_54, hp] ;  congr 1
  simp only [var_52, hp] ;  congr 1
  simp only [var_50, hp] ;  congr 1
  simp only [var_48, hp] ;  congr 1
  simp only [var_46, hp] ;  congr 1
  simp only [var_44, hp] ;  congr 1
  simp only [var_42, hp] ;  congr 1
  simp only [var_40, hp] ;  congr 1
  simp only [var_38, hp] ;  congr 1
  simp only [var_36, hp] ;  congr 1
  simp only [var_34, hp] ;  congr 1
  simp only [var_32, hp] ;  congr 1
  simp only [var_30, hp] ;  congr 1
  simp only [var_28, hp] ;  congr 1
  simp only [var_26, hp] ;  congr 1
  simp only [var_24, hp] ;  congr 1
  simp only [var_22, hp] ;  congr 1
  simp only [var_20, hp] ;  congr 1
  simp only [var_18, hp] ;  congr 1
  simp only [var_16, hp] ;  congr 1
  simp only [var_14, hp] ;  congr 1
  simp only [var_12, hp] ;  congr 1
  simp only [var_10, hp] ;  congr 1
  simp only [var_8, hp] ;  congr 1
  simp only [var_6, hp] ;  congr 1
  simp only [var_4, hp] ;  congr 1
  simp only [var_2, hp] ; congr 1
  simp only [var_255, hp] 

end gcm_core.platform.portable.gf128_core
