import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace aes_core.transpose_u8x16

def interleave_u8_1_spec (i0 : u8) (i1 : u8) : u16 :=
  UInt16.ofBitVec
  (
    let i0_btv := i0.toBitVec
    let i1_btv := i1.toBitVec
    (16 : Nat).fold (init := (0 : BitVec 16)) fun i _ res =>
      res ||| (((i0_btv >>> i) &&& 1).setWidth 16 <<< (2 * i)) ||| (((i1_btv >>> i) &&& 1).setWidth 16 <<< (2 * i + 1))
  )

def interleave_u8_1 (i0 : u8) (i1 : u8) : RustM u16 := do
  let x : u16 ← (rust_primitives.hax.cast_op i0 : RustM u16);
  let x : u16 ← ((← (x |||? (← (x <<<? (4 : i32))))) &&&? (3855 : u16));
  let x : u16 ← ((← (x |||? (← (x <<<? (2 : i32))))) &&&? (13107 : u16));
  let x : u16 ← ((← (x |||? (← (x <<<? (1 : i32))))) &&&? (21845 : u16));
  let y : u16 ← (rust_primitives.hax.cast_op i1 : RustM u16);
  let y : u16 ← ((← (y |||? (← (y <<<? (4 : i32))))) &&&? (3855 : u16));
  let y : u16 ← ((← (y |||? (← (y <<<? (2 : i32))))) &&&? (13107 : u16));
  let y : u16 ← ((← (y |||? (← (y <<<? (1 : i32))))) &&&? (21845 : u16));
  (x |||? (← (y <<<? (1 : i32))))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def interleave_u8_1.spec (i0 : u8) (i1 : u8) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (res ==? (interleave_u8_1_spec i0 i1)))
      (interleave_u8_1 (i0 : u8) (i1 : u8)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by
                hax_mvcgen [interleave_u8_1] <;> simp
                simp [interleave_u8_1_spec]
                bv_decide
}

@[spec]
def interleave_u16_2 (i0 : u16) (i1 : u16) :
    RustM (rust_primitives.hax.Tuple2 u16 u16) := do
  let x : u16 ←
    ((← ((← (i1 &&&? (13107 : u16))) <<<? (2 : i32)))
      |||? (← (i0 &&&? (13107 : u16))));
  let y : u16 ←
    ((← ((← (i0 &&&? (52428 : u16))) >>>? (2 : i32)))
      |||? (← (i1 &&&? (52428 : u16))));
  (pure (rust_primitives.hax.Tuple2.mk x y))

@[spec]
def interleave_u16_4 (i0 : u16) (i1 : u16) :
    RustM (rust_primitives.hax.Tuple2 u16 u16) := do
  let x : u16 ←
    ((← ((← (i1 &&&? (3855 : u16))) <<<? (4 : i32)))
      |||? (← (i0 &&&? (3855 : u16))));
  let y : u16 ←
    ((← ((← (i0 &&&? (61680 : u16))) >>>? (4 : i32)))
      |||? (← (i1 &&&? (61680 : u16))));
  (pure (rust_primitives.hax.Tuple2.mk x y))

@[spec]
def interleave_u16_8 (i0 : u16) (i1 : u16) :
    RustM (rust_primitives.hax.Tuple2 u16 u16) := do
  let x : u16 ←
    ((← ((← (i1 &&&? (255 : u16))) <<<? (8 : i32)))
      |||? (← (i0 &&&? (255 : u16))));
  let y : u16 ←
    ((← ((← (i0 &&&? (65280 : u16))) >>>? (8 : i32)))
      |||? (← (i1 &&&? (65280 : u16))));
  (pure (rust_primitives.hax.Tuple2.mk x y))

@[spec]
def transpose_u8x16 (input : (RustArray u8 16)) (output : (RustArray u16 8)) :
    RustM (RustArray u16 8) := do
  let o0 : u16 ←
    (interleave_u8_1 (← input[(0 : usize)]_?) (← input[(1 : usize)]_?));
  let o1 : u16 ←
    (interleave_u8_1 (← input[(2 : usize)]_?) (← input[(3 : usize)]_?));
  let o2 : u16 ←
    (interleave_u8_1 (← input[(4 : usize)]_?) (← input[(5 : usize)]_?));
  let o3 : u16 ←
    (interleave_u8_1 (← input[(6 : usize)]_?) (← input[(7 : usize)]_?));
  let o4 : u16 ←
    (interleave_u8_1 (← input[(8 : usize)]_?) (← input[(9 : usize)]_?));
  let o5 : u16 ←
    (interleave_u8_1 (← input[(10 : usize)]_?) (← input[(11 : usize)]_?));
  let o6 : u16 ←
    (interleave_u8_1 (← input[(12 : usize)]_?) (← input[(13 : usize)]_?));
  let o7 : u16 ←
    (interleave_u8_1 (← input[(14 : usize)]_?) (← input[(15 : usize)]_?));
  let ⟨o0, o1⟩ ← (interleave_u16_2 o0 o1);
  let ⟨o2, o3⟩ ← (interleave_u16_2 o2 o3);
  let ⟨o4, o5⟩ ← (interleave_u16_2 o4 o5);
  let ⟨o6, o7⟩ ← (interleave_u16_2 o6 o7);
  let ⟨o0, o2⟩ ← (interleave_u16_4 o0 o2);
  let ⟨o1, o3⟩ ← (interleave_u16_4 o1 o3);
  let ⟨o4, o6⟩ ← (interleave_u16_4 o4 o6);
  let ⟨o5, o7⟩ ← (interleave_u16_4 o5 o7);
  let ⟨o0, o4⟩ ← (interleave_u16_8 o0 o4);
  let ⟨o1, o5⟩ ← (interleave_u16_8 o1 o5);
  let ⟨o2, o6⟩ ← (interleave_u16_8 o2 o6);
  let ⟨o3, o7⟩ ← (interleave_u16_8 o3 o7);
  let output : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      output
      (0 : usize)
      o0);
  let output : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      output
      (1 : usize)
      o1);
  let output : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      output
      (2 : usize)
      o2);
  let output : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      output
      (3 : usize)
      o3);
  let output : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      output
      (4 : usize)
      o4);
  let output : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      output
      (5 : usize)
      o5);
  let output : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      output
      (6 : usize)
      o6);
  let output : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      output
      (7 : usize)
      o7);
  (pure output)

def transposeU8toU16 (input : RustArray u8 16) : RustArray u16 8 :=
  RustArray.ofVec <| Vector.ofFn fun (bt_num : Fin 8) =>
    (16 : Nat).fold (init := (0 : u16)) fun mtx_elem_num _ bt_plane =>
      UInt16.ofBitVec (bt_plane.toBitVec ||| (((input.toVec[mtx_elem_num].toBitVec >>> bt_num.val) &&& 1).setWidth 16 <<< mtx_elem_num))

end aes_core.transpose_u8x16
