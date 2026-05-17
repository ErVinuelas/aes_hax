
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


namespace aes_core.transpose_u16x8


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
def deinterleave_u8_1 (i0 : u16) :
    RustM ((u8 × u8)) := do
  let x : u16 ← (i0 &&&? (21845 : u16));
  let x : u16 ← ((← (x |||? (← (x >>>? (1 : i32))))) &&&? (13107 : u16));
  let x : u16 ← ((← (x |||? (← (x >>>? (2 : i32))))) &&&? (3855 : u16));
  let x : u16 ← ((← (x |||? (← (x >>>? (4 : i32))))) &&&? (255 : u16));
  let y : u16 ← ((← (i0 >>>? (1 : i32))) &&&? (21845 : u16));
  let y : u16 ← ((← (y |||? (← (y >>>? (1 : i32))))) &&&? (13107 : u16));
  let y : u16 ← ((← (y |||? (← (y >>>? (2 : i32))))) &&&? (3855 : u16));
  let y : u16 ← ((← (y |||? (← (y >>>? (4 : i32))))) &&&? (255 : u16));
  (pure
    ((← (rust_primitives.hax.cast_op x : RustM u8)),
    (← (rust_primitives.hax.cast_op y : RustM u8))))

def deinterleave_u8_1_spec (i0 : u16) : (u8 × u8) :=
  let i0_btv := i0.toBitVec
  -- We iterate 8 times because we are extracting 8 bits for each output
  let (x_btv, y_btv) := (8 : Nat).fold (init := ((0 : BitVec 8), (0 : BitVec 8))) fun i _ (x, y) =>
    let bit_even := (i0_btv >>> (2 * i)) &&& 1
    let bit_odd  := (i0_btv >>> (2 * i + 1)) &&& 1
    (
      x ||| (bit_even.setWidth 8 <<< i),
      y ||| (bit_odd.setWidth 8 <<< i)
    )
  (UInt8.ofBitVec x_btv, UInt8.ofBitVec y_btv)

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def deinterleave_u8_1.spec (i0 : u16) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (res ==? (deinterleave_u8_1_spec i0))
                                )
      (deinterleave_u8_1 (i0 : u16)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by
                hax_mvcgen [deinterleave_u8_1] <;> simp
                simp [deinterleave_u8_1_spec]
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
    RustM (u16 × u16) := do
  let x : u16 ←
    ((← ((← (i1 &&&? (255 : u16))) <<<? (8 : i32)))
      |||? (← (i0 &&&? (255 : u16))));
  let y : u16 ←
    ((← ((← (i0 &&&? (65280 : u16))) >>>? (8 : i32)))
      |||? (← (i1 &&&? (65280 : u16))));
  (pure (x, y))

def interleave_u16_8_spec (i0 : u16) (i1 : u16) : (u16 × u16) :=
  let i0_btv := i0.toBitVec
  let i1_btv := i1.toBitVec

  let i0_low  := i0_btv.extractLsb 7 0
  let i0_high := i0_btv.extractLsb 15 8
  let i1_low  := i1_btv.extractLsb 7 0
  let i1_high := i1_btv.extractLsb 15 8

  let x := (i1_low.zeroExtend 16 <<< 8) ||| (i0_low.zeroExtend 16)

  let y := (i0_high.zeroExtend 16) ||| (i1_high.zeroExtend 16 <<< 8)

  ((UInt16.ofBitVec x), (UInt16.ofBitVec y))

set_option hax_mvcgen.specset "bv" in
@[hax_spec]
def interleave_u16_8.spec (i0 : u16) (i1 : u16) :
    Spec
      (requires := do pure True)
      (ensures := fun res => do (res ==? (interleave_u16_8_spec i0 i1)))
      (interleave_u16_8 (i0 : u16) (i1 : u16)) := {
  pureRequires := by hax_construct_pure <;> bv_decide
  pureEnsures := by hax_construct_pure <;> bv_decide
  contract := by
                hax_mvcgen [interleave_u16_8] <;> simp
                simp [interleave_u16_8_spec]
                bv_decide
}

def transpose_u16x8 (input : (RustArray u16 8)) (output : (RustSlice u8)) :
    RustM (RustSlice u8) := do
  let ⟨i0, i4⟩ ←
    (interleave_u16_8 (← input[(0 : usize)]_?) (← input[(4 : usize)]_?));
  let ⟨i1, i5⟩ ←
    (interleave_u16_8 (← input[(1 : usize)]_?) (← input[(5 : usize)]_?));
  let ⟨i2, i6⟩ ←
    (interleave_u16_8 (← input[(2 : usize)]_?) (← input[(6 : usize)]_?));
  let ⟨i3, i7⟩ ←
    (interleave_u16_8 (← input[(3 : usize)]_?) (← input[(7 : usize)]_?));
  let ⟨i0, i2⟩ ← (interleave_u16_4 i0 i2);
  let ⟨i1, i3⟩ ← (interleave_u16_4 i1 i3);
  let ⟨i4, i6⟩ ← (interleave_u16_4 i4 i6);
  let ⟨i5, i7⟩ ← (interleave_u16_4 i5 i7);
  let ⟨i0, i1⟩ ← (interleave_u16_2 i0 i1);
  let ⟨i2, i3⟩ ← (interleave_u16_2 i2 i3);
  let ⟨i4, i5⟩ ← (interleave_u16_2 i4 i5);
  let ⟨i6, i7⟩ ← (interleave_u16_2 i6 i7);
  let ⟨o0, o1⟩ ← (deinterleave_u8_1 i0);
  let ⟨o2, o3⟩ ← (deinterleave_u8_1 i1);
  let ⟨o4, o5⟩ ← (deinterleave_u8_1 i2);
  let ⟨o6, o7⟩ ← (deinterleave_u8_1 i3);
  let ⟨o8, o9⟩ ← (deinterleave_u8_1 i4);
  let ⟨o10, o11⟩ ← (deinterleave_u8_1 i5);
  let ⟨o12, o13⟩ ← (deinterleave_u8_1 i6);
  let ⟨o14, o15⟩ ← (deinterleave_u8_1 i7);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      (output)
      (0 : usize)
      o0);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (1 : usize)
      o1);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (2 : usize)
      o2);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (3 : usize)
      o3);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (4 : usize)
      o4);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (5 : usize)
      o5);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (6 : usize)
      o6);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (7 : usize)
      o7);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (8 : usize)
      o8);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (9 : usize)
      o9);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (10 : usize)
      o10);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (11 : usize)
      o11);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (12 : usize)
      o12);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (13 : usize)
      o13);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (14 : usize)
      o14);
  let output : (RustSlice u8) ←
    (rust_primitives.slice.update_at
      output
      (15 : usize)
      o15);
  (pure output)

def transposeU16toU8 (input : RustArray u16 8) : RustArray u8 16 :=
  RustArray.ofVec <| Vector.ofFn fun (bt_num : Fin 16) =>
    (8 : Nat).fold (init := (0 : u8)) fun mtx_elem_num _ bt_plane =>
      UInt8.ofBitVec (bt_plane.toBitVec ||| (((input.toVec[mtx_elem_num].toBitVec >>> bt_num.val) &&& 1).setWidth 8 <<< mtx_elem_num))

--Theorem to ensure that we can obtain the same elements from the input
set_option maxHeartbeats 10000000
theorem transpose_correct (input : (RustArray u16 8)) (i : Nat) (hi : i < 16) :
  get_elem_bv input.toVec (BitVec.ofFin ⟨i, hi⟩) = (transposeU16toU8 input).toVec[i].toBitVec := by
  simp
  match i with
  | n + 16 => grind
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>

    simp only [get_elem_bv, transposeU16toU8]
    simp
    generalize h0 : @getElem (Vector u16 8) Nat u16 (fun x i => i < 8) Vector.instGetElemNatLt input.toVec 0 _ = var_0
    generalize h1 : @getElem (Vector u16 8) Nat u16 (fun x i => i < 8) Vector.instGetElemNatLt input.toVec 1 _ = var_1
    generalize h2 : @getElem (Vector u16 8) Nat u16 (fun x i => i < 8) Vector.instGetElemNatLt input.toVec 2 _ = var_2
    generalize h3 : @getElem (Vector u16 8) Nat u16 (fun x i => i < 8) Vector.instGetElemNatLt input.toVec 3 _ = var_3
    generalize h4 : @getElem (Vector u16 8) Nat u16 (fun x i => i < 8) Vector.instGetElemNatLt input.toVec 4 _ = var_4
    generalize h5 : @getElem (Vector u16 8) Nat u16 (fun x i => i < 8) Vector.instGetElemNatLt input.toVec 5 _ = var_5
    generalize h6 : @getElem (Vector u16 8) Nat u16 (fun x i => i < 8) Vector.instGetElemNatLt input.toVec 6 _ = var_6
    generalize h7 : @getElem (Vector u16 8) Nat u16 (fun x i => i < 8) Vector.instGetElemNatLt input.toVec 7 _ = var_7
    bv_decide


end aes_core.transpose_u16x8
