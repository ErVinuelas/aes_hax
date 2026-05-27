
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import transpose_u16x8
import transpose_u8x16
import sub_bytes
import shift_rows_state
import LibcruxAesgcm

import mix_columns
import xor_key1_state

import aes_keygen_assist
import key_expansion_step

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false



namespace libcrux_aesgcm.aes

--  AES block size
def AES_BLOCK_LEN : usize := (16 : usize)

end libcrux_aesgcm.aes


namespace libcrux_aesgcm.platform.portable.aes_core

abbrev State : Type := (RustArray u16 8)

@[spec]
def new_state (_ : rust_primitives.hax.Tuple0) : RustM (RustArray u16 8) := do
  (rust_primitives.hax.repeat (0 : u16) (8 : usize))

@[spec]
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

@[spec]
def deinterleave_u8_1 (i0 : u16) :
    RustM (rust_primitives.hax.Tuple2 u8 u8) := do
  let x : u16 ← (i0 &&&? (21845 : u16));
  let x : u16 ← ((← (x |||? (← (x >>>? (1 : i32))))) &&&? (13107 : u16));
  let x : u16 ← ((← (x |||? (← (x >>>? (2 : i32))))) &&&? (3855 : u16));
  let x : u16 ← ((← (x |||? (← (x >>>? (4 : i32))))) &&&? (255 : u16));
  let y : u16 ← ((← (i0 >>>? (1 : i32))) &&&? (21845 : u16));
  let y : u16 ← ((← (y |||? (← (y >>>? (1 : i32))))) &&&? (13107 : u16));
  let y : u16 ← ((← (y |||? (← (y >>>? (2 : i32))))) &&&? (3855 : u16));
  let y : u16 ← ((← (y |||? (← (y >>>? (4 : i32))))) &&&? (255 : u16));
  (pure (rust_primitives.hax.Tuple2.mk
    (← (rust_primitives.hax.cast_op x : RustM u8))
    (← (rust_primitives.hax.cast_op y : RustM u8))))

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


@[spec]
def xnor (a : u16) (b : u16) : RustM u16 := do (~? (← (a ^^^? b)))

set_option maxRecDepth 1000
@[spec]
def sub_bytes_state (st : (RustArray u16 8)) : RustM (RustArray u16 8) := do
  let u0 : u16 ← st[(7 : usize)]_?;
  let u1 : u16 ← st[(6 : usize)]_?;
  let u2 : u16 ← st[(5 : usize)]_?;
  let u3 : u16 ← st[(4 : usize)]_?;
  let u4 : u16 ← st[(3 : usize)]_?;
  let u5 : u16 ← st[(2 : usize)]_?;
  let u6 : u16 ← st[(1 : usize)]_?;
  let u7 : u16 ← st[(0 : usize)]_?;
  let t1 : u16 ← (u6 ^^^? u4);
  let t2 : u16 ← (u3 ^^^? u0);
  let t3 : u16 ← (u1 ^^^? u2);
  let t4 : u16 ← (u7 ^^^? t3);
  let t5 : u16 ← (t1 ^^^? t2);
  let t6 : u16 ← (u1 ^^^? u5);
  let t7 : u16 ← (u0 ^^^? u6);
  let t8 : u16 ← (t1 ^^^? t6);
  let t9 : u16 ← (u6 ^^^? t4);
  let t10 : u16 ← (u3 ^^^? t4);
  let t11 : u16 ← (u7 ^^^? t5);
  let t12 : u16 ← (t5 ^^^? t6);
  let t13 : u16 ← (u2 ^^^? u5);
  let t14 : u16 ← (t3 ^^^? t5);
  let t15 : u16 ← (u5 ^^^? t7);
  let t16 : u16 ← (u0 ^^^? u5);
  let t17 : u16 ← (u7 ^^^? t8);
  let t18 : u16 ← (u6 ^^^? u5);
  let t19 : u16 ← (t2 ^^^? t18);
  let t20 : u16 ← (t4 ^^^? t15);
  let t21 : u16 ← (t1 ^^^? t13);
  let t22 : u16 ← (u0 ^^^? t4);
  let t39 : u16 ← (t21 ^^^? t5);
  let t40 : u16 ← (t21 ^^^? t7);
  let t41 : u16 ← (t7 ^^^? t19);
  let t42 : u16 ← (t16 ^^^? t14);
  let t43 : u16 ← (t22 ^^^? t17);
  let t44 : u16 ← (t19 &&&? t5);
  let t45 : u16 ← (t20 &&&? t11);
  let t46 : u16 ← (t12 ^^^? t44);
  let t47 : u16 ← (t10 &&&? u7);
  let t48 : u16 ← (t47 ^^^? t44);
  let t49 : u16 ← (t7 &&&? t21);
  let t50 : u16 ← (t9 &&&? t4);
  let t51 : u16 ← (t40 ^^^? t49);
  let t52 : u16 ← (t22 &&&? t17);
  let t53 : u16 ← (t52 ^^^? t49);
  let t54 : u16 ← (t2 &&&? t8);
  let t55 : u16 ← (t41 &&&? t39);
  let t56 : u16 ← (t55 ^^^? t54);
  let t57 : u16 ← (t16 &&&? t14);
  let t58 : u16 ← (t57 ^^^? t54);
  let t59 : u16 ← (t46 ^^^? t45);
  let t60 : u16 ← (t48 ^^^? t42);
  let t61 : u16 ← (t51 ^^^? t50);
  let t62 : u16 ← (t53 ^^^? t58);
  let t63 : u16 ← (t59 ^^^? t56);
  let t64 : u16 ← (t60 ^^^? t58);
  let t65 : u16 ← (t61 ^^^? t56);
  let t66 : u16 ← (t62 ^^^? t43);
  let t67 : u16 ← (t65 ^^^? t66);
  let t68 : u16 ← (t65 &&&? t63);
  let t69 : u16 ← (t64 ^^^? t68);
  let t70 : u16 ← (t63 ^^^? t64);
  let t71 : u16 ← (t66 ^^^? t68);
  let t72 : u16 ← (t71 &&&? t70);
  let t73 : u16 ← (t69 &&&? t67);
  let t74 : u16 ← (t63 &&&? t66);
  let t75 : u16 ← (t70 &&&? t74);
  let t76 : u16 ← (t70 ^^^? t68);
  let t77 : u16 ← (t64 &&&? t65);
  let t78 : u16 ← (t67 &&&? t77);
  let t79 : u16 ← (t67 ^^^? t68);
  let t80 : u16 ← (t64 ^^^? t72);
  let t81 : u16 ← (t75 ^^^? t76);
  let t82 : u16 ← (t66 ^^^? t73);
  let t83 : u16 ← (t78 ^^^? t79);
  let t84 : u16 ← (t81 ^^^? t83);
  let t85 : u16 ← (t80 ^^^? t82);
  let t86 : u16 ← (t80 ^^^? t81);
  let t87 : u16 ← (t82 ^^^? t83);
  let t88 : u16 ← (t85 ^^^? t84);
  let t89 : u16 ← (t87 &&&? t5);
  let t90 : u16 ← (t83 &&&? t11);
  let t91 : u16 ← (t82 &&&? u7);
  let t92 : u16 ← (t86 &&&? t21);
  let t93 : u16 ← (t81 &&&? t4);
  let t94 : u16 ← (t80 &&&? t17);
  let t95 : u16 ← (t85 &&&? t8);
  let t96 : u16 ← (t88 &&&? t39);
  let t97 : u16 ← (t84 &&&? t14);
  let t98 : u16 ← (t87 &&&? t19);
  let t99 : u16 ← (t83 &&&? t20);
  let t100 : u16 ← (t82 &&&? t10);
  let t101 : u16 ← (t86 &&&? t7);
  let t102 : u16 ← (t81 &&&? t9);
  let t103 : u16 ← (t80 &&&? t22);
  let t104 : u16 ← (t85 &&&? t2);
  let t105 : u16 ← (t88 &&&? t41);
  let t106 : u16 ← (t84 &&&? t16);
  let t107 : u16 ← (t104 ^^^? t105);
  let t108 : u16 ← (t93 ^^^? t99);
  let t109 : u16 ← (t96 ^^^? t107);
  let t110 : u16 ← (t98 ^^^? t108);
  let t111 : u16 ← (t91 ^^^? t101);
  let t112 : u16 ← (t89 ^^^? t92);
  let t113 : u16 ← (t107 ^^^? t112);
  let t114 : u16 ← (t90 ^^^? t110);
  let t115 : u16 ← (t89 ^^^? t95);
  let t116 : u16 ← (t94 ^^^? t102);
  let t117 : u16 ← (t97 ^^^? t103);
  let t118 : u16 ← (t91 ^^^? t114);
  let t119 : u16 ← (t111 ^^^? t117);
  let t120 : u16 ← (t100 ^^^? t108);
  let t121 : u16 ← (t92 ^^^? t95);
  let t122 : u16 ← (t110 ^^^? t121);
  let t123 : u16 ← (t106 ^^^? t119);
  let t124 : u16 ← (t104 ^^^? t115);
  let t125 : u16 ← (t111 ^^^? t116);
  let t128 : u16 ← (t94 ^^^? t107);
  let t131 : u16 ← (t93 ^^^? t101);
  let t132 : u16 ← (t112 ^^^? t120);
  let t134 : u16 ← (t97 ^^^? t116);
  let t135 : u16 ← (t131 ^^^? t134);
  let t136 : u16 ← (t93 ^^^? t115);
  let t138 : u16 ← (t119 ^^^? t132);
  let t140 : u16 ← (t114 ^^^? t136);
  let s0 : u16 ← (t109 ^^^? t122);
  let s2 : u16 ← (xnor t123 t124);
  let s3 : u16 ← (t113 ^^^? t114);
  let s4 : u16 ← (t118 ^^^? t128);
  let s7 : u16 ← (xnor t113 t125);
  let s6 : u16 ← (xnor t109 t135);
  let s5 : u16 ← (t109 ^^^? t138);
  let s1 : u16 ← (xnor t109 t140);
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (0 : usize)
      s7);
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (1 : usize)
      s6);
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (2 : usize)
      s5);
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (3 : usize)
      s4);
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (4 : usize)
      s3);
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (5 : usize)
      s2);
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (6 : usize)
      s1);
  let st : (RustArray u16 8) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      st
      (7 : usize)
      s0);
  (pure st)

@[spec]
def shift_row_u16 (input : u16) : RustM u16 := do
  ((← ((← ((← ((← ((← ((← (input &&&? (4369 : u16)))
              |||? (← ((← (input &&&? (8736 : u16))) >>>? (4 : i32)))))
            |||? (← ((← (input &&&? (2 : u16))) <<<? (12 : i32)))))
          |||? (← ((← (input &&&? (17408 : u16))) >>>? (8 : i32)))))
        |||? (← ((← (input &&&? (68 : u16))) <<<? (8 : i32)))))
      |||? (← ((← (input &&&? (32768 : u16))) >>>? (12 : i32)))))
    |||? (← ((← (input &&&? (2184 : u16))) <<<? (4 : i32))))

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

@[spec]
def aes_enc (st : (RustArray u16 8)) (key : (RustArray u16 8)) :
    RustM (RustArray u16 8) := do
  let st : (RustArray u16 8) ← (sub_bytes_state st);
  let st : (RustArray u16 8) ← (shift_rows_state st);
  let st : (RustArray u16 8) ← (mix_columns_state st);
  let st : (RustArray u16 8) ← (xor_key1_state st key);
  (pure st)

@[spec]
def aes_enc_last (st : (RustArray u16 8)) (key : (RustArray u16 8)) :
    RustM (RustArray u16 8) := do
  let st : (RustArray u16 8) ← (sub_bytes_state st);
  let st : (RustArray u16 8) ← (shift_rows_state st);
  let st : (RustArray u16 8) ← (xor_key1_state st key);
  (pure st)

end libcrux_aesgcm.platform.portable.aes_core

namespace libcrux_aesgcm.platform

--  The AES state.
class AESState.AssociatedTypes (Self : Type) where
  [trait_constr_AESState_i0 : core_models.clone.Clone.AssociatedTypes Self]
  [trait_constr_AESState_i1 : core_models.fmt.Debug.AssociatedTypes Self]

attribute [instance_reducible, instance]
  AESState.AssociatedTypes.trait_constr_AESState_i0

attribute [instance_reducible, instance]
  AESState.AssociatedTypes.trait_constr_AESState_i1

class AESState (Self : Type)
  [associatedTypes : outParam (AESState.AssociatedTypes (Self : Type))]
  where
  [trait_constr_AESState_i0 : core_models.clone.Clone Self]
  [trait_constr_AESState_i1 : core_models.fmt.Debug Self]
  new (Self) : (rust_primitives.hax.Tuple0 -> RustM Self)
  load_block (Self) : (Self -> (RustSlice u8) -> RustM Self)
  store_block (Self) : (Self -> (RustSlice u8) -> RustM (RustSlice u8))
  xor_block (Self) :
    (Self -> (RustSlice u8) -> (RustSlice u8) -> RustM (RustSlice u8))
  xor_key (Self) : (Self -> Self -> RustM Self)
  aes_enc (Self) : (Self -> Self -> RustM Self)
  aes_enc_last (Self) : (Self -> Self -> RustM Self)
  aes_keygen_assist0 (Self) (RCON : i32) : (Self -> Self -> RustM Self)
  aes_keygen_assist1 (Self) : (Self -> Self -> RustM Self)
  key_expansion_step (Self) : (Self -> Self -> RustM Self)
attribute [instance_reducible, instance] AESState.trait_constr_AESState_i0

attribute [instance_reducible, instance] AESState.trait_constr_AESState_i1

end libcrux_aesgcm.platform


namespace libcrux_aesgcm.platform.portable.aes_core

@[reducible] instance Impl.AssociatedTypes :
  libcrux_aesgcm.platform.AESState.AssociatedTypes (RustArray u16 8)
  where

instance Impl : libcrux_aesgcm.platform.AESState (RustArray u16 8) where
  new := fun (_ : rust_primitives.hax.Tuple0) => do
    (new_state rust_primitives.hax.Tuple0.mk)
  load_block := fun (self : (RustArray u16 8)) (b : (RustSlice u8)) => do
    let _ ←
      if true then do
        let _ ←
          (hax_lib.assert
            (← ((← (core_models.slice.Impl.len u8 b)) ==? (16 : usize))));
        (pure rust_primitives.hax.Tuple0.mk)
      else do
        (pure rust_primitives.hax.Tuple0.mk);
    let self : (RustArray u16 8) ←
      (aes_core.transpose_u8x16.transpose_u8x16
        (← (core_models.result.Impl.unwrap
          (RustArray u8 16)
          core_models.array.TryFromSliceError
          (← (core_models.convert.TryInto.try_into
            (RustSlice u8)
            (RustArray u8 16) b))))
        self);
    (pure self)
  store_block :=
    sorry
  xor_block :=
    sorry
  xor_key := fun (self : (RustArray u16 8)) (key : (RustArray u16 8)) => do
    let self : (RustArray u16 8) ← (xor_key1_state self key);
    (pure self)
  aes_enc := fun (self : (RustArray u16 8)) (key : (RustArray u16 8)) => do
    let self : (RustArray u16 8) ← (aes_enc self key);
    (pure self)
  aes_enc_last := fun (self : (RustArray u16 8)) (key : (RustArray u16 8)) => do
    let self : (RustArray u16 8) ← (aes_enc_last self key);
    (pure self)
  aes_keygen_assist0 :=
    fun (RCON : i32) (self : (RustArray u16 8)) (prev : (RustArray u16 8)) => do
    let self : (RustArray u16 8) ←
      (aes_core.aes_keygen.aes_keygen_assist0
        self
        prev
        (← (rust_primitives.hax.cast_op RCON : RustM u8)));
    (pure self)
  aes_keygen_assist1 :=
    fun (self : (RustArray u16 8)) (prev : (RustArray u16 8)) => do
    let self : (RustArray u16 8) ← (aes_core.aes_keygen.aes_keygen_assist1 self prev);
    (pure self)
  key_expansion_step :=
    fun (self : (RustArray u16 8)) (prev : (RustArray u16 8)) => do
    let self : (RustArray u16 8) ← (aes_core.key_expansion_step.key_expansion_step self prev);
    (pure self)

end libcrux_aesgcm.platform.portable.aes_core

namespace libcrux_aesgcm.aes_gcm_128

def GCM_KEY_LEN : usize := (16 : usize)

end libcrux_aesgcm.aes_gcm_128


namespace libcrux_aesgcm.ctr.aes128_ctr

--  128 - Key expansion
@[spec]
def key_expansion_step
    (T : Type)
    [trait_constr_key_expansion_associated_type_i0 :
      libcrux_aesgcm.platform.AESState.AssociatedTypes
      T]
    [trait_constr_key_expansion_i0 : libcrux_aesgcm.platform.AESState T ]
    (key : (RustSlice u8)) :
    RustM (RustArray T 11) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 key))
            ==? libcrux_aesgcm.aes_gcm_128.GCM_KEY_LEN)));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let keyex : (RustArray T 11) ←
    (core_models.array.from_fn T ((11 : usize)) (usize -> RustM T)
      (fun _ =>
        (do
        (libcrux_aesgcm.platform.AESState.new T rust_primitives.hax.Tuple0.mk) :
        RustM T)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (0 : usize)
      (← (libcrux_aesgcm.platform.AESState.load_block
        T (← keyex[(0 : usize)]_?) key)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((1 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (1 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((1 : i32)) (← keyex[(1 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (1 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(1 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((2 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (2 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((2 : i32)) (← keyex[(2 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (2 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(2 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((3 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (3 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((4 : i32)) (← keyex[(3 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (3 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(3 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((4 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (4 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((8 : i32)) (← keyex[(4 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (4 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(4 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((5 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (5 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((16 : i32)) (← keyex[(5 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (5 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(5 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((6 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (6 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((32 : i32)) (← keyex[(6 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (6 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(6 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((7 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (7 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((64 : i32)) (← keyex[(7 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (7 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(7 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((8 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (8 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((128 : i32)) (← keyex[(8 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (8 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(8 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((9 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (9 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((27 : i32)) (← keyex[(9 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (9 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(9 : usize)]_?) prev)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((10 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (10 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((54 : i32)) (← keyex[(10 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (10 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(10 : usize)]_?) prev)));
  (pure keyex)


@[spec]
def key_expansion_small
    (T : Type)
    [trait_constr_key_expansion_associated_type_i0 :
      libcrux_aesgcm.platform.AESState.AssociatedTypes
      T]
    [trait_constr_key_expansion_i0 : libcrux_aesgcm.platform.AESState T ]
    (key : (RustSlice u8)) :
    RustM (RustArray T 11) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 key))
            ==? libcrux_aesgcm.aes_gcm_128.GCM_KEY_LEN)));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let keyex : (RustArray T 11) ←
    (core_models.array.from_fn T ((11 : usize)) (usize -> RustM T)
      (fun _ =>
        (do
        (libcrux_aesgcm.platform.AESState.new T rust_primitives.hax.Tuple0.mk) :
        RustM T)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (0 : usize)
      (← (libcrux_aesgcm.platform.AESState.load_block
        T (← keyex[(0 : usize)]_?) key)));
  let prev : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((1 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (1 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((1 : i32)) (← keyex[(1 : usize)]_?) prev)));
  let keyex : (RustArray T 11) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (1 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(1 : usize)]_?) prev)));
  (pure keyex)

def key_expansion_spec (i : Nat) (hi : i < 11) (key : RustSlice u8) (h : key.val.size = 16) :=
  let rcon_vec : Vector u8 11 := #v[0, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]
  if i = 0 then
    let fst := (aes_core.transpose_u8x16.transposeU8toU16 (RustArray.ofVec (@Vector.mk u8 16 key.val h))).toVec
    #v[get_word fst 3, get_word fst 2, get_word fst 1, get_word fst 0]
  else
    let prev := key_expansion_spec (i - 1) (by grind) key h

    let new_chunk := (aes_core.aes_keygen.rotword (aes_core.aes_keygen.subword (prev[0])))
    let word_first := #v[new_chunk[0], new_chunk[1], new_chunk[2], rcon_vec[i].toBitVec ^^^ new_chunk[3]]

    let row_next j := word_first

    let row_3 := xor_word (row_next 3) (prev[3])
    let row_2 := xor_word (row_next 2) (xor_word (prev[2]) (prev[3]))
    let row_1 := xor_word (row_next 1) (xor_word (prev[1]) (xor_word (prev[2]) (prev[3])))
    let row_0 := xor_word (row_next 0) (xor_word (prev[0]) (xor_word (prev[1]) (xor_word (prev[2]) (prev[3]))))

    #v[row_0, row_1, row_2, row_3]

set_option maxHeartbeats 10000000000000
set_option maxRecDepth 100000
theorem key_expansion_correct (key : RustSlice u8) (h : key.val.size = 16) :
⦃ ⌜ USize64.ofNat key.val.size = libcrux_aesgcm.aes_gcm_128.GCM_KEY_LEN /\ key.val.size = 16 ⌝ ⦄
  key_expansion_step libcrux_aesgcm.platform.portable.aes_core.State key
⦃ ⇓ ⟨res⟩ =>
    ⌜
    ∀ (i : Nat) (hi : i < 11),
    (key_expansion_spec i hi key (by grind))
    =
    let r := (res[i]'(by grind)).toVec
    #v[get_word r 3, get_word r 2, get_word r 1, get_word r 0 ]
    ⌝ ⦄ :=
  by
    unfold key_expansion_step
    unfold platform.portable.aes_core.Impl
    simp
    unfold aes_gcm_128.GCM_KEY_LEN core_models.clone.Clone.clone
    unfold platform.AESState.trait_constr_AESState_i0
    simp
    unfold core_models.marker.Copy.trait_constr_Copy_i0
    unfold core_models.result.Impl.unwrap core_models.convert.TryInto.try_into
    unfold core_models.convert.instTryIntoRustSliceRustArray core_models.slice.Impl.len
    unfold rust_primitives.slice.slice_length core_models.marker.Impl_3
    unfold core_models.array.from_fn
    unfold rust_primitives.slice.array_from_fn platform.portable.aes_core.State
    simp
    hax_mvcgen <;> simp at *
    .
      have hnat : 8 = @ToNat.toNat usize instToNatUsize 8 := by decide
      simp only [hnat]
      simp at *
      rename_auto_n 8
      obtain ⟨h1, h2⟩ := var_0
      simp only [h2]
      simp
      hax_mvcgen[
        aes_core.transpose_u8x16_correct,
        aes_core.aes_keygen.aes_keygen_assist0_correct,
        aes_core.key_expansion_step.key_expansion_correct2
      ] <;> simp at *
      .
        unfold key_expansion_spec
        unfold core_models.clone.Impl
        simp
        intros
        hax_mvcgen [
          aes_core.aes_keygen.aes_keygen_assist0_correct,
          aes_core.key_expansion_step.key_expansion_correct2
        ] <;> try (exact 1#8)
        .
          intros
          rename_auto_n 150
          simp at *
          have hi1 : Int32.toUInt8 1 = 1 := by decide
          simp only [hi1] at *
          have hi2 : Int32.toUInt8 2 = 2 := by decide
          simp only [hi2] at *
          have hi4 : Int32.toUInt8 4 = 4 := by decide
          simp only [hi4] at *
          have hi8 : Int32.toUInt8 8 = 8 := by decide
          simp only [hi8] at *
          have hi0x10 : Int32.toUInt8 0x10 = 0x10 := by decide
          simp only [hi0x10] at *
          have hi0x20 : Int32.toUInt8 0x20 = 0x20 := by decide
          simp only [hi0x20] at *
          have hi0x40 : Int32.toUInt8 0x40 = 0x40 := by decide
          simp only [hi0x40] at *
          have hi0x80 : Int32.toUInt8 0x80 = 0x80 := by decide
          simp only [hi0x80] at *
          have hi0x1b : Int32.toUInt8 0x1b = 0x1b := by decide
          simp only [hi0x1b] at *
          have hi0x36 : Int32.toUInt8 0x36 = 0x36 := by decide
          simp only [hi0x36] at *

          match var_136 with
          | n + 11 => grind
          | 0 =>
            simp only [var_8, var_28, var_15, var_41, var_54, var_67, var_80, var_93, var_106, var_119, var_132] at *
            simp only [<- var_13, <- var_26, <- var_39, <- var_52, <- var_65, <- var_78, <- var_91, <- var_104, <- var_130, <- var_117] at *
            simp only [<- var_3]
            simp only [var_6, var_21] at *
            simp

          | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 =>
              simp only [var_8, var_28, var_15, var_41, var_54, var_67, var_80, var_93, var_106, var_119, var_132] at *
              simp only [<- var_13, <- var_26, <- var_39, <- var_52, <- var_65, <- var_78, <- var_91, <- var_104, <- var_130, <- var_117] at *
              simp [var_6] at *
              simp only [var_21, var_34, var_47, var_60, var_73, var_86, var_99, var_112, var_125] at *
              simp only [var_18, var_135, var_122, var_109, var_96, var_83, var_70, var_57, var_44, var_31]

              simp [aes_core.aes_keygen.aes_keygen_first, key_expansion_spec]

              simp [<- var_3]

        all_goals grind
      all_goals grind
    all_goals grind

end libcrux_aesgcm.ctr.aes128_ctr
