
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Std.Tactic.Do.Syntax
import Utilities

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace aes_core.sub_bytes

def SBOX_mat : Vector (Vector (BitVec 8) 16) 16 := #v[
    #v[ 0x63#8, 0x7C#8, 0x77#8, 0x7B#8, 0xF2#8, 0x6B#8, 0x6F#8, 0xC5#8, 0x30#8, 0x01#8, 0x67#8, 0x2B#8, 0xFE#8, 0xD7#8, 0xAB#8, 0x76#8 ],
    #v[ 0xCA#8, 0x82#8, 0xC9#8, 0x7D#8, 0xFA#8, 0x59#8, 0x47#8, 0xF0#8, 0xAD#8, 0xD4#8, 0xA2#8, 0xAF#8, 0x9C#8, 0xA4#8, 0x72#8, 0xC0#8 ],
    #v[ 0xB7#8, 0xFD#8, 0x93#8, 0x26#8, 0x36#8, 0x3F#8, 0xF7#8, 0xCC#8, 0x34#8, 0xA5#8, 0xE5#8, 0xF1#8, 0x71#8, 0xD8#8, 0x31#8, 0x15#8 ],
    #v[ 0x04#8, 0xC7#8, 0x23#8, 0xC3#8, 0x18#8, 0x96#8, 0x05#8, 0x9A#8, 0x07#8, 0x12#8, 0x80#8, 0xE2#8, 0xEB#8, 0x27#8, 0xB2#8, 0x75#8 ],
    #v[ 0x09#8, 0x83#8, 0x2C#8, 0x1A#8, 0x1B#8, 0x6E#8, 0x5A#8, 0xA0#8, 0x52#8, 0x3B#8, 0xD6#8, 0xB3#8, 0x29#8, 0xE3#8, 0x2F#8, 0x84#8 ],
    #v[ 0x53#8, 0xD1#8, 0x00#8, 0xED#8, 0x20#8, 0xFC#8, 0xB1#8, 0x5B#8, 0x6A#8, 0xCB#8, 0xBE#8, 0x39#8, 0x4A#8, 0x4C#8, 0x58#8, 0xCF#8 ],
    #v[ 0xD0#8, 0xEF#8, 0xAA#8, 0xFB#8, 0x43#8, 0x4D#8, 0x33#8, 0x85#8, 0x45#8, 0xF9#8, 0x02#8, 0x7F#8, 0x50#8, 0x3C#8, 0x9F#8, 0xA8#8 ],
    #v[ 0x51#8, 0xA3#8, 0x40#8, 0x8F#8, 0x92#8, 0x9D#8, 0x38#8, 0xF5#8, 0xBC#8, 0xB6#8, 0xDA#8, 0x21#8, 0x10#8, 0xFF#8, 0xF3#8, 0xD2#8 ],
    #v[ 0xCD#8, 0x0C#8, 0x13#8, 0xEC#8, 0x5F#8, 0x97#8, 0x44#8, 0x17#8, 0xC4#8, 0xA7#8, 0x7E#8, 0x3D#8, 0x64#8, 0x5D#8, 0x19#8, 0x73#8 ],
    #v[ 0x60#8, 0x81#8, 0x4F#8, 0xDC#8, 0x22#8, 0x2A#8, 0x90#8, 0x88#8, 0x46#8, 0xEE#8, 0xB8#8, 0x14#8, 0xDE#8, 0x5E#8, 0x0B#8, 0xDB#8 ],
    #v[ 0xE0#8, 0x32#8, 0x3A#8, 0x0A#8, 0x49#8, 0x06#8, 0x24#8, 0x5C#8, 0xC2#8, 0xD3#8, 0xAC#8, 0x62#8, 0x91#8, 0x95#8, 0xE4#8, 0x79#8 ],
    #v[ 0xE7#8, 0xC8#8, 0x37#8, 0x6D#8, 0x8D#8, 0xD5#8, 0x4E#8, 0xA9#8, 0x6C#8, 0x56#8, 0xF4#8, 0xEA#8, 0x65#8, 0x7A#8, 0xAE#8, 0x08#8 ],
    #v[ 0xBA#8, 0x78#8, 0x25#8, 0x2E#8, 0x1C#8, 0xA6#8, 0xB4#8, 0xC6#8, 0xE8#8, 0xDD#8, 0x74#8, 0x1F#8, 0x4B#8, 0xBD#8, 0x8B#8, 0x8A#8 ],
    #v[ 0x70#8, 0x3E#8, 0xB5#8, 0x66#8, 0x48#8, 0x03#8, 0xF6#8, 0x0E#8, 0x61#8, 0x35#8, 0x57#8, 0xB9#8, 0x86#8, 0xC1#8, 0x1D#8, 0x9E#8 ],
    #v[ 0xE1#8, 0xF8#8, 0x98#8, 0x11#8, 0x69#8, 0xD9#8, 0x8E#8, 0x94#8, 0x9B#8, 0x1E#8, 0x87#8, 0xE9#8, 0xCE#8, 0x55#8, 0x28#8, 0xDF#8 ],
    #v[ 0x8C#8, 0xA1#8, 0x89#8, 0x0D#8, 0xBF#8, 0xE6#8, 0x42#8, 0x68#8, 0x41#8, 0x99#8, 0x2D#8, 0x0F#8, 0xB0#8, 0x54#8, 0xBB#8, 0x16#8 ] ]

  def SBOX : BitVec 2048 :=
    0x63#8 ++ 0x7C#8 ++ 0x77#8 ++ 0x7B#8 ++ 0xF2#8 ++ 0x6B#8 ++ 0x6F#8 ++ 0xC5#8 ++ 0x30#8 ++ 0x01#8 ++ 0x67#8 ++ 0x2B#8 ++ 0xFE#8 ++ 0xD7#8 ++ 0xAB#8 ++ 0x76#8 ++
    0xCA#8 ++ 0x82#8 ++ 0xC9#8 ++ 0x7D#8 ++ 0xFA#8 ++ 0x59#8 ++ 0x47#8 ++ 0xF0#8 ++ 0xAD#8 ++ 0xD4#8 ++ 0xA2#8 ++ 0xAF#8 ++ 0x9C#8 ++ 0xA4#8 ++ 0x72#8 ++ 0xC0#8 ++
    0xB7#8 ++ 0xFD#8 ++ 0x93#8 ++ 0x26#8 ++ 0x36#8 ++ 0x3F#8 ++ 0xF7#8 ++ 0xCC#8 ++ 0x34#8 ++ 0xA5#8 ++ 0xE5#8 ++ 0xF1#8 ++ 0x71#8 ++ 0xD8#8 ++ 0x31#8 ++ 0x15#8 ++
    0x04#8 ++ 0xC7#8 ++ 0x23#8 ++ 0xC3#8 ++ 0x18#8 ++ 0x96#8 ++ 0x05#8 ++ 0x9A#8 ++ 0x07#8 ++ 0x12#8 ++ 0x80#8 ++ 0xE2#8 ++ 0xEB#8 ++ 0x27#8 ++ 0xB2#8 ++ 0x75#8 ++
    0x09#8 ++ 0x83#8 ++ 0x2C#8 ++ 0x1A#8 ++ 0x1B#8 ++ 0x6E#8 ++ 0x5A#8 ++ 0xA0#8 ++ 0x52#8 ++ 0x3B#8 ++ 0xD6#8 ++ 0xB3#8 ++ 0x29#8 ++ 0xE3#8 ++ 0x2F#8 ++ 0x84#8 ++
    0x53#8 ++ 0xD1#8 ++ 0x00#8 ++ 0xED#8 ++ 0x20#8 ++ 0xFC#8 ++ 0xB1#8 ++ 0x5B#8 ++ 0x6A#8 ++ 0xCB#8 ++ 0xBE#8 ++ 0x39#8 ++ 0x4A#8 ++ 0x4C#8 ++ 0x58#8 ++ 0xCF#8 ++
    0xD0#8 ++ 0xEF#8 ++ 0xAA#8 ++ 0xFB#8 ++ 0x43#8 ++ 0x4D#8 ++ 0x33#8 ++ 0x85#8 ++ 0x45#8 ++ 0xF9#8 ++ 0x02#8 ++ 0x7F#8 ++ 0x50#8 ++ 0x3C#8 ++ 0x9F#8 ++ 0xA8#8 ++
    0x51#8 ++ 0xA3#8 ++ 0x40#8 ++ 0x8F#8 ++ 0x92#8 ++ 0x9D#8 ++ 0x38#8 ++ 0xF5#8 ++ 0xBC#8 ++ 0xB6#8 ++ 0xDA#8 ++ 0x21#8 ++ 0x10#8 ++ 0xFF#8 ++ 0xF3#8 ++ 0xD2#8 ++
    0xCD#8 ++ 0x0C#8 ++ 0x13#8 ++ 0xEC#8 ++ 0x5F#8 ++ 0x97#8 ++ 0x44#8 ++ 0x17#8 ++ 0xC4#8 ++ 0xA7#8 ++ 0x7E#8 ++ 0x3D#8 ++ 0x64#8 ++ 0x5D#8 ++ 0x19#8 ++ 0x73#8 ++
    0x60#8 ++ 0x81#8 ++ 0x4F#8 ++ 0xDC#8 ++ 0x22#8 ++ 0x2A#8 ++ 0x90#8 ++ 0x88#8 ++ 0x46#8 ++ 0xEE#8 ++ 0xB8#8 ++ 0x14#8 ++ 0xDE#8 ++ 0x5E#8 ++ 0x0B#8 ++ 0xDB#8 ++
    0xE0#8 ++ 0x32#8 ++ 0x3A#8 ++ 0x0A#8 ++ 0x49#8 ++ 0x06#8 ++ 0x24#8 ++ 0x5C#8 ++ 0xC2#8 ++ 0xD3#8 ++ 0xAC#8 ++ 0x62#8 ++ 0x91#8 ++ 0x95#8 ++ 0xE4#8 ++ 0x79#8 ++
    0xE7#8 ++ 0xC8#8 ++ 0x37#8 ++ 0x6D#8 ++ 0x8D#8 ++ 0xD5#8 ++ 0x4E#8 ++ 0xA9#8 ++ 0x6C#8 ++ 0x56#8 ++ 0xF4#8 ++ 0xEA#8 ++ 0x65#8 ++ 0x7A#8 ++ 0xAE#8 ++ 0x08#8 ++
    0xBA#8 ++ 0x78#8 ++ 0x25#8 ++ 0x2E#8 ++ 0x1C#8 ++ 0xA6#8 ++ 0xB4#8 ++ 0xC6#8 ++ 0xE8#8 ++ 0xDD#8 ++ 0x74#8 ++ 0x1F#8 ++ 0x4B#8 ++ 0xBD#8 ++ 0x8B#8 ++ 0x8A#8 ++
    0x70#8 ++ 0x3E#8 ++ 0xB5#8 ++ 0x66#8 ++ 0x48#8 ++ 0x03#8 ++ 0xF6#8 ++ 0x0E#8 ++ 0x61#8 ++ 0x35#8 ++ 0x57#8 ++ 0xB9#8 ++ 0x86#8 ++ 0xC1#8 ++ 0x1D#8 ++ 0x9E#8 ++
    0xE1#8 ++ 0xF8#8 ++ 0x98#8 ++ 0x11#8 ++ 0x69#8 ++ 0xD9#8 ++ 0x8E#8 ++ 0x94#8 ++ 0x9B#8 ++ 0x1E#8 ++ 0x87#8 ++ 0xE9#8 ++ 0xCE#8 ++ 0x55#8 ++ 0x28#8 ++ 0xDF#8 ++
    0x8C#8 ++ 0xA1#8 ++ 0x89#8 ++ 0x0D#8 ++ 0xBF#8 ++ 0xE6#8 ++ 0x42#8 ++ 0x68#8 ++ 0x41#8 ++ 0x99#8 ++ 0x2D#8 ++ 0x0F#8 ++ 0xB0#8 ++ 0x54#8 ++ 0xBB#8 ++ 0x16#8

def get_elem_SBOX (row col : Nat) : BitVec 8:=
  (SBOX >>> (((15 - row) * 16 + (15 - col)) * 8)).setWidth 8

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
theorem get_elem_correct (row col : Nat) (h1 : row < 16) (h2 : col < 16):
  get_elem_SBOX row col = SBOX_mat[row][col] := by
  unfold get_elem_SBOX SBOX SBOX_mat
  match row with
  | n + 16 => omega
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15  =>
    match col with
    | n + 16 => omega
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15  => rfl

def sub_bytes_state_spec (st : Vector u16 8) : Vector u16 8 :=
  (16 : Nat).fold (init := zero_array) fun elem_indx h res =>
    let elem := get_elem st elem_indx h
    let row := (BitVec.extractLsb 7 4 elem).toFin
    let col := (BitVec.extractLsb 3 0 elem).toFin
    let new_elem := get_elem_SBOX row col
    set_elem res elem_indx new_elem

theorem sbox_th (st : Vector u16 8) (el : BitVec 4) (h : el < 16):
  let ⟨el_val, el_h⟩ := el
  let elem := get_elem st el_val el_h
  let row := (BitVec.extractLsb 7 4 elem).toFin
  let col := (BitVec.extractLsb 3 0 elem).toFin
  let new_elem := get_elem_SBOX row col
  get_elem (set_elem zero_array el_val new_elem) el_val el_h = 0x22#8 :=
by
  unfold get_elem set_elem zero_array get_elem_SBOX SBOX
  simp
  bv_decide

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


set_option maxHeartbeats 1000000000
theorem sub_bytes_correct_some_array :
⦃ ⌜ true = true ⌝ ⦄
sub_bytes_state some_array
⦃ ⇓ ⟨res_output⟩ =>
    ⌜ (sub_bytes_state_spec some_array.toVec) = res_output ⌝ ⦄
:= by

  unfold sub_bytes_state
  hax_mvcgen <;> simp at *
  .
    ext i
    match i with
    | n + 16 => omega
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
      unfold sub_bytes_state_spec
      simp only [zero_array, get_elem_SBOX, get_elem, SBOX, set_elem]
      rename_auto_n 45
      simp only [var_1, var_3, var_5, var_7, var_9, var_11, var_13, var_24]
      simp
      unfold some_array
      simp
      bv_normalize
  all_goals grind

set_option maxHeartbeats 1000000000
theorem sub_bytes_correct (st : Vector u16 8):
⦃ ⌜ true = true ⌝ ⦄
sub_bytes_state (RustArray.ofVec st)
⦃ ⇓ ⟨res_output⟩ =>
    ⌜ (sub_bytes_state_spec st)[0] = res_output[0] ⌝ ⦄
:= by
    unfold sub_bytes_state
    hax_mvcgen <;> simp at *
    .
      unfold sub_bytes_state_spec
      simp only [zero_array, get_elem_SBOX, get_elem, SBOX, set_elem]
      rename_auto_n 45
      simp only [var_1, var_3, var_5, var_7, var_9, var_11, var_13, var_24]
      simp
      sorry
      --bv_decide

    all_goals grind



end aes_core.sub_bytes
