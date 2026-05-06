import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
import Utilities
import transpose_u16x8
import transpose_u8x16
import shift_rows_state
import xor_key1_state
import sub_bytes

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace aes_core

--Here are the most important lemmas and the proofs associated with them

set_option maxHeartbeats 100000000
set_option hax_mvcgen.specset "bv" in
theorem transpose_u16x8_correct (input : (RustArray u16 8)) (output : (RustSlice u8)) :
⦃ ⌜ output.val.size = 16 ⌝ ⦄
aes_core.transpose_u16x8.transpose_u16x8 input output
⦃ ⇓ ⟨res_arrar, array_size⟩ =>
    ⌜ res_arrar = (aes_core.transpose_u16x8.transposeU16toU8 input).toVec.toArray ⌝ ⦄
:= by
    unfold aes_core.transpose_u16x8.transpose_u16x8

    hax_mvcgen
    <;> simp at *
    .

      ext i

      .
        rename_auto_n 57
        simp
        exact var_0
      .
        repeat(rename True => hTrue; clear hTrue)
        rename_auto_n 59
        revert var_57 var_58
        match i with
        | n + 16 => intros
                    rename_i h0 h1
                    simp at h0
                    omega
        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 =>
          intros
          unfold aes_core.transpose_u16x8.transposeU16toU8
          simp only [Array.getElem_set]
          simp only [var_56, var_55, var_54, var_53, var_52, var_51, var_50, var_49, var_48, var_47, var_46, var_45]
          simp only [aes_core.transpose_u16x8.deinterleave_u8_1_spec, aes_core.transpose_u16x8.interleave_u16_8_spec]
          simp

          simp only [<- var_3, <- var_6, <- var_8, <- var_11, <- var_13, <- var_16, <- var_18, <- var_44]

          bv_check "./sat_proofs/LibcruxAesgcm.lean-aes_core.transpose_u16x8_correct-59-10.lrat"
    all_goals try omega
    grind


set_option maxHeartbeats 1000000
set_option hax_mvcgen.specset "bv" in
theorem transpose_u8x16_correct (input : (RustArray u8 16)) (output : (RustArray u16 8)) :
⦃ ⌜ true = true ⌝ ⦄
aes_core.transpose_u8x16.transpose_u8x16 input output
⦃ ⇓ ⟨res_output⟩ =>
    ⌜ res_output = (aes_core.transpose_u8x16.transposeU8toU16 input).toVec ⌝ ⦄
:= by
    unfold aes_core.transpose_u8x16.transpose_u8x16
    hax_mvcgen[aes_core.transpose_u8x16.interleave_u8_1] <;> simp at *
    .
      ext i

      repeat (rename True => h; clear h)
      rename_auto_n 59

      rw [var_48, var_49, var_50, var_51, var_52, var_53, var_54, var_55]

      revert var_56
      match i with
      | n + 8 => intro h; contradiction
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
          intros; simp

          unfold aes_core.transpose_u8x16.transposeU8toU16; simp
          unfold aes_core.transpose_u8x16.interleave_u8_1_spec; simp

          rw [ <- var_47, <- var_2, <- var_5, <- var_7, <- var_10, <- var_12, <- var_15,
            <- var_17, <- var_20, <- var_22, <- var_25, <- var_27, <- var_30,
            <- var_32, <- var_35, <- var_37]

          bv_check "./sat_proofs/LibcruxAesgcm.lean-aes_core.transpose_u8x16_correct-96-10.lrat"

    all_goals grind

set_option maxHeartbeats 100000000
set_option hax_mvcgen.specset "bv" in
@[spec]
theorem shift_rows_state_correct (st : (RustArray u16 8)) :
⦃ ⌜ true = true ⌝ ⦄
aes_core.shift_row_state.shift_rows_state st
⦃ ⇓ ⟨res⟩ =>
    ⌜ res = (aes_core.shift_row_state.shift_rows_stat_spec st) ⌝ ⦄
:= by
    unfold aes_core.shift_row_state.shift_rows_state

    hax_mvcgen
    <;> simp at *
    .
      ext i
      match i with
      | n + 8 => intros; omega
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
        simp only [aes_core.shift_row_state.shift_rows_stat_spec] at *
        rename_auto_n 41
        simp only [Vector.getElem_map]
        simp only [var_40, var_38, var_36, var_34, var_32, var_30, var_28, var_26]
        simp only [aes_core.shift_row_state.shift_row_u16_spec]
        simp
        simp only [<- var_39, <- var_37, <- var_35, <- var_33, <- var_31, <- var_29, <- var_27, <- var_25]
    all_goals grind

set_option maxHeartbeats 100000000
set_option hax_mvcgen.specset "bv" in
@[spec]
theorem xor_key1_state_correct (st : (RustArray u16 8))(k : (RustArray u16 8)) :
⦃ ⌜ true = true ⌝ ⦄
aes_core.xor_key1_state.xor_key1_state st k
⦃ ⇓ ⟨res⟩ =>
    ⌜ res = (aes_core.xor_key1_state.xor_key1_state_spec st.toVec k.toVec) ⌝ ⦄
:= by
    unfold aes_core.xor_key1_state.xor_key1_state

    hax_mvcgen
    <;> simp at *
    .
      unfold aes_core.xor_key1_state.xor_key1_state_spec
      simp
      rename_auto_n 41
      ext i
      match i with
      | n + 8 => omega
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
        simp
        simp only [<- var_29, <- var_5, <- var_9, <- var_13, <- var_17, <- var_21, <- var_25, <- var_32, <- var_33, <- var_34, <- var_35, <- var_36, <- var_37, <- var_38, <- var_39, <- var_40]

    all_goals grind

set_option maxHeartbeats 10000000000000
set_option maxRecDepth 100000
theorem sub_bytes_correct (st : RustArray u16 8) (a : BitVec 8) (n : BitVec 4) :
⦃ ⌜ a = get_elem_bv st.toVec n ⌝ ⦄
aes_core.sub_bytes.sub_bytes_state st
⦃ ⇓ ⟨res_output⟩ =>
    ⌜ aes_core.sub_bytes.get_elem_SBOX (a.extractLsb 7 4) (a.extractLsb 3 0) = get_elem_bv res_output n  ⌝ ⦄
:= by

  unfold aes_core.sub_bytes.sub_bytes_state
  hax_mvcgen <;> simp at *
  .
    rename_auto_n 45

    simp only [var_0]
    simp only [get_elem_bv, aes_core.sub_bytes.get_elem_SBOX]
    simp only [Nat.reduceAdd, Nat.sub_zero, beq_iff_eq, BitVec.ushiftRight_eq', BitVec.zero_or,
      ne_eq, reduceCtorEq, not_false_eq_true, Vector.getElem_set_ne, Nat.succ_ne_self,
      Vector.getElem_set_self, UInt16.toBitVec_not, UInt16.toBitVec_xor, UInt16.toBitVec_and,
      Nat.reduceEqDiff]
    simp only [<- var_24, <- var_2, <- var_4, <- var_6, <- var_8, <- var_10, <- var_12, <- var_14 ]
    bv_check "./sat_proofs/sub_bytes_per_bit.lean-aes_core.sub_bytes.sub_bytes_correct-650-4.lrat"
  all_goals grind

end aes_core
