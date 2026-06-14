
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax

import transpose_u8x16
import cipher_theorems
import sub_bytes
import shift_rows
import xor_key1

import aes_keygen_assist
import key_expansion_step

open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace libcrux_aesgcm.platform.portable.aes_core

abbrev State : Type := (RustArray u16 8)

@[spec]
def new_state (_ : rust_primitives.hax.Tuple0) : RustM (RustArray u16 8) := do
  (rust_primitives.hax.repeat (0 : u16) (8 : usize))

@[spec]
def aes_enc (st : (RustArray u16 8)) (key : (RustArray u16 8)) :
    RustM (RustArray u16 8) := do
  let st : (RustArray u16 8) ← (aes_core.sub_bytes.sub_bytes_state st);
  let st : (RustArray u16 8) ← (aes_core.shift_rows.shift_rows_state st);
  let st : (RustArray u16 8) ← (aes_core.mix_columns.mix_columns_state st);
  let st : (RustArray u16 8) ← (aes_core.xor_key1.xor_key1_state st key);
  (pure st)

@[spec]
def aes_enc_last (st : (RustArray u16 8)) (key : (RustArray u16 8)) :
    RustM (RustArray u16 8) := do
  let st : (RustArray u16 8) ← (aes_core.sub_bytes.sub_bytes_state st);
  let st : (RustArray u16 8) ← (aes_core.shift_rows.shift_rows_state st);
  let st : (RustArray u16 8) ← (aes_core.xor_key1.xor_key1_state st key);
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
    let self : (RustArray u16 8) ← (aes_core.xor_key1.xor_key1_state self key);
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
def key_expansion
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

def key_expansion_spec (i : Nat) (hi : i < 11) (key : RustSlice u8) (h : key.val.size = 16) :=
  let rcon_vec : Vector u8 11 := #v[0, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]
  if i = 0 then
    let fst := (aes_core.transpose_u8x16.transposeU8toU16 (RustArray.ofVec (@Vector.mk u8 16 key.val h)))
    #v[get_word fst 3, get_word fst 2, get_word fst 1, get_word fst 0]
  else
    let prev := key_expansion_spec (i - 1) (by grind) key h

    let new_chunk := (aes_core.aes_keygen.rotword (aes_core.aes_keygen.subword (prev[0])))
    let word_first := #v[new_chunk[0], new_chunk[1], new_chunk[2], rcon_vec[i].toBitVec ^^^ new_chunk[3]]

    let xor_2_3 := xor_word prev[2] prev[3]
    let xor_1_2_3 := xor_word prev[1] xor_2_3
    let xor_0_1_2_3 := xor_word prev[0] xor_1_2_3

    let row_3 := xor_word word_first prev[3]
    let row_2 := xor_word word_first xor_2_3
    let row_1 := xor_word word_first xor_1_2_3
    let row_0 := xor_word word_first xor_0_1_2_3

    #v[row_0, row_1, row_2, row_3]

set_option maxHeartbeats 10000000000000
set_option maxRecDepth 100000
theorem key_expansion_128_correct (key : RustSlice u8) (h : key.val.size = 16) :
⦃ ⌜ USize64.ofNat key.val.size = libcrux_aesgcm.aes_gcm_128.GCM_KEY_LEN /\ key.val.size = 16 ⌝ ⦄
  key_expansion libcrux_aesgcm.platform.portable.aes_core.State key
⦃ ⇓ ⟨res⟩ =>
    ⌜
    ∀ (i : Nat) (hi : i < 11),
    (key_expansion_spec i hi key (by grind))
    =
    let r := (res[i]'(by grind)).toVec
    #v[get_word r 3, get_word r 2, get_word r 1, get_word r 0 ]
    ⌝ ⦄ :=
  by
    unfold key_expansion
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
        aes_core.key_expansion_step.key_expansion_correct
      ] <;> simp at *
      .
        unfold key_expansion_spec
        unfold core_models.clone.Impl
        simp
        intros
        hax_mvcgen [
          aes_core.aes_keygen.aes_keygen_assist0_correct,
          aes_core.key_expansion_step.key_expansion_correct
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
