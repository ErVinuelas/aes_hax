

-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax

import transpose_u8x16
import sub_bytes
import shift_rows
import mix_columns
import xor_key1
import cipher_theorems


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


namespace libcrux_aesgcm.aes_gcm_256

--  AES-GCM 256 key length.
def KEY_LEN : usize := (32 : usize)

end libcrux_aesgcm.aes_gcm_256

namespace libcrux_aesgcm.ctr.aes256_ctr

def NUM_KEYS : usize := (15 : usize)

end libcrux_aesgcm.ctr.aes256_ctr


namespace libcrux_aesgcm.ctr.aes256_ctr

--  256 - Key expansion
set_option maxRecDepth 100000
@[spec]
def key_expansion
    (T : Type)
    [trait_constr_key_expansion_associated_type_i0 :
      libcrux_aesgcm.platform.AESState.AssociatedTypes
      T]
    [trait_constr_key_expansion_i0 : libcrux_aesgcm.platform.AESState T ]
    (key : (RustSlice u8)) :
    RustM (RustArray T 15) := do
  let _ ←
    if true then do
      let _ ←
        (hax_lib.assert
          (← ((← (core_models.slice.Impl.len u8 key))
            ==? libcrux_aesgcm.aes_gcm_256.KEY_LEN)));
      (pure rust_primitives.hax.Tuple0.mk)
    else do
      (pure rust_primitives.hax.Tuple0.mk);
  let keyex : (RustArray T 15) ←
    (core_models.array.from_fn T ((15 : usize)) (usize -> RustM T)
      (fun _ =>
        (do
        (libcrux_aesgcm.platform.AESState.new T rust_primitives.hax.Tuple0.mk) :
        RustM T)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (0 : usize)
      (← (libcrux_aesgcm.platform.AESState.load_block
        T
        (← keyex[(0 : usize)]_?)
        (← key[
          (core_models.ops.range.Range.mk
            (start := (0 : usize))
            (_end := (16 : usize)))
          ]_?))));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (1 : usize)
      (← (libcrux_aesgcm.platform.AESState.load_block
        T
        (← keyex[(1 : usize)]_?)
        (← key[
          (core_models.ops.range.Range.mk
            (start := (16 : usize))
            (_end := (32 : usize)))
          ]_?))));
  let prev0 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((2 : usize) -? (2 : usize)))]_?));
  let prev1 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((2 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (2 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((1 : i32)) (← keyex[(2 : usize)]_?) prev1)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (2 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(2 : usize)]_?) prev0)));
  let next0 : T ← (core_models.clone.Clone.clone T (← keyex[(2 : usize)]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((2 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist1
        T (← keyex[(← ((2 : usize) +? (1 : usize)))]_?) next0)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((2 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(← ((2 : usize) +? (1 : usize)))]_?) prev1)));
  let prev0 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((4 : usize) -? (2 : usize)))]_?));
  let prev1 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((4 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (4 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((2 : i32)) (← keyex[(4 : usize)]_?) prev1)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (4 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(4 : usize)]_?) prev0)));
  let next0 : T ← (core_models.clone.Clone.clone T (← keyex[(4 : usize)]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((4 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist1
        T (← keyex[(← ((4 : usize) +? (1 : usize)))]_?) next0)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((4 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(← ((4 : usize) +? (1 : usize)))]_?) prev1)));
  let prev0 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((6 : usize) -? (2 : usize)))]_?));
  let prev1 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((6 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (6 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((4 : i32)) (← keyex[(6 : usize)]_?) prev1)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (6 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(6 : usize)]_?) prev0)));
  let next0 : T ← (core_models.clone.Clone.clone T (← keyex[(6 : usize)]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((6 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist1
        T (← keyex[(← ((6 : usize) +? (1 : usize)))]_?) next0)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((6 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(← ((6 : usize) +? (1 : usize)))]_?) prev1)));
  let prev0 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((8 : usize) -? (2 : usize)))]_?));
  let prev1 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((8 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (8 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((8 : i32)) (← keyex[(8 : usize)]_?) prev1)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (8 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(8 : usize)]_?) prev0)));
  let next0 : T ← (core_models.clone.Clone.clone T (← keyex[(8 : usize)]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((8 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist1
        T (← keyex[(← ((8 : usize) +? (1 : usize)))]_?) next0)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((8 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(← ((8 : usize) +? (1 : usize)))]_?) prev1)));
  let prev0 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((10 : usize) -? (2 : usize)))]_?));
  let prev1 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((10 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (10 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((16 : i32)) (← keyex[(10 : usize)]_?) prev1)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (10 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(10 : usize)]_?) prev0)));
  let next0 : T ← (core_models.clone.Clone.clone T (← keyex[(10 : usize)]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((10 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist1
        T (← keyex[(← ((10 : usize) +? (1 : usize)))]_?) next0)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((10 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(← ((10 : usize) +? (1 : usize)))]_?) prev1)));
  let prev0 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((12 : usize) -? (2 : usize)))]_?));
  let prev1 : T ←
    (core_models.clone.Clone.clone
      T (← keyex[(← ((12 : usize) -? (1 : usize)))]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (12 : usize)
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((32 : i32)) (← keyex[(12 : usize)]_?) prev1)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (12 : usize)
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(12 : usize)]_?) prev0)));
  let next0 : T ← (core_models.clone.Clone.clone T (← keyex[(12 : usize)]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((12 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist1
        T (← keyex[(← ((12 : usize) +? (1 : usize)))]_?) next0)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← ((12 : usize) +? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(← ((12 : usize) +? (1 : usize)))]_?) prev1)));
  let prev0 : T ← (core_models.clone.Clone.clone T (← keyex[(12 : usize)]_?));
  let prev1 : T ← (core_models.clone.Clone.clone T (← keyex[(13 : usize)]_?));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← (NUM_KEYS -? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.aes_keygen_assist0
        T ((64 : i32)) (← keyex[(← (NUM_KEYS -? (1 : usize)))]_?) prev1)));
  let keyex : (RustArray T 15) ←
    (rust_primitives.hax.monomorphized_update_at.update_at_usize
      keyex
      (← (NUM_KEYS -? (1 : usize)))
      (← (libcrux_aesgcm.platform.AESState.key_expansion_step
        T (← keyex[(← (NUM_KEYS -? (1 : usize)))]_?) prev0)));
  (pure keyex)

def rcon_256 : Vector u8 8 := #v[0, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40]

-- rcon_index maps even round index i (2, 4, 6, 8, 10, 12, 14) to its RCON entry (1..7).
def rcon_index (i : Nat) : Nat := i / 2

def key_expansion_256_spec (i : Nat) (hi : i < 15)
    (key : RustSlice u8) (h : key.val.size = 32) :=
  -- The key bytes occupy two blocks: key[0..16] and key[16..32].
  let block0 : RustArray u8 16 :=
    RustArray.ofVec (@Vector.mk u8 16
      (key.val.extract 0 16) (by grind))
  let block1 : RustArray u8 16 :=
    RustArray.ofVec (@Vector.mk u8 16
      (key.val.extract 16 32) (by grind))

  let fst0 := aes_core.transpose_u8x16.transposeU8toU16 block0
  let fst1 := aes_core.transpose_u8x16.transposeU8toU16 block1

  if i = 0 then
    -- keyex[0] = load_block(key[0..16])
    #v[get_word fst0 3, get_word fst0 2, get_word fst0 1, get_word fst0 0]
  else if i = 1 then
    -- keyex[1] = load_block(key[16..32])
    #v[get_word fst1 3, get_word fst1 2, get_word fst1 1, get_word fst1 0]
  else if i % 2 = 0 then

    let prev0 := key_expansion_256_spec (i - 2) (by omega) key h
    let prev1 := key_expansion_256_spec (i - 1) (by omega) key h
    let rcon  := rcon_256[rcon_index i]'(by unfold rcon_index; grind)

    let new_chunk := aes_core.aes_keygen.rotword (aes_core.aes_keygen.subword prev1[0])
    let word_first :=
      #v[new_chunk[0], new_chunk[1], new_chunk[2], rcon.toBitVec ^^^ new_chunk[3]]

    let xor_2_3     := xor_word prev0[2] prev0[3]
    let xor_1_2_3   := xor_word prev0[1] xor_2_3
    let xor_0_1_2_3 := xor_word prev0[0] xor_1_2_3

    let row_3 := xor_word word_first prev0[3]
    let row_2 := xor_word word_first xor_2_3
    let row_1 := xor_word word_first xor_1_2_3
    let row_0 := xor_word word_first xor_0_1_2_3

    #v[row_0, row_1, row_2, row_3]
  else

    let next0 := key_expansion_256_spec (i - 1) (by omega) key h
    let prev1 := key_expansion_256_spec (i - 2) (by omega) key h

    let sub   := aes_core.aes_keygen.subword next0[0]
    let word_first := sub

    let xor_2_3     := xor_word prev1[2] prev1[3]
    let xor_1_2_3   := xor_word prev1[1] xor_2_3
    let xor_0_1_2_3 := xor_word prev1[0] xor_1_2_3

    let row_3 := xor_word word_first prev1[3]
    let row_2 := xor_word word_first xor_2_3
    let row_1 := xor_word word_first xor_1_2_3
    let row_0 := xor_word word_first xor_0_1_2_3

    #v[row_0, row_1, row_2, row_3]


set_option maxHeartbeats 10000000000000
set_option maxRecDepth 100000
theorem key_expansion_256_correct (key : RustSlice u8) (h : key.val.size = 32) :
    ⦃ ⌜ USize64.ofNat key.val.size = libcrux_aesgcm.aes_gcm_256.KEY_LEN
        /\ key.val.size = 32 ⌝ ⦄
      key_expansion libcrux_aesgcm.platform.portable.aes_core.State key
    ⦃ ⇓ ⟨res⟩ =>
        ⌜
        ∀ (i : Nat) (hi : i < 15),
        (key_expansion_256_spec i (by grind) key h)
        =
        let r := (res[i]'(by grind)).toVec
        #v[get_word r 3, get_word r 2, get_word r 1, get_word r 0]
        ⌝ ⦄ :=
  by
    unfold key_expansion
    unfold platform.portable.aes_core.Impl
    simp
    unfold aes_gcm_256.KEY_LEN core_models.clone.Clone.clone
    unfold platform.AESState.trait_constr_AESState_i0
    simp
    unfold core_models.marker.Copy.trait_constr_Copy_i0
    unfold core_models.result.Impl.unwrap core_models.convert.TryInto.try_into
    unfold core_models.convert.instTryIntoRustSliceRustArray core_models.slice.Impl.len
    unfold rust_primitives.slice.slice_length core_models.marker.Impl_3
    unfold core_models.array.from_fn
    unfold rust_primitives.slice.array_from_fn platform.portable.aes_core.State
    simp

    hax_mvcgen[
      aes_core.transpose_u8x16_correct,
      aes_core.aes_keygen.aes_keygen_assist0_correct,
      aes_core.aes_keygen.aes_keygen_assist1_correct,
      aes_core.key_expansion_step.key_expansion_correct
    ] <;> simp at *
    .
      have hnat : 8 = @ToNat.toNat usize instToNatUsize 8 := by decide
      simp only [hnat]
      simp at *
      simp only [getElemResult]
      simp

      rename_auto_n 8
      obtain ⟨h1, h2⟩ := var_0
      simp [h2]

      unfold core_models.clone.Impl
      simp


      hax_mvcgen [
      aes_core.transpose_u8x16_correct,
      aes_core.aes_keygen.aes_keygen_assist0_correct,
      aes_core.aes_keygen.aes_keygen_assist1_correct,
      aes_core.key_expansion_step.key_expansion_correct
      ] <;> try (exact 1#8)
      .
        intros
        simp at *
        unfold key_expansion_256_spec NUM_KEYS rcon_index
        simp at *
        rename_auto_n 150

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

        match var_62 with

        | n + 15 => grind

        | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14  =>

            simp [var_67] at *

            try (simp [key_expansion_256_spec, rcon_256])
            simp [<- var_5, <- var_2]

            try (simp only [<- var_71, <- var_66, <- var_77, <- var_71, <- var_82, <- var_88, <- var_93, <- var_99, <- var_104, <- var_110, <- var_115, <- var_121, <- var_126, <- var_132 ])
            repeat (
              simp only [var_78, var_85, var_74, var_89, var_96, var_100, var_107, var_111, var_118, var_122, var_129, var_135];
              simp only [<- var_71, <- var_66, <- var_77, <- var_71, <- var_82, <- var_88, <- var_93, <- var_99, <- var_104, <- var_110, <- var_115, <- var_121, <- var_126, <- var_132 ]
            )

            try(simp only [aes_core.aes_keygen.aes_keygen_first])
            try (simp [rcon_index])



      all_goals grind

      --all_goals grind
    .
      grind

end libcrux_aesgcm.ctr.aes256_ctr
