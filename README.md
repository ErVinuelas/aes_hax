# Verifying Libcrux AES using Hax + Lean
 
## Overview
 
This project formally verifies functional correctness of the portable AES-128 and AES-256 block cipher implementations from [libcrux](https://github.com/cryspen/libcrux), a high-assurance Rust cryptographic library. It uses the combination of **Hax** and **Lean** to bridge the gap between a Rust implementation and its mathematical specification.
 
## Tools
 
- **[Hax](https://github.com/hacspec/hax)** — extracts a Lean model from Rust source code, encoding Rust's panic/divergence behaviour via a `RustM` monad.
- **[Lean 4](https://leanprover.github.io/)** — interactive theorem prover used to write the AES specification and prove correctness theorems, making use of `mvcgen` (monadic verification condition generator) and `bv_decide` (SAT-backed bitvector tactic).
## What is verified
 
All core functions of the AES block cipher are verified against a readable mathematical specification:
 
- `transpose_u16x8` / `transpose_u8x16` — bitsliced state representation transforms
- `sub_bytes_state` — SubBytes step via SBox lookup
- `shift_rows_state` — ShiftRows cyclic rotation
- `mix_columns_state` — MixColumns matrix multiplication in GF(2⁸)
- `xor_key1_state` — AddRoundKey XOR
- `key_expansion_step` — full AES-128 and AES-256 key schedule
