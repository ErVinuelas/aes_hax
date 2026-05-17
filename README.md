This repo serves as a summary of what I have been able to prove so far. The main file, `LibcruxAesgcm.lean`, contains the main proofs. This proofs relate a specification in Lean to the translation done by hax of the corresponding function of libcrux.
All functions done so far belong to [`aes_core.rs`](https://github.com/cryspen/libcrux/blob/main/crates/algorithms/aesgcm/src/platform/portable/aes_core.rs).

__Addition to Hax:__

When I started working with `RustSlice` there wasn't a function to update the value of a certain slice. I needed such a function to be able to reason around `transpose_u16x8_correct`. 
Add the following to the file `Hax/proof-libs/lean/Hax/rust_primitives/slice.lean`. 

```
@[spec]
def rust_primitives.slice.update_at {α} (s : RustSlice α) (i : usize) (v : α) : RustM (RustSlice α) :=
  if h : (USize64.toNat i) < s.val.size then
    pure ⟨(s.val.set (USize64.toNat i) v h), by grind⟩
  else
    .fail (.arrayOutOfBounds)
```

__About what is already proved:__

Both the specification and the translated function done by hax are defined in a separate file called as the function. This file usually also contains auxiliary functions that I needed to relate to a specification so I could reason about the main one. Fx,
the function `transpose_u8x16` is related to the specification `transpose_u16x8` by the lemma `transpose_u16x8_correct`, where the lemma is defined in `LibcruxAesgcm.lean` and the rest is defined in the file `transpose_u16x8.lean`.

__About what is left to prove:__

What it is left to be proven from AES is the key generation. I am working on it. Besides that, it would be important to reason around the GCM side of things, but I am not entirely sure
that the specification I can make is clearer that the code itself.
