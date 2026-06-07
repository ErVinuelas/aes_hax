import Std.Tactic.BVDecide
/-!
# GF(2^128) via BitVec — MSB-first / GCM convention

Elements of GF(2¹²⁸) are represented as `BitVec 128` using the
**MSB-first** (GCM / GHASH, RFC 4771) bit ordering:

  - The coefficient of **x⁰** (constant term) lives in the **MSB** (bit 127).
  - The coefficient of **x¹²⁷** lives in the **LSB** (bit 0).

Under this convention the primitive polynomial
  p(x) = x¹²⁸ + x⁷ + x² + x + 1
is represented by its non-leading terms x⁷ + x² + x + 1, which occupy
bit positions 120, 125, 126, 127 (counting from the MSB end), giving:

  polyRed = 0xE100_0000_0000_0000_0000_0000_0000_0000

Operations:
  - **Addition**       : bitwise XOR
  - **xtime (·x)**     : shift RIGHT by 1; if the old LSB was 1, XOR polyRed
  - **Multiplication** : `List.foldl` over bit indices 127..0 of `b`
                         (MSB → LSB, i.e. x⁰ → x¹²⁷)
-/

/-- Elements of GF(2¹²⁸), MSB-first / GCM convention. -/
abbrev GF128 := BitVec 128

namespace GF128

/-! ## Constants -/

/-- The zero element (additive identity). -/
def zero : GF128 := 0#128

/-- The one element (multiplicative identity).
    In MSB-first convention, x⁰ = 1 sits at the MSB. -/
def one : GF128 := BitVec.ofNat 128 (1 <<< 127)

/-! ## Addition -/

/-- Add two GF(2¹²⁸) elements (= bitwise XOR). -/
def add (a b : GF128) : GF128 := a ^^^ b

/-! ## Multiplication -/

/-- Non-leading terms of p(x) = x¹²⁸+x⁷+x²+x+1 in MSB-first layout. -/
def polyRed : GF128 :=
  0xE1000000000000000000000000000000#128

/-- Multiply `a` by x in MSB-first convention.
    Shift right by 1; if the outgoing LSB (= x¹²⁷ coefficient) was 1,
    reduce by XORing with polyRed. -/
def xtime (a : GF128) : GF128 :=
  let shifted := a >>> 1
  if a.getLsbD 0 then shifted ^^^ polyRed else shifted

/-- One step of the shift-and-XOR accumulation, suitable for `List.foldl`.

    State is `(accumulator, current scaled copy of a)`.
    `bitIdx` is a bit index into `b` counted from the LSB; since we fold
    over `[127, 126, …, 0]` this reads b's coefficients MSB → LSB,
    i.e. x⁰ first. -/
def mulStep (b : GF128) (state : GF128 × GF128) (bitIdx : Nat)
    : GF128 × GF128 :=
  let (acc, cur_a) := state
  (if b.getLsbD bitIdx then acc ^^^ cur_a else acc, xtime cur_a)

/-- Multiply two GF(2¹²⁸) elements.

    We fold `mulStep` over the list `[127, 126, …, 0]`, which reads b's
    bit-coefficients in MSB-first order (x⁰ through x¹²⁷). -/
def mul (a b : GF128) : GF128 :=
  let bitIndices := (List.range 128).reverse   -- [127, 126, …, 0]
  (bitIndices.foldl (mulStep b) (zero, a)).1

/-! ## Exponentiation (square-and-multiply) -/

/-- One step of binary exponentiation, suitable for `List.foldl`.

    State is `(accumulator, base)`.
    Each bit of the exponent (LSB first) decides whether to multiply
    the accumulator, and always squares the base. -/
private def powStep (state : GF128 × GF128) (bit : Bool) : GF128 × GF128 :=
  let (acc, base) := state
  (if bit then mul acc base else acc, mul base base)

/-- Raise `a` to the `n`-th power in GF(2¹²⁸) by folding over the
    bits of `n` from LSB to MSB (standard binary exponentiation). -/
def pow (a : GF128) (n : Nat) : GF128 :=
  let bits := (List.range 128).map (fun i => n.testBit i)   -- LSB first
  (bits.foldl powStep (one, a)).1

/-! ## Inversion (Fermat's little theorem)

In GF(2¹²⁸)×, a^(2¹²⁸−1) = 1, so a⁻¹ = a^(2¹²⁸−2). -/

/-- Multiplicative inverse via Fermat's little theorem.
    Returns 0 for input 0. -/
def inv (a : GF128) : GF128 :=
  if a == zero then zero else pow a (2 ^ 128 - 2)

/-! ## Typeclass instances -/

instance : Add   GF128 := ⟨add⟩
instance : Mul   GF128 := ⟨mul⟩
instance : OfNat GF128 0 := ⟨zero⟩
instance : OfNat GF128 1 := ⟨one⟩

/-! ## Basic lemmas -/

/-- Addition is its own inverse (characteristic 2). -/
theorem add_self (a : GF128) : add a a = zero := by
  simp [add, zero, BitVec.xor_self]

/-- Zero is the additive identity (left). -/
theorem zero_add (a : GF128) : add zero a = a := by
  simp [add, zero, BitVec.zero_xor]

/-- Zero is the additive identity (right). -/
theorem add_zero (a : GF128) : add a zero = a := by
  simp [add, zero, BitVec.xor_zero]

/-- Addition is commutative. -/
theorem add_comm (a b : GF128) : add a b = add b a := by
  simp [add, BitVec.xor_comm]

/-- One is the left multiplicative identity. -/
theorem one_mul (a : GF128) : mul one a = a := by
  sorry--native_decide+revert


/-- Multiplication by zero yields zero. -/
theorem mul_zero (a : GF128) : mul a zero = zero := by
  sorry--native_decide

/-! ## Sanity checks -/

section Examples

-- `one` is 0x80...0 in MSB-first convention
#eval (one == 0x80000000000000000000000000000000#128)           -- true

-- 1 + 1 = 0  (characteristic 2)
#eval (add one one == zero)                                     -- true

-- 0 * anything = 0
#eval (mul zero one == zero)                                    -- true

-- 1 * a = a
#eval (mul one 0xDEADBEEF#128 == 0xDEADBEEF#128)               -- true

-- polyRed is as specified
#eval (polyRed == 0xE1000000000000000000000000000000#128)       -- true

-- a * b = b * a  (spot-check commutativity)
#eval
  let a : GF128 := 0xABCDEF01234567890ABCDEF012345678#128
  let b : GF128 := 0x112233445566778899AABBCCDDEEFF00#128
  mul a b == mul b a                                            -- true

-- a * a⁻¹ = 1  (spot-check inversion)
#eval
  let a : GF128 := 0xDEADBEEFCAFEBABE0123456789ABCDEF#128
  mul a (inv a) == one                                         -- true

end Examples

end GF128
