import Std.Tactic.BVDecide
/-!
# Formalization of GF(2^8)

Elements of GF(2⁸) are represented as `BitVec 8`

The primitive polynomial
  p(x) = x⁸ + x⁴ + x³ + x + 1
is represented by its non-leading terms x⁴ + x³ + x + 1, occupiying positions
4, 3, 1, 0. That is:

  polyRed = 0x1B

-/

abbrev GF8 := BitVec 8

namespace GF8

-- Constants

def zero : GF8 := 0#8

def one : GF8 := BitVec.ofNat 8 1

-- Addition

def add (a b : GF8) : GF8 := a ^^^ b

-- Multiplication

def polyRed : GF8 := 0x1B#8

def xtime (a : GF8) : GF8 :=
  let shifted := a <<< 1#8
  if a.getLsbD 7 then shifted ^^^ polyRed else shifted

def mulStep (b : GF8) (state : GF8 × GF8) (bitIdx : Nat)
    : GF8 × GF8 :=
  let (acc, cur_a) := state
  (if b.getLsbD bitIdx then acc ^^^ cur_a else acc, xtime cur_a)

def mul (a b : GF8) : GF8 :=
  let bitIndices := List.range 8   -- [0, 1, …, 7]
  (bitIndices.foldl (mulStep b) (zero, a)).1

/-! ## Exponentiation (square-and-multiply) -/

/-- One step of binary exponentiation, suitable for `List.foldl`.

    State is `(accumulator, base)`.
    Each bit of the exponent (LSB first) decides whether to multiply
    the accumulator, and always squares the base. -/
private def powStep (state : GF8 × GF8) (bit : Bool) : GF8 × GF8 :=
  let (acc, base) := state
  (if bit then mul acc base else acc, mul base base)

/-- Raise `a` to the `n`-th power in GF(2⁸) by folding over the
    bits of `n` from LSB to MSB (standard binary exponentiation). -/
def pow (a : GF8) (n : Nat) : GF8 :=
  let bits := (List.range 8).map (fun i => n.testBit i)   -- LSB first
  (bits.foldl powStep (one, a)).1

/-! ## Inversion (Fermat's little theorem)

In GF(2⁸)×, a^(2⁸−1) = 1, so a⁻¹ = a^(2⁸−2) = a^254. -/

/-- Multiplicative inverse via Fermat's little theorem.
    Returns 0 for input 0. -/
def inv (a : GF8) : GF8 :=
  if a == zero then zero else pow a (2 ^ 8 - 2)

/-! ## Typeclass instances -/

instance : Add   GF8 := ⟨add⟩
instance : Mul   GF8 := ⟨mul⟩
instance : OfNat GF8 0 := ⟨zero⟩
instance : OfNat GF8 1 := ⟨one⟩

/-! ## Basic lemmas -/

/-- Addition is its own inverse (characteristic 2). -/
theorem add_self (a : GF8) : add a a = zero := by
  simp [add, zero, BitVec.xor_self]

/-- Zero is the additive identity (left). -/
theorem zero_add (a : GF8) : add zero a = a := by
  simp [add, zero, BitVec.zero_xor]

/-- Zero is the additive identity (right). -/
theorem add_zero (a : GF8) : add a zero = a := by
  simp [add, zero, BitVec.xor_zero]

/-- Addition is commutative. -/
theorem add_comm (a b : GF8) : add a b = add b a := by
  simp [add, BitVec.xor_comm]

/-- Addition is associative. -/
theorem add_assoc (a b c : GF8) : add (add a b) c = add a (add b c) := by
  simp [add, BitVec.xor_assoc]

/-- One is the left multiplicative identity. -/
theorem one_mul (a : GF8) : mul one a = a := by
  native_decide+revert

/-- One is the right multiplicative identity. -/
theorem mul_one (a : GF8) : mul a one = a := by
  native_decide+revert

/-- Multiplication by zero yields zero (left). -/
theorem zero_mul (a : GF8) : mul zero a = zero := by
  native_decide+revert

/-- Multiplication by zero yields zero (right). -/
theorem mul_zero (a : GF8) : mul a zero = zero := by
  native_decide+revert

/-- Multiplication is commutative. -/
theorem mul_comm (a b : GF8) : mul a b = mul b a := by
  native_decide+revert

/-- Multiplication is associative. -/
theorem mul_assoc (a b c : GF8) : mul (mul a b) c = mul a (mul b c) := by
  sorry--native_decide+revert

/-- Multiplication distributes over addition (left). -/
theorem mul_add (a b c : GF8) : mul a (add b c) = add (mul a b) (mul a c) := by
  sorry--native_decide+revert

/-- Multiplication distributes over addition (right). -/
theorem add_mul (a b c : GF8) : mul (add a b) c = add (mul a c) (mul b c) := by
  sorry--native_decide+revert

/-- Every nonzero element has a multiplicative inverse. -/
theorem mul_inv_cancel (a : GF8) (h : a ≠ zero) : mul a (inv a) = one := by
  native_decide+revert

/-- The inverse of the inverse is the original element. -/
theorem inv_inv (a : GF8) : inv (inv a) = a := by
  native_decide+revert

/-! ## Sanity checks -/

section Examples

-- `one` is 0x01 in LSB-first convention (x⁰ = 1 sits at bit 0)
#eval (one == 0x01#8)                                         -- true

-- 1 + 1 = 0  (characteristic 2)
#eval (add one one == zero)                                   -- true

-- 0 * anything = 0
#eval (mul zero one == zero)                                  -- true

-- 1 * a = a
#eval (mul one 0xDE#8 == 0xDE#8)                              -- true

-- a * 1 = a
#eval (mul 0xDE#8 one == 0xDE#8)                              -- true

-- polyRed is 0x1B (AES reduction polynomial, non-leading terms)
#eval (polyRed == 0x1B#8)                                     -- true

-- xtime of `one` shifts left, no reduction needed (MSB was 0)
-- one = 0x01, xtime one = 0x02
#eval (xtime one == 0x02#8)                                   -- true

-- a + b = b + a  (commutativity of addition)
#eval (add 0xAB#8 0xCD#8 == add 0xCD#8 0xAB#8)               -- true

-- a * b = b * a  (spot-check commutativity of multiplication)
#eval
  let a : GF8 := 0x53#8
  let b : GF8 := 0xCA#8
  mul a b == mul b a                                          -- true

-- AES S-box uses 0x53 * 0xCA = 0x01 (they are inverses)
#eval
  let a : GF8 := 0x53#8
  let b : GF8 := 0xCA#8
  mul a b == one                                              -- true

-- a * a⁻¹ = 1  (spot-check inversion)
#eval
  let a : GF8 := 0x57#8
  mul a (inv a) == one                                        -- true

-- 0 has no inverse; inv returns 0
#eval (inv zero == zero)                                      -- true

-- Exhaustive check: every nonzero element satisfies a * a⁻¹ = 1
#eval (List.range 255).all (fun n =>
  let a : GF8 := BitVec.ofNat 8 (n + 1)
  mul a (inv a) == one)                                       -- true

end Examples


/-! ## bv_decide-friendly multiplication by constants -/

/-- xtime expressed as a pure bitvector formula (no foldl, bv_decide-friendly).
    Multiply a GF8 element by 0x02 = x: shift left by 1, then conditionally
    reduce by 0x1B if the MSB (bit 7) was set. -/
def xtime_bv (a : GF8) : GF8 :=
  (a <<< 1#8) ^^^ (if a.getMsbD 0 then 0x1B#8 else 0x00#8)

/-- Multiply by 0x03 = x+1: xtime(a) XOR a -/
def mul3_bv (a : GF8) : GF8 :=
  xtime_bv a ^^^ a

/-- The MSB check in xtime uses getLsbD 7, which equals getMsbD 0 for 8-bit vectors. -/
theorem getLsbD7_eq_getMsbD0 (a : GF8) : a.getLsbD 7 = a.getMsbD 0 := by
  simp [BitVec.getLsbD, BitVec.getMsbD]

/-- xtime_bv equals GF8.xtime (the foldl-based one). -/
theorem xtime_bv_eq_xtime (a : GF8) : xtime_bv a = GF8.xtime a := by
  simp [xtime_bv, GF8.xtime, GF8.polyRed]
  grind

/-- Multiplication by 0x02 equals xtime_bv. -/
theorem mul_02_eq_xtime_bv (a : GF8) : GF8.mul 0x02#8 a = xtime_bv a := by
  have : GF8.mul 0x02#8 a = GF8.xtime a := by native_decide +revert
  rw [this, ← xtime_bv_eq_xtime]

/-- Multiplication by 0x03 equals mul3_bv. -/
theorem mul_03_eq_mul3_bv (a : GF8) : GF8.mul 0x03#8 a = mul3_bv a := by
  have h : GF8.mul 0x03#8 a = GF8.xtime a ^^^ a := by native_decide +revert
  rw [h, ← xtime_bv_eq_xtime]
  simp [mul3_bv]

/-- Expand xtime_bv into a form that bv_decide can close.
    After rewriting with this, the goal is a pure BitVec expression. -/
theorem xtime_bv_bv (a : GF8) :
    xtime_bv a =
      (a <<< 1#8) ^^^ (BitVec.ofBool (a.getMsbD 0)).zeroExtend 8 * 0x1B#8 := by
  simp [xtime_bv, BitVec.ofBool]
  split <;> simp [*]

end GF8
