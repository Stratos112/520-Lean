/-
REFACTOR: the DFT and FFT over an arbitrary number type, indexed by `k`
=======================================================================

This file is your DFT and FFT with two refactors done for you, plus a second
version of the DFT, `DFT'`, written as a `Finset` sum.

The rest is your structure: the `!` lookups, `mapFinIdx`, `append`, and
`List.range` / `map` / `sum`. Comments marked `REFACTOR:` explain what
changed. Comments marked `EXERCISE:` point at the refactor left for you.

What changed
------------

1. The number type is a parameter.

   Both functions take a type `R` and a root of unity `ω : R` instead of
   computing `cos` and `sin` of an angle. For complex numbers and size `N`,
   `ω = e^{-2πi/N}`. Every `e^{-2πikn/N}` in the DFT is then `ω ^ (k * n)`.
   In the FFT, the twiddle factor at position `i` is `ω ^ i`, and the
   recursive calls use `ω * ω`, a primitive root for half the size.

   `R` only needs `+`, `-`, `*`, `0` and `1`. Complex multiplication is
   written once, in the `Mul CFloat` instance below. The FFT just writes `*`.
   So the twiddle bug (multiplying real by real and imaginary by imaginary)
   can no longer happen.

   This gives us modularity and more options for testing. We can test over
   pairs of floats representing complex numbers with some loss in precision
   and we can test over a finite field like the integers modulo 17.

2. The FFT is indexed by the exponent `k`.

   It has type `FFT ω k : Vector R (2 ^ k) → Vector R (2 ^ k)` and is defined
   by pattern matching on `0` and `k + 1`. The recursive calls are on `k`,
   which is structurally smaller, so Lean needs no termination proof. That
   removes:
   - `pow2Nat`, `div2`, `mul2`, the `Coe` / `OfNat` / `HAdd` instances, and
     the three lemmas `always_ge1`, `half_and_half` and `div2_lt`. Those were
     real proofs and they did their job; they just aren't needed now.
   - the argument `h : size.val ≥ 1`;
   - `termination_by` / `decreasing_by`;
   - the `h_base ▸ single` weirdness. At `k = 0` the input already has type
     `Vector R (2 ^ 0)`, which is `Vector R 1`, and the DFT of a single
     sample is that sample. So the base case returns its input unchanged,
     and the bug there (dropping the imaginary part) is gone too.

   One `cast` is left, from length `2 ^ k + 2 ^ k` to `2 ^ (k + 1)`, after
   `append`. That is `Vector.cast`, not `▸`. `Vector.cast` only changes the
   length in the type and keeps the same underlying array, and `simp` knows
   how to look through it (`Vector.getElem_cast`, `Vector.getElem_append`).

3. There is a second DFT, `DFT'`, for the proof.

   `DFT'` computes the same transform as a `Finset` sum,
   `∑ j : Fin size, samples[j] * ω ^ (j * k)`, instead of `List.range` /
   `map` / `sum`. The indices are `Fin size`, so there is no `!`, and Mathlib
   has many lemmas about `Finset` sums that the proof needs. The theorem is
   stated with `DFT'`.

   `∑` and `^` need a commutative ring, so `DFT'` runs on `ZMod 17` but not
   on `CFloat`. Your `DFT` stays for the Float tests, and the `ZMod 17` tests
   check that the two agree.

What this buys you
------------------

1. You can run the same code on several number types:
   - `CFloat`, a pair of Floats with complex arithmetic, for numerical tests;
   - `ZMod 17` with `ω = 2` (2 has order 8 mod 17), for exact tests. There
     is no rounding, so `#guard FFT … = DFT …` checks exact equality.

2. You can state the theorem. Look at `FFT_eq_DFT` at the bottom. It says
   that over any integral domain, with `ω` a primitive `2 ^ k`-th root of
   unity, `FFT` equals `DFT'`. Specialising `R := ℂ` gives the usual FFT.
   Before this refactor there was nothing to state, because Lean has no lemmas
   about Float arithmetic.

3. The proof is induction on `k`, the same induction the code does. This
   *REALLY* exposes the advantage of not having pow2Nat...

Exercise
--------

Remove the `!` lookups from the FFT. Every index is in bounds. Use `Fin`
indices, or the bound proof that `mapFinIdx` hands you. For example, in
`get_evens`, `2 * i.val < 2 ^ (k + 1)` follows from `i.isLt`, `pow_succ` and
`omega`. When the FFT has no `!` left, the `[Inhabited R]` assumptions in the
FFT section and on `FFT_eq_DFT` can be deleted. They exist only because `!`
needs a default value to return when an index is out of range.

You should then be in a position to prove FFT_eq_DFT by induction on k, leaning
on Mathlib where it helps.

-/
import Mathlib
namespace Fourier

variable {R : Type*}

/-! ## Powers using only `*` and `1`

`ω ^ n` from Mathlib needs `R` to be a monoid. `CFloat` isn't one, because
Float multiplication isn't associative. So we define powers using only `*` and
`1`, and prove they agree with `^` whenever `R` is a monoid.
-/

def power [One R] [Mul R] (ω : R) : ℕ → R
  | 0 => 1
  | n + 1 => power ω n * ω

-- Induction on `n`, following the two cases of `power`. In each case `simp`
-- unfolds `power` and uses `pow_zero : ω ^ 0 = 1` or
-- `pow_succ : ω ^ (n + 1) = ω ^ n * ω`. In the step, `ih` rewrites
-- `power ω n` to `ω ^ n`.
-- In the main proof, `simp only [power_eq_pow]` replaces every `power` with
-- `^`, so the twiddles become `ω ^ i` and Mathlib's lemmas about powers apply.
theorem power_eq_pow [Monoid R] (ω : R) (n : ℕ) : power ω n = ω ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, ih, pow_succ]

/-! ## The DFT -/

section DFT

variable [Zero R] [One R] [Add R] [Mul R] [Inhabited R]

-- The inner most loop
-- k is a given frequency from the references
-- n is an iterator of a sample
-- x is *the* given sample
-- REFACTOR: `e^{-2πikn/N}` is now `ω ^ (k * n)`, so the angle, `cos`, `sin`
-- and the `size` argument are gone. The result is one value of type `R`
-- instead of a (real, imaginary) pair.
def per_sample (ω : R) (k : ℕ) (n : ℕ) (x : R) : R :=
  x * power ω (k * n)

-- k is the given reference frequency
-- size is the size of the sample vector
-- samples is the vector of samples
-- `DFT'` below is the same sum without `samples[i]!` or the `List`.
def per_reference (ω : R) (k : ℕ) (size : ℕ) (samples : Vector R size) : R :=
  let indices : List ℕ := List.range size
  -- for each sample in samples do per_sample
  let terms : List R := indices.map (fun i =>
    let x := samples[i]!
    per_sample ω k i x
  )
  -- REFACTOR: the real and imaginary sums are now one sum in `R`.
  terms.sum

-- size is the length of the sample vector
-- samples is the vector of samples
-- REFACTOR: the references are natural numbers now (they are exponents).
def DFT (ω : R) (size : ℕ) (samples : Vector R size) : Vector R size :=
  -- we will make the references vector based on the length of the input
  let references : Vector ℕ size := Vector.range size
  -- for each reference, use per_reference to sum along all the samples
references.map (fun k => per_reference ω k size samples)

end DFT

/-! ## The DFT as a `Finset` sum -/

-- REFACTOR: the same transform, `X_k = ∑ j, x_j * ω ^ (j * k)`, written the
-- way the proof wants it. `j` and `k` are `Fin size`, so `samples[j]` needs no
-- `!`, and Mathlib's `Finset` sum lemmas apply. `∑` and `^` need a commutative
-- ring, so this runs on `ZMod 17` but not on `CFloat`.
def DFT' [CommRing R] (ω : R) (size : ℕ) (samples : Vector R size) : Vector R size :=
  Vector.ofFn fun k : Fin size => ∑ j : Fin size, samples[j] * ω ^ (j.val * k.val)

/-! ## The FFT -/

section FFT

variable [One R] [Add R] [Sub R] [Mul R] [Inhabited R]

-- A helper for getting every other element of the vector.
-- REFACTOR: the input has length `2 ^ (k + 1)` and the output `2 ^ k`.
-- EXERCISE: `2 * i.val < 2 ^ (k + 1)` always holds, so `!` isn't needed.
def get_evens {k : ℕ} (input : Vector R (2 ^ (k + 1))) : Vector R (2 ^ k) :=
  Vector.ofFn fun i => input[2 * i.val]!
-- And for odds.
def get_odds {k : ℕ} (input : Vector R (2 ^ (k + 1))) : Vector R (2 ^ k) :=
  Vector.ofFn fun i => input[2 * i.val + 1]!

-- PSEUDO
-- if input is len(1) return it
  -- otherwise get all the even inputs x_0 -> x_N-2
  -- get all the odd inputs x_1 -> x_N-1
  -- FFT(even)
  -- FFT(odd)
  -- for all m in N:
  -- -- twiddle is ω ^ m
  -- -- Waves[m] = even[m] + twiddle odd[m]
  -- -- Waves[m + N/2] = even[m] - twiddle odd[m]
  -- return waves

-- REFACTOR: the input has length `2 ^ k`, and `ω` is a primitive `2 ^ k`-th
-- root of unity. `ω` comes after the colon because the recursive calls change
-- it to `ω * ω`.
def FFT : R → (k : ℕ) → Vector R (2 ^ k) → Vector R (2 ^ k)
  -- REFACTOR: a DFT of length 1 is the identity.
  | _, 0, samples => samples
  | ω, k + 1, samples =>
    -- recursion
    -- REFACTOR: `ω * ω` is a primitive root for half the size.
    let evens : Vector R (2 ^ k) := FFT (ω * ω) k (get_evens samples)
    let odds : Vector R (2 ^ k) := FFT (ω * ω) k (get_odds samples)
    -- twiddle
    -- REFACTOR: the i-th twiddle is `ω ^ i`. The complex multiplication comes
    -- from `R`, so it can't be done wrong here.
    let twiddle_odd : Vector R (2 ^ k) :=
      odds.mapFinIdx (fun i o _ => power ω i * o)
    --
    -- recombine
    -- EXERCISE: use the element and the bound proof `mapFinIdx` gives
    -- you instead of `twiddle_odd[i]!` and `evens[i]!`.
    let waves_top := twiddle_odd.mapFinIdx (fun i _ _ =>
      evens[i]! + twiddle_odd[i]!)
    let waves_bottom := twiddle_odd.mapFinIdx (fun i _ _ =>
      evens[i]! - twiddle_odd[i]!)
    --
    -- REFACTOR: `2 ^ k + 2 ^ k = 2 ^ (k + 1)` takes one line now, in place of
    -- `pow2Nat.half_and_half`. We write `++` rather than `Vector.append`
    -- because the simp lemma `Vector.getElem_append` is stated for `++`.
    let two_halves : Vector R (2 ^ k + 2 ^ k) :=
      waves_top ++ waves_bottom
    two_halves.cast (by rw [Nat.pow_succ]; omega)

end FFT

/-! ## Running it: Float complex numbers -/

-- Complex numbers as a pair of Floats, for running numerical tests. The
-- complex multiplication is written once, here.
structure CFloat where
  re : Float
  im : Float
deriving Inhabited

namespace CFloat

instance : Zero CFloat := ⟨⟨0, 0⟩⟩
instance : One CFloat := ⟨⟨1, 0⟩⟩
instance : Add CFloat := ⟨fun a b => ⟨a.re + b.re, a.im + b.im⟩⟩
instance : Sub CFloat := ⟨fun a b => ⟨a.re - b.re, a.im - b.im⟩⟩
instance : Mul CFloat :=
  ⟨fun a b => ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩

def ofReal (x : Float) : CFloat := ⟨x, 0⟩
def toPair (z : CFloat) : Float × Float := (z.re, z.im)

/-- `e^{-2πi/n}`, the root to pass to `DFT` and `FFT` for size `n`. -/
def root (n : ℕ) : CFloat :=
  let θ := -(2 * 3.141592653589793) / n.toFloat
  ⟨Float.cos θ, Float.sin θ⟩

end CFloat

open CFloat

def reals {n : ℕ} (xs : Vector Float n) : Vector CFloat n := xs.map ofReal

/-- Componentwise comparison with an absolute tolerance. -/
def close (ε : Float) (xs ys : List (Float × Float)) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (a, b) =>
    (a.1 - b.1).abs ≤ ε && (a.2 - b.2).abs ≤ ε

def ε : Float := 1e-9

-- Your DFT tests, as checks that fail when the answer is wrong.
#eval (DFT (root 4) 4 (reals #v[1, 2, 3, 4])).toList.map toPair
#guard close ε ((DFT (root 4) 4 (reals #v[1, 1, 1, 1])).toList.map toPair)
  [(4, 0), (0, 0), (0, 0), (0, 0)]
#guard close ε ((DFT (root 4) 4 (reals #v[1, 2, 3, 4])).toList.map toPair)
  [(10, 0), (-2, 2), (-2, 0), (-2, -2)]
-- Your comment said (4,0) at index 4. The correct value is (-4,0).
#guard close ε ((DFT (root 8) 8 (reals #v[1, 2, 1, 2, 1, 2, 1, 2])).toList.map toPair)
  [(12, 0), (0, 0), (0, 0), (0, 0), (-4, 0), (0, 0), (0, 0), (0, 0)]
#guard close ε ((DFT (root 8) 8 (reals #v[2, 1, 0, 1, 2, 1, 0, 1])).toList.map toPair)
  [(8, 0), (0, 0), (4, 0), (0, 0), (0, 0), (0, 0), (4, 0), (0, 0)]
#guard close ε ((DFT (root 8) 8 (reals #v[0, 1, 2, 1, 0, 1, 2, 1])).toList.map toPair)
  [(8, 0), (0, 0), (-4, 0), (0, 0), (0, 0), (0, 0), (-4, 0), (0, 0)]
#guard close ε
  ((DFT (root 12) 12 (reals #v[2, -1, -1, 2, -1, -1, 2, -1, -1, 2, -1, -1])).toList.map toPair)
  [(0, 0), (0, 0), (0, 0), (0, 0), (12, 0), (0, 0), (0, 0), (0, 0), (12, 0), (0, 0), (0, 0), (0, 0)]

/-- Run both transforms at size `2 ^ k` and compare. -/
def fftMatchesDft (k : ℕ) (xs : Vector CFloat (2 ^ k)) : Bool :=
  close ε ((FFT (root (2 ^ k)) k xs).toList.map toPair)
    ((DFT (root (2 ^ k)) (2 ^ k) xs).toList.map toPair)

#eval (FFT (root 4) 2 (reals #v[1, 2, 3, 4])).toList.map toPair
#guard fftMatchesDft 2 (reals #v[1, 2, 3, 4])
#guard fftMatchesDft 3 (reals #v[1, 2, 1, 2, 1, 2, 1, 2])
#guard fftMatchesDft 3 (reals #v[2, 1, 0, 1, 2, 1, 0, 1])
-- An impulse: its spectrum has nonzero imaginary parts everywhere.
#guard fftMatchesDft 3 (reals #v[0, 1, 0, 0, 0, 0, 0, 0])
-- Complex input.
#guard fftMatchesDft 0 #v[⟨0, 1⟩]
#guard fftMatchesDft 2 #v[⟨1, 2⟩, ⟨-3, 0.5⟩, ⟨0, -1⟩, ⟨4, 4⟩]

/-! ## Running it: exact tests in `ZMod 17`

In `ZMod 17`, 2 has order 8. So 2 is a primitive 8th root of unity, 4 is a
primitive 4th root, 16 = -1 is a primitive square root, and 1 is the
primitive first root. No rounding, so we can check exact equality.
-/

#guard (2 : ZMod 17) ^ 4 = -1
#eval (FFT (2 : ZMod 17) 3 #v[1, 2, 3, 4, 5, 6, 7, 8]).toList.map ZMod.val
#guard FFT (2 : ZMod 17) 3 #v[1, 2, 3, 4, 5, 6, 7, 8] = DFT 2 8 #v[1, 2, 3, 4, 5, 6, 7, 8]
#guard FFT (2 : ZMod 17) 3 #v[0, 1, 0, 0, 0, 0, 0, 0] = #v[1, 2, 4, 8, 16, 15, 13, 9]
#guard FFT (4 : ZMod 17) 2 #v[3, 1, 4, 1] = DFT 4 4 #v[3, 1, 4, 1]
#guard FFT (16 : ZMod 17) 1 #v[5, 9] = #v[14, 13]
#guard FFT (1 : ZMod 17) 0 #v[5] = #v[5]

-- `DFT'` agrees with your `DFT` and with the FFT.
#guard DFT' (2 : ZMod 17) 8 #v[1, 2, 3, 4, 5, 6, 7, 8] = DFT 2 8 #v[1, 2, 3, 4, 5, 6, 7, 8]
#guard DFT' (4 : ZMod 17) 4 #v[3, 1, 4, 1] = DFT 4 4 #v[3, 1, 4, 1]
#guard FFT (2 : ZMod 17) 3 #v[1, 2, 3, 4, 5, 6, 7, 8] = DFT' 2 8 #v[1, 2, 3, 4, 5, 6, 7, 8]
#guard FFT (2 : ZMod 17) 3 #v[0, 1, 0, 0, 0, 0, 0, 0] = DFT' 2 8 #v[0, 1, 0, 0, 0, 0, 0, 0]
#guard FFT (16 : ZMod 17) 1 #v[5, 9] = DFT' 16 2 #v[5, 9]

/-! ## The theorem

`IsPrimitiveRoot ω n` means `ω ^ n = 1` and no smaller positive power of `ω`
is 1. `IsDomain` is needed for the step `ω ^ (2 ^ k) = -1` when `ω` is a
primitive `2 ^ (k + 1)`-th root.

-/

-- Prove it with `induction k generalizing ω`. In each case, start with
-- `ext i hi`. The base case is short. In the step,
-- `simp only [FFT, Vector.getElem_cast, Vector.getElem_append]` turns the goal
-- into `if h : i < 2 ^ k then … else …`, the top and bottom halves. Do the
-- exercise first: every `!` left in the FFT is a side goal here.
theorem FFT_eq_DFT [CommRing R] [IsDomain R] [Inhabited R]
    (k : ℕ) (ω : R) (hω : IsPrimitiveRoot ω (2 ^ k)) (samples : Vector R (2 ^ k)) :
    FFT ω k samples = DFT' ω (2 ^ k) samples := by
  sorry

end Fourier
