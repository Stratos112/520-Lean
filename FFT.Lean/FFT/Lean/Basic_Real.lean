import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Batteries.Data.Float

-- The inner most loop
-- k is a given frequency from the references
-- n is an iterator of a sample
-- size is the length of the samples array
-- x is *the* given sample
-- what are the types of I though??
def per_sample (k : Float) (n : ℕ) (size: ℕ) (x : Float) : (ℝ × ℝ) :=

  let k_real : ℝ := ↑(Float.toRat0 k) -- Not sure why the suggestion was to convert to rational? Because the coerce to real?
  let n_real : ℝ := ↑(n) -- simple coercion on n is ok?
  let s_real : ℝ := ↑(size)
  let theta := (2 * Real.pi  * k_real * n_real) / s_real -- should now be a Real

  -- Both I and R can both be Real for now!
  let x_real : ℝ := ↑(Float.toRat0 x)
  let R : ℝ := x_real * Real.cos theta
  let I : ℝ := x_real * Real.sin theta
(R, I)

-- alpha is the type of the sample vexctor
-- k is the given reference frequency
-- size is the size of the sample vector
-- v is the vector of samples
def per_reference (k : Float) (size : ℕ) (samples : Vector Float (size)) : Complex :=

  -- changed from imperative for loop to an anonymous function as a peace offering to lean.
  let indices : List ℕ := List.range size

  -- heres this new map which holds a tuple of Reals and their index i
  -- for each sample in samples do per_sample
  let both_parts : List (ℝ × ℝ) := indices.map (fun i =>
    let x := samples[i]!
    per_sample k i size x
  )

    let R : ℝ :=  (both_parts.map (fun row => row.1 )).sum -- sum all the R
    let I : Complex := (both_parts.map (fun row => row.2)).sum * Complex.I -- sum all the I
↑(R) - (I)  -- return the complex number representing phase and amplitude of this frequency.


-- alpha is the type of the values in the sample vector
-- size is the length of the sample vector
-- v is the vector of samples
def DFT (size: ℕ) (samples : Vector Float (size)) : Vector Complex (size) :=
  -- we will make the references vector based on the length of the input s
  let references : Vector Float size := (Vector.range size).map Nat.toFloat
  -- for each reference, use per per_reference to sum along all the samples and get the complex number representing phase and amplitude
  -- return the vector of complex numbers for each reference frequency.
references.map (fun k => per_reference k size samples )
