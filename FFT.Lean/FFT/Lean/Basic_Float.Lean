import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
namespace Fourier
open Float

-- The inner most loop
-- k is a given frequency from the references
-- n is an iterator of a sample
-- size is the length of the samples array
-- x is *the* given sample
-- what are the types of I though??
def per_sample_f (k : Float) (n : ℕ) (size : ℕ) (x : Float) : (Float × Float) :=
  let theta := -(2 * 3.141592653589793  * k * (n.toFloat)) / ↑(size.toFloat) --should now be a Float

  -- Both I and R can both be Real for now!
  let R : Float := x * cos theta
  let I : Float := x * sin theta
(R, I)

-- alpha is the type of the sample vexctor
-- k is the given reference frequency
-- size is the size of the sample vector
-- v is the vector of samples
def per_reference_f (k : Float) (size : ℕ) (samples : Vector Float (size)) : (Float × Float) :=
  -- changed from imperative for loop to an anonymous function as a peace offering to lean.
  let indices : List ℕ := List.range size
  -- heres this new map which holds a tuple of Reals and their index i
  -- for each sample in samples do per_sample
  let both_parts : List (Float × Float) := indices.map (fun i =>
    let x := samples[i]!
    per_sample_f k i size x
  )
    let R : Float :=  (both_parts.map (fun row => row.1 )).sum -- sum all the R
    let I : Float := (both_parts.map (fun row => row.2)).sum -- sum all the I
(R, I)

-- alpha is the type of the values in the sample vector
-- size is the length of the sample vector
-- v is the vector of samples
def DFT_float (size : ℕ) (samples : Vector Float (size)) : Vector (Float × Float) (size) :=
  -- we will make the references vector based on the length of the input s
  let references : Vector Float size := (Vector.range size).map Nat.toFloat
  -- for each reference, use per per_reference to sum along all the samples
  -- get the tuple of floats representing phase and amplitude
  -- return the vector of tuples for each reference frequency.
references.map (fun k => per_reference_f k size samples )


#eval DFT_float 4 (#v[1, 1, 1, 1]) -- expect 4, 0, 0 ,0
#eval DFT_float 4 (#v[1, 2, 3, 4]) -- expect 10, (-2 0) (-2 0) (-2 0) -- Wrong??
#eval DFT_float 8 (#v[1, 2, 1, 2, 1, 2, 1, 2]) --expect (12,0) (0,0), (0,0) (0,0) (-4,0), (0,0) (0,0) (0,0)
#eval DFT_float 8 (#v[2, 1, 0, 1, 2, 1, 0, 1]) -- expect (8,0), 0, (4,0), 0 ,0 ,0 ,(4,0), 0

#eval DFT_float 8 (#v[0, 1, 2, 1, 0, 1, 2, 1])
-- expect [(8.0, 0.0), (0.0, 0.0), (-4.0, 0.0), (-0.0, -0.0), (0.0, -0.0), (0.0, 0.0),
--         (-4.0, 0.0), (-0.0, 0.0)]

#eval DFT_float 12 (#v[2.0, -1.0, -1.0, 2.0, -1.0, -1.0, 2.0, -1.0, -1.0, 2.0, -1.0, -1.0])
-- expect [(0.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.0, 0.0), (12.0, 0.0), (0.0, 0.0), (0.0, 0.0),
--         (0.0, 0.0), (12.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.0, 0.0)]

end Fourier
