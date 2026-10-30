import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
namespace Fourrier
open Float


-- My whole size-must-be-power-of-2 abomination
----------------------------------------------------
def pow2Nat : Type :=
  {n : ℕ // n.isPowerOfTwo}

def pow2Nat.div2 (n : pow2Nat) : pow2Nat :=
  let k := n.val.log2
  ⟨2 ^ (k - 1), by
    use k - 1
   ⟩

   -- Sigh ....
  -- rcases n.property with ⟨j, hj⟩
  -- have hj_self : j = (j + 1) - 1 := by omega -- this was so dumb. But like of course.
  -- rw [hj_self] at hj
  -- rw [Nat.sub_add_comm] at hj
  -- rw [Nat.pow_add_one'] at hj
  -- use j -1


def pow2Nat.mul2 (n : pow2Nat) : pow2Nat :=
  ⟨2 * n.val, by
  rcases n.property with ⟨k,hk⟩
  use k+1
  rw[Nat.pow_add_one]
  omega
  ⟩

-- let there be an instance of coercion where if Lean expects a Nat and sees pow2Nat,
-- it will promote the n.val as a Nat
instance : Coe pow2Nat ℕ where
  coe n := n.val
-- let there be an instace of coercion where if Lean expects a pow2NAt and sees a Nat,
-- it will try to demote it.
instance (n : ℕ) [h : Fact (n.isPowerOfTwo)] : OfNat pow2Nat n where
  ofNat := ⟨n, h.out⟩
instance : HAdd pow2Nat pow2Nat ℕ where
  hAdd a b := a.val + b.val




-- showing that pow2 / 2 will be >= 1
theorem pow2Nat.always_ge1 (n : pow2Nat) : n.div2.val ≥ 1 := by
  simp only [pow2Nat.div2]
  exact Nat.one_le_two_pow -- LMAO this is literally just exactly it.

-- showing that pow 2 plus itself is the next pow 2
theorem pow2Nat.half_and_half (n : pow2Nat) (h : n.val > 1) : (n.div2 + n.div2) = n.val := by
  rcases n.property with ⟨k, hk⟩
  rw [← Nat.mul_two]
  rw [hk] at h
  rw [hk]
  simp only [pow2Nat.div2]
  rw[hk]
  simp only [Nat.log2_two_pow]
  rw[Nat.mul_comm]
  rw[← Nat.pow_add_one']
  rw[Nat.sub_add_cancel]
  grind
  --rw [hj]

-- showing half of pow 2 is less than pow 2
theorem pow2Nat.div2_lt (n : pow2Nat) (h : n.val ≥ 2) : n.div2.val < n.val  := by
  simp only [pow2Nat.div2]
  rcases n.property with ⟨k, hk⟩
  rw[hk] at h
  rw[hk]
  simp only [Nat.log2_two_pow]
  rw[Nat.pow_lt_pow_iff_right]
  · grind
  · simp


#eval Nat.isPowerOfTwo 1 -- just making sure
#check Nat.pow_sub_one



---------------------------------------------------

-- A helper for getting every other element of the vector.
def get_evens {n : pow2Nat} (input : Vector (Float × Float) (n)) : Vector (Float × Float) n.div2 :=
  Vector.ofFn fun i => input[2 * i.val]!
-- And for odds.
def get_odds {n : pow2Nat} (input : Vector (Float × Float) (n)) : Vector (Float × Float) n.div2 :=
  Vector.ofFn fun i => input[2 * i.val + 1]!

-- PSEUDO
-- if input is len(1) return it
  -- otherwise get all the even inputs x_0 -> x_N-2
  -- get all the odd inputs x_1 -> x_N-1
  -- FFT(even)
  -- FFT(odd)
  -- for all m in N:
  -- -- twiddle is the whole e^2pi thing
  -- -- Waves[m] = even[m] + twiddle odd[m]
  -- -- Waves[m + N/2] = even[m] - twiddle odd[m]
  -- return waves


--here we go
def FFT (size : pow2Nat) (samples : Vector (Float × Float) (size)) (h : size.val >= 1):
  Vector (Float × Float) (size) :=
  --
  let f0 : Float := 0.0
  if h_base : size.val = 1 then
     -- Ok I used pw2Nat as a nat, but now I'm backwards and need '1' to be a pow2Nat.
    --#v[(samples[0]!, f0)]
    let single : Vector (Float × Float) 1 := #v[(samples[0]!.1, f0)]
    h_base ▸ single -- thats cool. Thanks gemini.
    -- ^^ this could probably due with some additional syhntax explanation
  else
    -- The actual meat and potatos
    have h_gt2 : size.val ≥ 2 := by omega
    -- recursion
    let half_size : pow2Nat := (size.div2)
    let evens : Vector (Float × Float) (half_size) := FFT half_size (get_evens samples)
      (pow2Nat.always_ge1 size)
    let odds : Vector (Float × Float) (half_size) := FFT half_size (get_odds samples)
      (pow2Nat.always_ge1 size)
    -- twiddle
    let indices : List ℕ := List.range half_size
    let theta : List Float :=  indices.map
      (fun k => -1 * (2 * 3.141592653589793 * k.toFloat) / size.val.toFloat )
    -- k is the element, not the index
    let twiddle : List (Float × Float) :=
      theta.map (fun k => (cos k, sin k )) -- trying to keep the complex numbers in 2 pieces
    --
    let twiddle_odd : Vector (Float × Float) half_size :=
      odds.mapFinIdx (fun i o _ =>
        -- i is index
        -- o is the odd component (1, 2)
        let w := twiddle[i]!
        -- w is twiddle (1, 2)
        let R := o.1 * w.1
        let I := o.2 * w.2
        (R, I))
    --
    -- recombine
    let waves_top := twiddle_odd.mapFinIdx (fun i k _ =>
      let R := evens[i]!.1 + twiddle_odd[i]!.1
      let I := evens[i]!.2 + twiddle_odd[i]!.2
      (R, I)
     )
    --
    let waves_bottom := twiddle_odd.mapFinIdx (fun i k _ =>
      let R := evens[i]!.1 - twiddle_odd[i]!.1
      let I := evens[i]!.2 - twiddle_odd[i]!.2
      (R, I)
    )
    --
    -- Lean doesnt believe me that (pow2Nat / 2) + (pow2Nat / 2) = pow2Nat
    -- FIXED see above theorem
    let two_halves : Vector (Float × Float) (half_size + half_size) :=
      Vector.append waves_top waves_bottom
    let waves' : Vector (Float × Float) size.val :=
      two_halves.cast (pow2Nat.half_and_half size h_gt2)
    --
    waves'
    --
        -- also still need to show termination via recersion. Telling lean the lists get smaller.
    termination_by size.val
    decreasing_by all_goals exact pow2Nat.div2_lt size h_gt2

end Fourrier
