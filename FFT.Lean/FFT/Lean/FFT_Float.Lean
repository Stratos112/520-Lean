import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FFT.Lean.Basic_Float
namespace Fourrier
open Float

-- Ok 3 goals:
-- 1. rewrite without pow2Nat. use n and 2 ^ n --           :)
-- 2. remove all []!                                        :)
-- 3. check the answers using DFT and the python script.  .. :(

--  From there, let's send it to Ewen and make sure I am on the right track,
--    before giving the new type cast for complex numbers a shot.


-- A helper for getting every other element of the vector.
def get_evens {n : ℕ} (input : Vector (Float × Float) (2 ^ n)) (h : n ≥ 1)
: Vector (Float × Float) (2^(n - 1)):=
  Vector.ofFn fun (i : Fin (2 ^ (n - 1))) => input[2 * i.val]'(by
    have h1 : i.val < 2 ^ (n - 1) := i.isLt
    have h_pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      refine Eq.symm (mul_pow_sub_one ?_ 2)
      omega
    omega)
-- And for odds.
def get_odds {n : ℕ} (input : Vector (Float × Float) (2 ^ n)) (h : n ≥ 1)
: Vector (Float × Float) (2^(n - 1)):=
  Vector.ofFn fun (i : Fin (2 ^ (n - 1))) => input[2 * i.val + 1]'(by
    have h1 : i.val < 2 ^ (n - 1) := i.isLt
    have h_pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      refine Eq.symm (mul_pow_sub_one ?_ 2)
      omega
    omega)

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
def FFT (n : ℕ) (samples : Vector (Float × Float) (2 ^ n)) :
  Vector (Float × Float) (2 ^ n) :=
  let size : ℕ := 2 ^ n
  let f0 : Float := 0.0
  if h_base : n = 0  then
    samples
  else
    -- The actual meat and potatoes
    have h_gt1 : n ≥ 1 := by omega
    -- recursion
    let half_size : ℕ := (2 ^ (n - 1))
    let evens : Vector (Float × Float) half_size := FFT (n - 1) (get_evens samples h_gt1)
    let odds : Vector (Float × Float) half_size := FFT (n - 1) (get_odds samples h_gt1)
    -- twiddle
    let indices : List ℕ := List.range half_size
    let theta : List Float :=  indices.map
      (fun k => -1 * (2 * 3.141592653589793 * k.toFloat) / size.toFloat )
    -- k is the element, not the index
    let twiddle : List (Float × Float) :=
      theta.map (fun k => (cos k, sin k )) -- trying to keep the complex numbers in 2 pieces
    --
    let twiddle_odd : Vector (Float × Float) half_size :=
      odds.mapFinIdx (fun i o _ =>
        -- i is index
        -- o is the odd component (1, 2)
        let w := twiddle[i]'(by grind)
        -- w is twiddle (1, 2) -- AHA! 
        let R := o.1 * w.1 - o.2 * w.2
        let I := o.1 * w.2 + o.2 * w.1
        (R, I))
    --
    -- recombine
    let waves_top := twiddle_odd.mapFinIdx (fun i k _ =>
      let R := evens[i].1 + twiddle_odd[i].1
      let I := evens[i].2 + twiddle_odd[i].2
      (R, I)
     )
    --
    let waves_bottom := twiddle_odd.mapFinIdx (fun i k _ =>
      let R := evens[i].1 - twiddle_odd[i].1
      let I := evens[i].2 - twiddle_odd[i].2
      (R, I)
    )
    let waves : Vector (Float × Float) (size) :=
      cast (by
      rw [Nat.two_pow_pred_add_two_pow_pred h_gt1] -- this literally came from rw? --
    ) (Vector.append waves_top waves_bottom)
    --
    waves
    --
        -- also still need to show termination via recursion. Telling lean the lists get smaller.
    termination_by n
    decreasing_by all_goals omega

def close (ε : Float) (xs ys : List (Float × Float)) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (a, b) =>
    (a.1 - b.1).abs ≤ ε && (a.2 - b.2).abs ≤ ε
def ε : Float := 1e-9

#eval FFT 2 (#v[(1,0), (1,0), (1,0), (1,0)])-- expect 4, 0, 0 ,0
#guard FFT 2 (#v[(1,0), (1,0), (1,0), (1,0)]) = #v[(4.0, 0.0), (0,0), (0,0), (0,0)]
#guard close ε (FFT 2 (#v[(1,0), (1,0), (1,0), (1,0)])).toList (DFT 4 (#v[1, 1, 1, 1])).toList

#eval FFT 2 (#v[(1,0), (2,0), (3,0), (4,0)]) -- expect (10,0), (-2 2) (-2 0) (-2 -2) -- Wrong?
#guard close ε (FFT 2 (#v[(1,0), (2,0), (3,0), (4,0)])).toList (DFT 4 (#v[1, 2, 3, 4])).toList

#eval FFT 3 (#v[(1,0), (2,0), (1,0), (2,0), (1,0), (2,0), (1,0), (2,0)])
--expect (12,0) (0,0), (0,0) (0,0) (-4,0), (0,0) (0,0) (0,0)
#guard close ε (FFT 3 (#v[(1,0), (2,0), (1,0), (2,0), (1,0), (2,0), (1,0), (2,0)])).toList (DFT 8 (#v[1, 2, 1, 2, 1, 2, 1, 2])).toList

#eval FFT 3 (#v[(2,0), (1,0), (0,0), (1,0), (2,0), (1,0), (0,0), (1,0)])
-- expect (8,0), 0, (4,0), 0 ,0 ,0 ,(4,0), 0
#guard close ε (FFT 3 (#v[(2,0), (1,0), (0,0), (1,0), (2,0), (1,0), (0,0), (1,0)])).toList (DFT 8 (#v[2, 1, 0, 1, 2, 1, 0, 1])).toList


#eval FFT 3 (#v[(0,0), (1,0), (2,0), (1,0), (0,0), (1,0), (2,0), (1,0)])
-- expect [(8.0, 0.0), (0.0, 0.0), (-4.0, 0.0), (-0.0, -0.0), (0.0, -0.0), (0.0, 0.0),
--         (-4.0, 0.0), (-0.0, 0.0)]
#guard close ε (FFT 3 (#v[(0,0), (1,0), (2,0), (1,0), (0,0), (1,0), (2,0), (1,0)])).toList (DFT 8 (#v[0, 1, 2, 1, 0, 1, 2, 1])).toList


-- NOT POW 2
--#eval FFT 4 (#v[2.0, -1.0, -1.0, 2.0, -1.0, -1.0, 2.0, -1.0, -1.0, 2.0, -1.0, -1.0])
-- expect [(0.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.0, 0.0), (12.0, 0.0), (0.0, 0.0), (0.0, 0.0),
--         (0.0, 0.0), (12.0, 0.0), (0.0, 0.0), (0.0, 0.0), (0.0, 0.0)]

end Fourrier
