import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FFT.Lean.Basic_Real
namespace Fourier
open Real

-- A helper for getting every other element of the vector.
def get_evens {n : ℕ} (input : Vector (Real × Real) (2 ^ n)) (h : n ≥ 1)
: Vector (Real × Real) (2^(n - 1)):=
  Vector.ofFn fun (i : Fin (2 ^ (n - 1))) => input[2 * i.val]'(by
    have h1 : i.val < 2 ^ (n - 1) := i.isLt
    have h_pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      refine Eq.symm (mul_pow_sub_one ?_ 2)
      omega
    omega)
-- And for odds.
def get_odds {n : ℕ} (input : Vector (Real × Real) (2 ^ n)) (h : n ≥ 1)
: Vector (Real × Real) (2^(n - 1)):=
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
noncomputable def FFT (n : ℕ) (samples : Vector (Real × Real) (2 ^ n)) :
  Vector (Real × Real) (2 ^ n) :=
  let size : ℕ := 2 ^ n
  if h_base : n = 0  then
    samples
  else
    -- The actual meat and potatoes
    have h_gt1 : n ≥ 1 := by omega
    -- recursion
    let half_size : ℕ := (2 ^ (n - 1))
    let evens : Vector (Real × Real) half_size := FFT (n - 1) (get_evens samples h_gt1)
    let odds : Vector (Real × Real) half_size := FFT (n - 1) (get_odds samples h_gt1)
    -- twiddle
    -- k is the element not an index
    let twiddle : ℕ → Real × Real :=
      fun k => (cos (-(2 * π * k) / size), sin (-(2 * π * k) / size))
    --
    let twiddle_odd : Vector (Real × Real) half_size :=
      odds.mapFinIdx (fun i o _ =>
        -- i is index
        -- o is the odd component (1, 2)
        let w := twiddle i
        -- w is twiddle (1, 2) -- AHA!
        let R := o.1 * w.1 - o.2 * w.2
        let I := o.1 * w.2 + o.2 * w.1
        (R, I))
    --
    -- recombine
    let waves_top := twiddle_odd.mapFinIdx (fun i _ _ =>
      let R := evens[i].1 + twiddle_odd[i].1
      let I := evens[i].2 + twiddle_odd[i].2
      (R, I)
     )
    --
    let waves_bottom := twiddle_odd.mapFinIdx (fun i _ _ =>
      let R := evens[i].1 - twiddle_odd[i].1
      let I := evens[i].2 - twiddle_odd[i].2
      (R, I)
    )
    let waves : Vector (Real × Real) (size) :=
      Vector.ofFn fun (i : Fin (size)) =>
        if h: (i.val < 2 ^ (n - 1)) then
          waves_top[i.val]
        else
          have hfs : size - half_size ≤ half_size := by
            simp only [tsub_le_iff_right]
            rw[Nat.two_pow_pred_add_two_pow_pred]
            omega
          waves_bottom[i.val - 2 ^ (n - 1)]'(by omega)
    waves
    --
        -- also still need to show termination via recursion. Telling lean the lists get smaller.
    termination_by n
    decreasing_by all_goals omega

end Fourier
