import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import FFT.Lean.DFT_Real

namespace Fourier
open Real


-- A helper for getting every other element of the vector.
def get_evens {n : ℕ} (input : Vector ℂ (2 ^ n)) (h : n ≥ 1)
: Vector ℂ (2^(n - 1)):=
  Vector.ofFn fun (i : Fin (2 ^ (n - 1))) => input[2 * i.val]'(by
    have h1 : i.val < 2 ^ (n - 1) := i.isLt
    have h_pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      refine Eq.symm (mul_pow_sub_one ?_ 2)
      omega
    omega)

-- And for odds.
def get_odds {n : ℕ} (input : Vector ℂ (2 ^ n)) (h : n ≥ 1)
: Vector ℂ (2^(n - 1)):=
  Vector.ofFn fun (i : Fin (2 ^ (n - 1))) => input[2 * i.val + 1]'(by
    have h1 : i.val < 2 ^ (n - 1) := i.isLt
    have h_pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      refine Eq.symm (mul_pow_sub_one ?_ 2)
      omega
    omega)

--here we go
noncomputable def FFT (n : ℕ) (samples : Vector ℂ (2 ^ n)) :
  Vector ℂ (2 ^ n) :=
  let size : ℕ := 2 ^ n
  if h_base : n = 0  then
    samples
  else
    -- The actual meat and potatoes
    have h_gt1 : n ≥ 1 := by omega
    -- recursion
    let half_size : ℕ := (2 ^ (n - 1))
    let evens : Vector ℂ half_size := FFT (n - 1) (get_evens samples h_gt1)
    let odds : Vector ℂ half_size := FFT (n - 1) (get_odds samples h_gt1)
    -- twiddle
    -- k is the element not an index
    let twiddle : ℕ → ℂ := fun k => ω size ^ k --- This now imports twiddle from DFT_Real
    --
    let twiddle_odd : Vector ℂ half_size :=
      odds.mapFinIdx (fun i o _ => o * twiddle i) -- upsetting how simple this makes it.
    --
    -- recombine
    let waves_top := twiddle_odd.mapFinIdx (fun i _ _ => evens[i] + twiddle_odd[i])
    --
    let waves_bottom := twiddle_odd.mapFinIdx (fun i _ _ => evens[i] - twiddle_odd[i])
    let waves : Vector ℂ (size) :=
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
