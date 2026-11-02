import FFT.Lean.DFT_Real
import FFT.Lean.FFT_Real
import Mathlib.Data.Nat.Cast.Field

/-! ... -/ --?? wtf .. IDK what this is.

namespace Fourier

-- ok so the issue here is just using sin and cos instead of e^-2pi like I did on paper.
-- Or to translate them.
-- Which is actually good because it will force me to improve my understanding of the relationship.

-- Addendum, and idk if this was Ewens suggestion or both, but I'm going to refactor this to use
-- Complex.exp (base e). The old code can still be found at "FFT_Real_Old" and "Basic_Real_old"


-- DEFINITIONS --

-- N is some 2 pow
variable (n : ℕ) (hn : n ≥ 0)
def N : ℕ := 2 ^ n
-- M is the half size constant
def M : ℕ := 2 ^ (n - 1)
-- S is a vector of samples
variable (S : Vector ℂ (N n))

-- We can pull twiddle ω from DFT_Real

-- Evens and odds
variable (hn' : n ≥ 1)
def E := (get_evens S hn')
def O := (get_odds S hn')
noncomputable def E_fun (k : ℕ) : ℂ :=
   -- this syntax is actually great. Thanks claude
  ∑ l : Fin (M n), (E n S hn')[l] * ω (M n) ^ (l * k)
noncomputable def O_fun (k : ℕ) : ℂ :=
  ∑ l : Fin (M n), (O n S hn')[l] * ω (M n) ^ (l * k)


-- LEMMAS --

lemma lemma_1 (hn' : n ≥ 1) : ω (N n) ^ ((N n) / 2) = -1 := by
  simp only [ω]
  rw [← Complex.exp_nat_mul]
  have h2 : 2 ∣ N n := dvd_pow_self 2 (by omega)
  rw [Nat.cast_div_charZero h2] -- gross. this NAt division is a problem.
  push_cast
  rw [neg_mul_comm]
  field_simp
  rw [mul_div_right_comm]
  rw [mul_div_right_comm]
  rw [div_self]
  · simp
  · unfold N -- Im genuinly so confused why it thought that n could be 0.
    -- .. and then wouldnt let me use hn'?
    -- is this because of casting from complex numbers to Nats?
    simp
    -- Oh wait! cus when I div_Self it has to make sure its not 0.
    -- still dumb that hn' didnt stick but it makes sense because type casting

lemma lemma_2 (hn' : n ≥ 1) : (ω (N n) ^ 2) ^ ((N n) / 2) = 1 := by
  simp only [ω]
  rw [← Complex.exp_nat_mul]; rw [← Complex.exp_nat_mul]
  have h2 : 2 ∣ N n := dvd_pow_self 2 (by omega)
  rw [Nat.cast_div_charZero h2]
  push_cast;
  field_simp
  rw [mul_div_right_comm]; rw [mul_div_right_comm]; rw [mul_div_right_comm];
  rw [div_self]
  · rw [one_mul]
    rw [Complex.exp_neg] -- Oh come on. lol.
    rw [Complex.exp_two_pi_mul_I]
    simp
  · unfold N
    simp


-- Ok I'm on a roll
lemma lemma_3 (hn' : n ≥ 1) : ω (M n) = ω (N n) ^ 2 := by
  simp only [ω]
  rw [← Complex.exp_nat_mul]
  congr  -- thats nifty
  field_simp
  conv => {
    rhs
    arg 1
    arg 2
    unfold N
    rw [Nat.cast]
    rw [← Nat.two_pow_pred_mul_two hn']
  }
  unfold M
  push_cast
  field_simp


--ok a little helper
lemma lemma_m2 (hn' : n ≥ 1) : N n = 2 * M n  := by
  unfold M N
  rw [← Nat.two_pow_pred_mul_two]
  · omega
  · omega

lemma root_lemma (hn' : n ≥ 1) : ω (M n) ^ (M n) = 1 := by
  have h2 : N n / 2 = M n := by
   rw [lemma_m2]
   · omega
   · omega
  rw [lemma_3 n hn', ← h2]
  exact lemma_2 n hn'

--Im going to do this in a slightly different order.
-- if I show the repetition period first, then the butterfly might be easier
-- also just trying to replicate my english proof at this point.
lemma lemma_4 (k : ℕ) : (E_fun n S hn' (k + M n)) = E_fun n S hn' k := by
  unfold E_fun
  rw [Finset.sum_congr rfl] -- this is apparently how I undo the sum notation
  intro l j
  congr 1
  rw [mul_add]
  rw [pow_add]
  rw [mul_comm]
  conv => {lhs; arg 1; arg 2; rw [mul_comm]}
  rw [pow_mul]
  rw [root_lemma n hn']
  simp

-- 5 is the same as 4 but with Odd
lemma lemma_5 (k : ℕ) : (O_fun n S hn' (k + M n)) = O_fun n S hn' k := by
  unfold O_fun
  rw [Finset.sum_congr rfl] -- this is apparently how I undo the sum notation
  intro l j
  congr 1
  rw [mul_add]
  rw [pow_add]
  rw [mul_comm]
  conv => {lhs; arg 1; arg 2; rw [mul_comm]}
  rw [pow_mul]
  rw [root_lemma n hn']
  simp


-- lemma 6

-- shoot Im gonna need a helper
lemma split_lemma (f : ℕ → ℂ) (K : ℕ) :
  ∑ i ∈ Finset.range (2 * K), f i = ∑ m ∈ Finset.range K, (f (2*m) + f (2*m+1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Nat.two_mul]
      rw [← Nat.add_left_comm]
      rw [← Nat.add_assoc]
      rw [← Nat.add_assoc]
      rw [← Nat.mul_two]
      rw [Nat.mul_comm]
      rw [Finset.sum_range_succ] --??
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ]
      grind

 -- Cont'd in the 'Correct_Proof' file
end Fourier
