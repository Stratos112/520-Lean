import FFT.Lean.DFT_Real
import FFT.Lean.FFT_Real
import Mathlib.Data.Nat.Cast.Field

/-! ... -/ --?? wtf .. IDK what this is.

namespace Fourier

-- ok so the issue here is just using sin and cos instead of e^-2pi like I did on paper.
-- Which is actually good because it will force me to improve my understanding of the relationship.

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


-- this is the butterfly lemma
lemma lemma_6 (k : ℕ) (hk : k < N n) :
    (E_fun n S hn' k) + ω (N n) ^ k * (O_fun n S hn' k) = (DFT (N n) S)[k]'hk := by
  unfold DFT per_reference per_sample
  rw [@Vector.getElem_ofFn]
  rw [← @Fin.sum_univ_def]
  unfold E_fun O_fun
  -- Ok everything is in math notation
  let x : ℕ → ℂ := fun j => if h : j < N n then S[j] else 0
  have hR : ∑ j : Fin (N n), S[j] * ω (N n) ^ (j.val * k)
    = ∑ j ∈ Finset.range (N n), x j * ω (N n) ^ (j * k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => x j * ω (N n) ^ (j * k))]
    apply Finset.sum_congr rfl
    intro j _
    simp [x]
  have hR2 : ∑ j ∈ Finset.range (2 * M n), x j * ω (N n) ^ (j * k)
    = ∑ j ∈ Finset.range (N n), x j * ω (N n) ^ (j * k) := by rw [← lemma_m2 n hn']
  conv => {
    rhs
    simp only [Fin.val_mk]
    rw [hR]
    rw [← hR2]
    rw [split_lemma] -- omg that was way too hard lol
  }
  -- So now we set about on a journey to try and rearrange the power terms which are inside the sum
  -- ok so fin them to range
  have hE : ∑ l : Fin (M n), (E n S hn')[l] * ω (M n) ^ (↑l * k)
    = ∑ l ∈ Finset.range (M n), x (2 * l) * ω (M n) ^ (l * k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => x (2 * j) * ω (M n) ^ (j * k)) (M n)]
    apply Finset.sum_congr rfl
    intro m _
    congr
    unfold E get_evens
    have hl : 2 * m.val < N n := by
      have := m.isLt
      have := lemma_m2 n hn'
      omega
    simp [x]
    simp [hl]
    rfl
  have hO : ∑ l : Fin (M n), (O n S hn')[l] * ω (M n) ^ (↑l * k)
    = ∑ l ∈ Finset.range (M n), x (2 * l + 1) * ω (M n) ^ (l * k) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => x (2 * j + 1) * ω (M n) ^ (j * k)) (M n)]
    apply Finset.sum_congr rfl
    intro m _
    congr
    unfold O get_odds
    have hl : 2 * m.val + 1< N n := by
      have := m.isLt
      have := lemma_m2 n hn'
      omega
    simp [x]
    simp [hl]
    rfl
  -- Sorry, I should have factored these out.
  -- Idk if this could have been made easier by somehow casting them?
  -- I guess i'm less than confident in the difference between fin, finset, sum and range because ??
  -- But we're using finsets now
  rw [hE, hO]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  -- Hey now its looking pretty good
  intro m _
  rw [lemma_3 n hn']
  rw [← pow_mul]
  conv => {lhs; arg 2; rw [← mul_assoc]}
  rw [mul_assoc 2 m k]
  rw [add_mul]
  rw [one_mul]
  rw [pow_add]
  rw [mul_assoc 2 m k]
  congr 1
  -- omg I guess il;l just spoon feed you everything lean
  rw [mul_comm (ω (N n) ^ k) (x (2 * m + 1))]
  rw [mul_assoc]
  rw [mul_comm (ω (N n) ^ k)]
  --by rfl. but it did it automatically? cool ig.


-- The bottom half. Essentially reusing the rest of this stuff. 
lemma lemma_7

-- THE FINAL BOSS --

theorem FFT_correct (n : ℕ) (S : Vector ℂ (2 ^ n)) :
  (FFT n S) = (DFT (2 ^ n) S) := by
  unfold FFT DFT per_reference per_sample

    induction K with
    | zero => sorry
    | succ K ih => sorry

end Fourier
