import FFT.Lean.DFT_Real
import FFT.Lean.FFT_Real
import FFT.Lean.FFT_Correct_Lemmas
import Mathlib.Data.Nat.Cast.Field

/-! ... -/ --?? wtf .. IDK what this is.

namespace Fourier

variable (n : ℕ) (hn : n ≥ 0)
variable (S : Vector ℂ (N n))
variable (hn' : n ≥ 1)


-- this is the butterfly lemma
lemma lemma_6 (k : ℕ) (hk : k < 2 ^ n) :
    (E_fun n S hn' k) + ω (2 ^ n) ^ k * (O_fun n S hn' k) = (DFT (2 ^ n) S)[k]'hk := by
  have hk' : k < N n := hk
  change (E_fun n S hn' k) + ω (N n) ^ k * (O_fun n S hn' k) = (DFT (N n) S)[k]'hk'
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
lemma lemma_7 (k : ℕ) (hk : k + 2 ^ (n - 1) < 2 ^ n) :
    E_fun n S hn' k - ω (2 ^ n) ^ k * O_fun n S hn' k = (DFT (2 ^ n) S)[k + 2 ^ (n - 1)]'hk := by
  have hk' : k + M n < N n := hk
  change E_fun n S hn' k - ω (N n) ^ k * O_fun n S hn' k = (DFT (N n) S)[k + M n]'hk'
  have h6 : E_fun n S hn' (k + M n) + ω (N n) ^ (k + M n) * O_fun n S hn' (k + M n)
  = (DFT (N n) S)[k + M n]'hk' :=
    lemma_6 n S hn' (k + M n) hk
  rw [← h6]
  rw [lemma_4]
  rw [lemma_5]
  rw [pow_add]
  have half (hn' : n ≥ 1) : ω (N n) ^ M n = -1 := by
    rw [← lemma_1 n hn']
    congr 1
    rw [lemma_m2 n hn']
    omega
  rw [half hn']
  rw [mul_neg_one]
  rw [neg_mul]
  rw [ ← sub_eq_add_neg]
  -- does this use all the lemmas? no. missing #3. cool though.


-- THE FINAL BOSS --
-- Though on hindsight not really, butterfly was the big enchilada. this is just housekeeping

lemma E_fun_eq_DFT (m : ℕ) (S : Vector ℂ (2 ^ (m + 1))) (hn' : m + 1 ≥ 1) (k : ℕ) (hk : k < 2 ^ m) :
    (DFT (2 ^ m) (get_evens S hn'))[k] = E_fun (m + 1) S hn' k := by
  unfold DFT per_reference per_sample E_fun
  rw [Vector.getElem_ofFn]
  simp
  rfl

lemma O_fun_eq_DFT (m : ℕ) (S : Vector ℂ (2 ^ (m + 1))) (hn' : m + 1 ≥ 1) (k : ℕ) (hk : k < 2 ^ m) :
    (DFT (2 ^ m) (get_odds S hn'))[k] = O_fun (m + 1) S hn' k := by
  unfold DFT per_reference per_sample O_fun
  rw [Vector.getElem_ofFn]
  simp
  rfl

set_option maxHeartbeats 1000000 in
theorem FFT_correct (n : ℕ) (S : Vector ℂ (2 ^ n)) :
  (FFT n S) = (DFT (2 ^ n) S) := by
  induction n with
  | zero =>
    unfold FFT
    apply Vector.ext --Ah this is the magic ok.
    intro i hi
    unfold DFT per_reference per_sample
    simp only [Nat.pow_zero, ↓reduceDIte, Fin.getElem_fin, Fin.val_eq_zero, pow_zero, mul_zero,
      mul_one, Vector.getElem_ofFn] -- Let the record show I just did a "simp" here
      -- the above  was the result of a warning and applying the suggestion
      -- tbh I feel like thats a lot of things for "simp *only*" so perhaps a silly warning
    rw [List.finRange_succ]
    simp
    -- ?? this should be rfl.
    -- ok genuine question, why doesnt rw or apply [hi] or similar work?
    -- also, shouldnt simnp and omega see this i=0 by default?
    have h_base_rfl : i = 0 := by omega --??????????? LMAO
    grind

  | succ m ih =>
    -- starting the same as zero case.
    unfold FFT
    apply Vector.ext
    intro i hi
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte, add_tsub_cancel_right,
      Nat.add_one_sub_one, Vector.getElem_mapFinIdx, Vector.mapFinIdx_mapFinIdx,
      Vector.getElem_ofFn]
    --ok I ha ve to pull apart the if: R + I vs R -I
    by_cases h_tb : i < 2 ^ m
    · rw [dite_eq_left h_tb]
      simp only [ih]
      conv => {
        lhs
        rw [E_fun_eq_DFT]
        rw [O_fun_eq_DFT]
      }
      rw [mul_comm]
      rw [lemma_6 (m + 1) S (by omega)] -- yay
    · rw [dite_eq_right h_tb]
      simp only [ih]
      have hii : i - 2 ^ m < 2 ^ m := by omega
      rw [mul_comm]
      have hl7 := lemma_7 (m + 1) S (by omega) (i - 2 ^ m) (by
        rw [Nat.add_one_sub_one]
        omega)
      rw [E_fun_eq_DFT m S (by omega) (i - 2 ^ m) hii]
      rw [O_fun_eq_DFT m S (by omega) (i - 2 ^ m) hii]
      rw [hl7]
      simp
      congr -- oh lol.
      omega

end Fourier
