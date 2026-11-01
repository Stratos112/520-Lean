import FFT.Lean.DFT_Real
import FFT.Lean.FFT_Real

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
noncomputable def E_dft : Vector ℂ (M n) := DFT (M n) (E n S hn')
noncomputable def O_dft : Vector ℂ (M n) := DFT (M n) (O n S hn')

lemma lemma_1 : ω ^ ((N n) / 2) = -1 := by
  sorry

lemma lemma_2 : (ω^2) ^ ((N n) / 2) = 1 := by
  sorry

lemma lemma_3 (γ : ℂ) (hgamm := γ = (ω n) ^ (1 / (M n))) : γ = (ω n) ^ 2 :=  by
  sorry

--Im going to do this in a slightly different order.
-- if I show the repetition period first, then the butterfly might be easier
lemma lemma_4 (k : ℕ) (hk : k < (M n)) :
  ((E_dft n S hn')[k + (M n)]'(by sorry)) = ((E_dft n S hn')[k]'hk) := by
  sorry

-- 5 is the same as 4 but with Odd
lemma lemma_5 (k : ℕ) (hk : k < (M n)) :
  ((O_dft n S hn')[k + (M n)]'(by sorry)) = ((O_dft n S hn')[k]'hk) := by
  sorry

-- lemma 6
lemma lemma_6 (k : ℕ) (hk : k < (N n)) : ((E_dft n S hn')[k]'(by sorry)) +
  (((ω n) ^ k) : ℂ)  * ((O_dft n S hn')[k]'(by sorry))
  = ((DFT (N n) S)[k]'(by sorry)) := by
  sorry


-- claims ? -- Top half bottom half. ..

theorem FFT_correct (n : ℕ) (S : Vector ℂ (2 ^ n)) :
  (FFT n S) = (DFT (2 ^ n) S) := by
    sorry

end Fourier
