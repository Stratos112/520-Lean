import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Batteries.Data.Float

/-! ... -/ --?? wtf

namespace Fourier

-- Sigh. Idk why I fought so hard to avoid this only to finally succumb to it in the end.
-- .. Defeat tastes like a wasted sunday ..  but I guess I feel good that I learned stuff.
noncomputable def ω (N : ℕ) : ℂ := Complex.exp (-2 * Real.pi * Complex.I / N)

noncomputable def per_sample (k : ℕ) (n : ℕ) (size : ℕ) (x : ℂ) : ℂ :=
  x * ω size ^ (n * k)

noncomputable def per_reference (k : ℕ) (size : ℕ) (samples : Vector ℂ size) : ℂ :=
  ((List.finRange size).map (fun (i : Fin size) =>
    per_sample k i.val size samples[i])).sum

noncomputable def DFT (size : ℕ) (samples : Vector ℂ size) : Vector ℂ size :=
  Vector.ofFn fun (k : Fin size) => per_reference k.val size samples


--- ...... Im upset that this is 8 lines now ...

end Fourier
