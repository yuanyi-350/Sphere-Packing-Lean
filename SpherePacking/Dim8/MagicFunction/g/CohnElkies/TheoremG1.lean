import SpherePacking.Dim8.MagicFunction.g.Basic
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.RealValued
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.SignConditions


/-!
# Cohn-Elkies hypotheses for `g`

This file packages the real-valuedness and sign properties of Viazovska's magic function `g`
needed for the Cohn-Elkies linear programming bound, corresponding to blueprint Theorem `thm:g1`.

This is a lightweight aggregation layer; proofs live in the smaller files.

## Main statements
* `MagicFunction.g.CohnElkies.g_cohnElkies₁`
* `MagicFunction.g.CohnElkies.g_cohnElkies₂`
-/

namespace MagicFunction.g.CohnElkies

open scoped FourierTransform SchwartzMap

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

/-- Cohn-Elkies condition (g1): `g` is nonpositive outside radius `sqrt 2`. -/
public theorem g_cohnElkies₁ : ∀ x : ℝ⁸, ‖x‖ ≥ Real.sqrt 2 → (g x).re ≤ 0 := by
  intro x hx
  have hx2 : (2 : ℝ) ≤ ‖x‖ ^ (2 : ℕ) := by
    have hxSq : (Real.sqrt 2) ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Real.sqrt_nonneg 2) (by simpa using hx) 2
    simpa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hxSq
  exact g_nonpos_of_norm_sq_ge_two x hx2

/-- Cohn-Elkies condition (g2): the Fourier transform `𝓕 g` has nonnegative real part. -/
public theorem g_cohnElkies₂ : ∀ x : ℝ⁸, (𝓕 g x).re ≥ 0 := by
  simpa using fourier_g_nonneg

end MagicFunction.g.CohnElkies
