module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Radial
public import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU
import SpherePacking.Dim24.MagicFunction.A.LaplaceZeros
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Periodic
import Mathlib.MeasureTheory.Integral.ExpDecay


/-!
# Contour identities for the zeros of `a`

This file collects auxiliary identities used in the proof of Lemma 2.1 of `dim_24.tex` (around
(2.16)-(2.17)). They rewrite the linear combination of the three S-transformed translates of
`varphi` in terms of `varphi` itself on the imaginary axis, producing the contour decomposition
`eq:conta`. These identities are also the starting point for the Laplace representation that
forces the Leech-radius zeros.

## Main statements
* `ZerosAux.coeff_two_mul_nat`
* `ZerosAux.aProfile_two_mul_nat_of_two_lt`
-/


local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace ZerosAux

open scoped Interval

/-! ### Even-integer vanishing of the one-variable profile -/

/-- The even-integer coefficient `expU (2k) 1 + (expU (2k) 1)⁻¹ - 2` vanishes. -/
public lemma coeff_two_mul_nat (k : ℕ) :
    (SpecialValuesAux.expU ((2 : ℝ) * k) 1)⁻¹ +
        SpecialValuesAux.expU ((2 : ℝ) * k) 1 - 2 = 0 := by
  have hu : SpecialValuesAux.expU ((2 : ℝ) * k) 1 = 1 :=
    SpecialValuesAux.expU_two_mul_nat_one (k := k)
  have : ((1 : ℂ)⁻¹ + (1 : ℂ) - (2 : ℂ)) = 0 := by norm_num
  simpa [hu] using this

/-- For integers `k > 2`, the contour representation implies `aProfile (2k) = 0`. -/
public lemma aProfile_two_mul_nat_of_two_lt (k : ℕ) (hk : 2 < k) :
    aProfile ((2 : ℝ) * k) = 0 := by
  set u : ℝ := (2 : ℝ) * k
  have hu4 : 4 < u := by
    have hk' : (2 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have : (4 : ℝ) < (2 : ℝ) * (k : ℝ) := by linarith
    simpa [u] using this
  have h135 := LaplaceZeros.I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u)
  have h246 :=
    LaplaceZerosTail.TailDeform.I₂'_add_I₄'_add_I₆'_eq_imag_axis (u := u) hu4
  -- Unfold and regroup the six contour pieces.
  dsimp [aProfile, RealIntegrals.a']
  calc
    RealIntegrals.I₁' u + RealIntegrals.I₂' u + RealIntegrals.I₃' u + RealIntegrals.I₄' u +
          RealIntegrals.I₅' u + RealIntegrals.I₆' u =
        (RealIntegrals.I₁' u + RealIntegrals.I₃' u + RealIntegrals.I₅' u) +
          (RealIntegrals.I₂' u + RealIntegrals.I₄' u + RealIntegrals.I₆' u) := by
          ac_rfl
    _ = 0 := by
        -- Both blocks are scalar multiples of the even-integer factor, which vanishes at `u=2k`.
        have hu : SpecialValuesAux.expU u 1 = 1 := by
          simpa [u] using SpecialValuesAux.expU_two_mul_nat_one (k := k)
        let x : ℂ := ((Real.pi * u : ℝ) : ℂ) * Complex.I
        have hx : (Real.pi : ℂ) * Complex.I * (u : ℂ) * (1 : ℂ) = x := by
          simp [x, mul_assoc, mul_left_comm, mul_comm]
        have hpos : Complex.exp x = 1 := by
          simpa [SpecialValuesAux.expU, hx, x] using hu
        have hneg : Complex.exp (-x) = 1 := by
          simp [Complex.exp_neg, hpos]
        grind only

end ZerosAux


end

end SpherePacking.Dim24
