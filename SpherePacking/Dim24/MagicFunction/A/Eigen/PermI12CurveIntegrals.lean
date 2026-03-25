module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI12Prelude
import SpherePacking.Contour.Segments
import SpherePacking.Contour.PermJ12CurveIntegral


/-!
# Curve-integral representations for `I₁'` through `I₄'`

We rewrite the real integrals `RealIntegrals.I₁'`, ..., `RealIntegrals.I₄'` as contour
integrals along straight segments in `ℂ`. These formulas are used in the contour deformation
step for the `I₁/I₂` and `I₃/I₄` permutation identities.

## Main statements
* `I₁'_eq_curveIntegral_segment`, `I₂'_eq_curveIntegral_segment`
* `I₃'_eq_curveIntegral_segment`, `I₄'_eq_curveIntegral_segment`
-/

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section

open MagicFunction.Parametrisations
open MagicFunction
open scoped Interval

public instance instContinuousSMulRealComplex : ContinuousSMul ℝ ℂ := by
  refine ⟨?_⟩
  simpa [smul_eq_mul] using
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd

/-- `I₁' r` as a contour integral along the segment from `-1` to `-1 + i`. -/
public lemma I₁'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.I₁' r =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
        scalarOneForm (Φ₁' r) z) := by
  simpa [RealIntegrals.I₁', scalarOneForm_apply, RealIntegrals.RealIntegrands.Φ₁,
    RealIntegrals.ComplexIntegrands.Φ₁', Φ₁', mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₁ (f := Φ₁' r)).symm

/-- `I₂' r` as a contour integral along the segment from `-1 + i` to `i`. -/
public lemma I₂'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.I₂' r =
      (∫ᶜ z in Path.segment ((-1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Φ₁' r) z) := by
  simpa [RealIntegrals.I₂', scalarOneForm_apply, RealIntegrals.RealIntegrands.Φ₂,
    RealIntegrals.ComplexIntegrands.Φ₂', RealIntegrals.ComplexIntegrands.Φ₁', Φ₁',
    mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₂ (f := Φ₁' r)).symm

/-- `I₃' r` as a contour integral along the segment from `1` to `1 + i`. -/
public lemma I₃'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.I₃' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
        scalarOneForm (Φ₃' r) z) := by
  simpa [RealIntegrals.I₃', scalarOneForm_apply, RealIntegrals.RealIntegrands.Φ₃,
    RealIntegrals.ComplexIntegrands.Φ₃', Φ₃', mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₃ (f := Φ₃' r)).symm

/-- `I₄' r` as a contour integral along the segment from `1 + i` to `i`. -/
public lemma I₄'_eq_curveIntegral_segment (r : ℝ) :
    RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
        scalarOneForm (Φ₃' r) z) := by
  simpa [RealIntegrals.I₄', scalarOneForm_apply, RealIntegrals.RealIntegrands.Φ₄,
    RealIntegrals.ComplexIntegrands.Φ₄', RealIntegrals.ComplexIntegrands.Φ₃', Φ₃',
    mul_assoc, mul_left_comm, mul_comm] using
    (SpherePacking.Contour.curveIntegral_segment_z₄ (f := Φ₃' r)).symm

/-- A combined segment representation of `I₃' r + I₄' r`. -/
public lemma I₃'_add_I₄'_eq_curveIntegral_segments (r : ℝ) :
    RealIntegrals.I₃' r + RealIntegrals.I₄' r =
      (∫ᶜ z in Path.segment (1 : ℂ) ((1 : ℂ) + Complex.I),
          scalarOneForm (Φ₃' r) z) +
        ∫ᶜ z in Path.segment ((1 : ℂ) + Complex.I) Complex.I,
          scalarOneForm (Φ₃' r) z := by
  simp [I₃'_eq_curveIntegral_segment (r := r), I₄'_eq_curveIntegral_segment (r := r)]


end

end SpherePacking.Dim24.AFourier
