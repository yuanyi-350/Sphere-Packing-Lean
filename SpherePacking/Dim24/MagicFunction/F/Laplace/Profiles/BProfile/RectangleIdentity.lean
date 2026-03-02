module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
public import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.EvenU.BProfileZeros
public import SpherePacking.Dim24.MagicFunction.F.BKernelAsymptotics
public import SpherePacking.Dim24.MagicFunction.F.Laplace.KernelTools
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.LeadingCorrection
public import SpherePacking.Dim24.MagicFunction.F.Laplace.B.SubLeadingBounds.BKernelSubLeadingBound
public import SpherePacking.Dim24.MagicFunction.F.ProfileComplex.B
public import SpherePacking.Dim24.MagicFunction.F.Laplace.TopologyDomains
public import SpherePacking.Dim24.Inequalities.Defs
import SpherePacking.Tactic.NormNumI
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
public import SpherePacking.Dim24.MagicFunction.Radial
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import SpherePacking.Dim24.MagicFunction.F.Laplace.A.Basic
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSRectIdentity
import SpherePacking.Dim24.ModularForms.Psi.Relations
public import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU


/-!
# Rectangle identities for `ψS` and `ψT`

This file records basic identities relating the cusp forms `ψS`, `ψT`, and their sum `ψI`, and
proves a rectangle identity for the `ψS'` integrand against the exponential weight `expU`.

These lemmas are used in the convergent Laplace representation of `bProfile` for `u > 4`.

## Main statements
* `ψI'_eq_ψS'_add_ψT'`
* `ψS_rect_integral_eq_one_add_expU_one_mul_vertical`
-/

namespace SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped UpperHalfPlane Interval Topology

open Complex Filter MeasureTheory Real SchwartzMap Set
open UpperHalfPlane
open MagicFunction.Parametrisations RealIntegrals SpecialValuesAux

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

lemma ψS'_eq (z : ℂ) (hz : 0 < z.im) :
    ψS' z = ψS (UpperHalfPlane.mk z hz) := by
  simp [ψS', hz]

/-- On the upper half-plane, `ψT'` agrees with `ψT` viewed as a function on `ℍ`. -/
public lemma ψT'_eq (z : ℂ) (hz : 0 < z.im) :
    ψT' z = ψT (UpperHalfPlane.mk z hz) := by
  simp [ψT', hz]

/-- On the imaginary axis, the derivative `ψI'` splits as `ψS' + ψT'`. -/
public lemma ψI'_eq_ψS'_add_ψT' (t : ℝ) (ht : 0 < t) :
    ψI' ((t : ℂ) * Complex.I) = ψS' ((t : ℂ) * Complex.I) + ψT' ((t : ℂ) * Complex.I) := by
  set z : ℂ := (t : ℂ) * Complex.I
  have hz : 0 < z.im := by simpa [z] using ht
  let w : ℍ := UpperHalfPlane.mk z hz
  have hsum : ψS w + ψT w = ψI w := congrFun ψS_add_ψT_eq_ψI w
  have : ψS' z + ψT' z = ψI' z := by
    simpa [ψI', hz, w, (ψS'_eq z hz).symm, (ψT'_eq z hz).symm] using hsum
  simpa [z] using this.symm

/-- Rectangle identity for the `ψS'` integrand against `expU`, written as an integral on `t > 1`. -/
public lemma ψS_rect_integral_eq_one_add_expU_one_mul_vertical (u : ℝ) (hu0 : 0 ≤ u) :
    (∫ x in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I)) =
      (1 + expU u 1) *
        (Complex.I • ∫ t in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) := by
  simpa using (SpecialValuesAux.ψS_rect_integral_eq_one_add_expU_one_mul_vertical (u := u) hu0)


/-!
### Convergent Laplace representation for `bProfile` (range `u > 4`)

We combine:
- the already-proved segment identity `LaplaceB.J₁'_add_J₃'_add_J₅'_eq_imag_axis`, and
- a rectangle deformation for the `ψT'`-integrand (using `u > 4` to control the top edge),
- the `ψS`-rectangle identity `ψS_rect_integral_eq_one_add_expU_one_mul_vertical`,
to show that `bProfile u` is `-4i sin(πu/2)^2` times the Laplace transform of `ψI` on the
positive imaginary axis (paper equation (b2)).
-/

end

end SpherePacking.Dim24.LaplaceTmp.LaplaceProfiles.LaplaceBProfile
