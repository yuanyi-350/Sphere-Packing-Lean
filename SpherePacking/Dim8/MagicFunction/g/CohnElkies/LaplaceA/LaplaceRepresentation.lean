module
public import SpherePacking.Dim8.MagicFunction.g.CohnElkies.LaplaceA.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.LaplaceA.TailDeformation
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.LaplaceA.FiniteDifference
import SpherePacking.Dim8.MagicFunction.g.CohnElkies.IntegralPieces

/-!
# Laplace representation for `a'`

This file proves the main Laplace representation for the radial profile `a'`, used in the
blueprint proposition `prop:a-double-zeros`.

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.aRadial_eq_laplace_phi0_main`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

open scoped BigOperators UpperHalfPlane Topology intervalIntegral
open MeasureTheory Real Complex Filter
open UpperHalfPlane
open MagicFunction.FourierEigenfunctions
open MagicFunction.a.ComplexIntegrands

/-- Main lemma for blueprint proposition `prop:a-double-zeros`. -/
public theorem aRadial_eq_laplace_phi0_main {u : ℝ} (hu : 2 < u) :
    a' u =
      (4 * (Complex.I : ℂ)) *
        (Real.sin (π * u / 2)) ^ (2 : ℕ) *
          (∫ t in Set.Ioi (0 : ℝ),
            ((t ^ (2 : ℕ) : ℝ) : ℂ) *
              φ₀'' ((Complex.I : ℂ) / (t : ℂ)) *
                Real.exp (-π * u * t)) := by
  -- Proof outline (blueprint `prop:a-double-zeros`):
  -- 1. Introduce the contour integral `d(u)` and express `a' u` in terms of it.
  -- 2. Expand `sin^2` and rewrite `d(u)` as a linear combination of vertical-ray integrals.
  -- 3. Deform rays to the rectangle contour defining the pieces of `a'`, using decay.
  -- 4. Simplify the "tail" via the finite-difference identity for `φ₀''`.
  -- 5. Parametrize the remaining ray integral by `z = I*t` to reach the Laplace form.
  have hu0 : 0 ≤ u := (lt_trans (by norm_num : (0 : ℝ) < 2) hu).le
  -- Rewrite `a'` in terms of the raw real-integral definition.
  have ha : a' u = MagicFunction.a.RealIntegrals.a' u := by
    simpa using (MagicFunction.g.CohnElkies.a'_eq_realIntegrals_a' (u := u) hu0)
  rw [ha]
  dsimp [MagicFunction.a.RealIntegrals.a']
  -- Group the six pieces as `(I₁'+I₃'+I₅') + (I₂'+I₄'+I₆')`.
  have hsplit :
      MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₂' u +
            MagicFunction.a.RealIntegrals.I₃' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₅' u + MagicFunction.a.RealIntegrals.I₆' u =
          (MagicFunction.a.RealIntegrals.I₁' u + MagicFunction.a.RealIntegrals.I₃' u +
              MagicFunction.a.RealIntegrals.I₅' u) +
            (MagicFunction.a.RealIntegrals.I₂' u + MagicFunction.a.RealIntegrals.I₄' u +
              MagicFunction.a.RealIntegrals.I₆' u) := by
    ring
  rw [hsplit]
  -- Replace each grouped part by an imaginary-axis integral of `Φ₅'`.
  rw [I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u)]
  rw [I₂'_add_I₄'_add_I₆'_eq_imag_axis_tail (u := u) hu]
  -- Convert the segment integral to a set integral on `Ioc (0,1]` and combine with the tail.
  have hseg :
      (∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)) =
        ∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I) := by
    -- `intervalIntegral` is the integral on `uIoc`, and `uIoc 0 1 = Ioc 0 1`.
    simp [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    exact one_smul ℝ (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I))
  rw [hseg]
  have hsplitIoi :
      (Set.Ioi (0 : ℝ)) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
    simp [Set.Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one]
  have hIoi :
      (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I)) +
          (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
        ∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I) := by
    have h5Ioi0 :
        IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (0 : ℝ)) volume :=
      integrableOn_Φ₅'_imag_axis_Ioi0 (u := u) hu
    have h5Ioc :
        IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioc (0 : ℝ) 1) volume :=
      h5Ioi0.mono_set (by
        intro t ht
        exact ht.1)
    have h5Ioi1 :
        IntegrableOn (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (Set.Ioi (1 : ℝ)) volume :=
      (integrableOn_Φ₅'_imag_axis (u := u) hu)
    -- Rewrite the RHS as an integral over the disjoint union.
    rw [hsplitIoi]
    -- Apply additivity on disjoint unions, then rearrange.
    simpa [add_comm, add_left_comm, add_assoc] using
      (MeasureTheory.setIntegral_union (μ := volume)
        (f := fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I))
        (s := Set.Ioc (0 : ℝ) 1) (t := Set.Ioi (1 : ℝ))
        (hst := Set.Ioc_disjoint_Ioi_same)
        (ht := measurableSet_Ioi) h5Ioc h5Ioi1).symm
  -- Combine the two `Φ₅'` pieces into a single ray integral.
  set coeff : ℂ :=
    (Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) +
        Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ))
  have hcomb :
      (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioc (0 : ℝ) 1, Φ₅' u ((t : ℂ) * Complex.I))) +
          (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) =
        (Complex.I : ℂ) * (coeff * (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I))) := by
    -- Factor and use `hIoi`.
    rw [← hIoi]
    ring
  -- Replace the sum by the combined form.
  rw [hcomb]
  -- Trigonometric simplification of the exponential coefficient.
  have hcoeff :
      coeff = -((4 * (Real.sin (π * u / 2)) ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hrew :
        coeff =
          -((2 : ℂ) - Complex.exp (((π * u : ℝ) : ℂ) * Complex.I) -
              Complex.exp (-(((π * u : ℝ) : ℂ) * Complex.I))) := by
      simp [coeff]
      ring
    have htrig := MagicFunction.g.CohnElkies.Trig.two_sub_exp_pi_mul_I_sub_exp_neg_pi_mul_I u
    have hhalf := MagicFunction.g.CohnElkies.Trig.two_sub_two_cos_eq_four_sin_sq u
    grind only
  -- Convert the `Φ₅'`-ray integral to the Laplace integral.
  have hΦ5 :
      (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
        - (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := by
    have hcongr :
        (∫ t in Set.Ioi (0 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) =
          ∫ t in Set.Ioi (0 : ℝ), -aLaplaceIntegrand u t := by
      refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi ?_
      intro t ht
      simpa using (Φ₅'_imag_axis_eq_neg_aLaplaceIntegrand (u := u) (t := t))
    -- Pull the negation out of the integral.
    have hneg :
        (∫ t in Set.Ioi (0 : ℝ), -aLaplaceIntegrand u t) =
          - (∫ t in Set.Ioi (0 : ℝ), aLaplaceIntegrand u t) := integral_neg (aLaplaceIntegrand u)
    simpa using hcongr.trans hneg
  -- Finish by substitution and normalization.
  rw [hcoeff, hΦ5]
  -- `(-1) * (-1) = 1` and everything else is a definitional unfold.
  simp [aLaplaceIntegrand, mul_assoc, mul_left_comm, mul_comm]

end MagicFunction.g.CohnElkies.IntegralReps
