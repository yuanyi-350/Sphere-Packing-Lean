module
public import SpherePacking.Dim24.MagicFunction.F.Defs
public import SpherePacking.Dim24.MagicFunction.F.Fourier
public import SpherePacking.Dim24.MagicFunction.F.Zero
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Radial
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Final
public import SpherePacking.Dim24.MagicFunction.Radial
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul


/-!
# Special values of `f` and `𝓕 f`

This file records the special values (roots and derivatives) of the auxiliary function `f`
and its Fourier transform that are used in the dimension-24 argument.

## Main definitions
* `fRadial`
* `fhatRadial`

## Main statements
* `fRadial_zero`
* `fRadial_sqrtTwo`
* `fRadial_two`
* `fhatRadial_zero`
* `fhatRadial_sqrtTwo`

Paper reference: `dim_24.tex`, Section 4 (`sec:proof`), immediately after defining `f`.
-/

namespace SpherePacking.Dim24

/-
Noncomputable because `axisVec` is noncomputable (it uses `EuclideanSpace.single` on `ℝ`).
-/
noncomputable section

open scoped Real FourierTransform
open SchwartzMap Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)
local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

/-- One-variable restriction of `f`, matching the paper's notation `f(r)` (with `r ≥ 0`). -/
public def fRadial (r : ℝ) : ℂ := f (axisVec r)

/--
One-variable restriction of `\hat f`, matching the paper's notation `\hat f(r)` (with `r ≥ 0`).
-/
public def fhatRadial (r : ℝ) : ℂ := (FT f) (axisVec r)

/-- The normalization `fRadial 0 = 1`. -/
public theorem fRadial_zero : fRadial 0 = 1 := by
  simpa [fRadial, axisVec_zero] using (f_zero)

/-- The normalization `fhatRadial 0 = 1`. -/
public theorem fhatRadial_zero : fhatRadial 0 = 1 := by
  simpa [fhatRadial, axisVec_zero] using (fourier_f_zero)

/-- Paper special value: `fRadial (Real.sqrt 2) = 1 / 156`. -/
public theorem fRadial_sqrtTwo : fRadial (Real.sqrt 2) = ((1 : ℂ) / 156) := by
  /- Paper: `f(√2) = 1/156`. -/
  have ha : a (axisVec (Real.sqrt 2)) = (725760 : ℂ) * Complex.I / (π : ℂ) := by
    simpa [aRadial] using (aRadial_sqrtTwo : aRadial (Real.sqrt 2) = _)
  have hb : b (axisVec (Real.sqrt 2)) = 0 := by
    simpa [bRadial] using (bRadial_sqrtTwo : bRadial (Real.sqrt 2) = _)
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  -- Evaluate `f` using the special values for `a` and `b`.
  dsimp [fRadial]
  simp only [Dim24.f, sub_eq_add_neg, add_apply, neg_apply, smul_apply, smul_eq_mul]
  rw [ha, hb]
  field_simp [hpi]; ring_nf; simp

/-- Paper special derivative at `Real.sqrt 2` for `fRadial`. -/
public theorem fRadial_hasDerivAt_sqrtTwo :
    HasDerivAt fRadial (-(146 : ℝ) * Real.sqrt 2 / 4095 : ℂ) (Real.sqrt 2) := by
  /- Paper: `f'(√2) = -146 √2 / 4095`. -/
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have ha' :
      HasDerivAt (fun r : ℝ => a (axisVec r))
        (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) (Real.sqrt 2) := by
    simpa [aRadial] using (aRadial_hasDerivAt_sqrtTwo :
      HasDerivAt aRadial (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) (Real.sqrt 2))
  have hb' :
      HasDerivAt (fun r : ℝ => b (axisVec r))
        ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I) (Real.sqrt 2) := by
    simpa [bRadial] using (bRadial_hasDerivAt_sqrtTwo :
      HasDerivAt bRadial ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I) (Real.sqrt 2))
  have hder0 :
      HasDerivAt
          (fun r : ℝ =>
            (-(π * Complex.I) / (113218560 : ℂ)) * a (axisVec r) -
              (Complex.I / ((262080 : ℂ) * π)) * b (axisVec r))
          ((-(π * Complex.I) / (113218560 : ℂ)) *
              (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) -
            (Complex.I / ((262080 : ℂ) * π)) *
              ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I))
          (Real.sqrt 2) :=
    (ha'.const_mul (-(π * Complex.I) / (113218560 : ℂ))).sub
      (hb'.const_mul (Complex.I / ((262080 : ℂ) * π)))
  have hder :
      HasDerivAt fRadial
          ((-(π * Complex.I) / (113218560 : ℂ)) *
              (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) -
            (Complex.I / ((262080 : ℂ) * π)) *
              ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I))
          (Real.sqrt 2) := by
    -- Unfold `fRadial` and then unfold `f`.
    assumption
  have hconst :
      (-(π * Complex.I) / (113218560 : ℂ)) *
          (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) -
        (Complex.I / ((262080 : ℂ) * π)) *
          ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I)
        =
        (-(146 : ℝ) * Real.sqrt 2 / 4095 : ℂ) := by
    field_simp [hpi]
    norm_num
  -- Replace the derivative constant by the simplified paper value.
  exact HasDerivAt.congr_deriv hder hconst

/-- Paper special value: `fRadial 2 = 0`. -/
public theorem fRadial_two : fRadial 2 = 0 := by
  /- Paper: `f(2)=0`. -/
  have ha : a (axisVec (2 : ℝ)) = 0 := by
    simpa [aRadial] using (aRadial_two : aRadial 2 = 0)
  have hb : b (axisVec (2 : ℝ)) = 0 := by
    simpa [bRadial] using (bRadial_two : bRadial 2 = 0)
  dsimp [fRadial]
  simp [Dim24.f, ha, hb]

/-- Paper special derivative at `2` for `fRadial`. -/
public theorem fRadial_hasDerivAt_two : HasDerivAt fRadial (-(1 : ℝ) / 16380 : ℂ) 2 := by
  /- Paper: `f'(2) = -1/16380` (and this is the unique simple root among the Leech radii ≥ 2). -/
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have ha' :
      HasDerivAt (fun r : ℝ => a (axisVec r)) ((-3456 : ℂ) * Complex.I / (π : ℂ)) 2 := by
    simpa [aRadial] using (aRadial_hasDerivAt_two :
      HasDerivAt aRadial ((-3456 : ℂ) * Complex.I / (π : ℂ)) 2)
  have hb' :
      HasDerivAt (fun r : ℝ => b (axisVec r)) ((-8 : ℝ) * (π : ℝ) * Complex.I) 2 := by
    simpa [bRadial] using (bRadial_hasDerivAt_two :
      HasDerivAt bRadial ((-8 : ℝ) * (π : ℝ) * Complex.I) 2)
  have hder0 :
      HasDerivAt
          (fun r : ℝ =>
            (-(π * Complex.I) / (113218560 : ℂ)) * a (axisVec r) -
              (Complex.I / ((262080 : ℂ) * π)) * b (axisVec r))
          ((-(π * Complex.I) / (113218560 : ℂ)) * ((-3456 : ℂ) * Complex.I / (π : ℂ)) -
            (Complex.I / ((262080 : ℂ) * π)) * ((-8 : ℝ) * (π : ℝ) * Complex.I))
          2 :=
    (ha'.const_mul (-(π * Complex.I) / (113218560 : ℂ))).sub
      (hb'.const_mul (Complex.I / ((262080 : ℂ) * π)))
  have hder :
      HasDerivAt fRadial
          ((-(π * Complex.I) / (113218560 : ℂ)) * ((-3456 : ℂ) * Complex.I / (π : ℂ)) -
            (Complex.I / ((262080 : ℂ) * π)) * ((-8 : ℝ) * (π : ℝ) * Complex.I))
          2 := by
    assumption
  have hconst :
      (-(π * Complex.I) / (113218560 : ℂ)) * ((-3456 : ℂ) * Complex.I / (π : ℂ)) -
          (Complex.I / ((262080 : ℂ) * π)) * ((-8 : ℝ) * (π : ℝ) * Complex.I)
        =
        (-(1 : ℝ) / 16380 : ℂ) := by
    field_simp [hpi]
    norm_num
  exact HasDerivAt.congr_deriv hder hconst

/-- Paper special value: `fhatRadial (Real.sqrt 2) = 1 / 156`. -/
public theorem fhatRadial_sqrtTwo : fhatRadial (Real.sqrt 2) = ((1 : ℂ) / 156) := by
  /- Paper: `\hat f(√2) = 1/156`. -/
  have ha : a (axisVec (Real.sqrt 2)) = (725760 : ℂ) * Complex.I / (π : ℂ) := by
    simpa [aRadial] using (aRadial_sqrtTwo : aRadial (Real.sqrt 2) = _)
  have hb : b (axisVec (Real.sqrt 2)) = 0 := by
    simpa [bRadial] using (bRadial_sqrtTwo : bRadial (Real.sqrt 2) = _)
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  change (FT f) (axisVec (Real.sqrt 2)) = (1 : ℂ) / 156
  rw [fourier_f]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [ha, hb]
  field_simp [hpi]; ring_nf; simp

/-- Paper special derivative at `Real.sqrt 2` for `fhatRadial`. -/
public theorem fhatRadial_hasDerivAt_sqrtTwo :
    HasDerivAt fhatRadial (-(5 : ℝ) * Real.sqrt 2 / 117 : ℂ) (Real.sqrt 2) := by
  /- Paper: `\hat f'(√2) = -5 √2 / 117`. -/
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have ha' :
      HasDerivAt (fun r : ℝ => a (axisVec r))
        (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) (Real.sqrt 2) := by
    simpa [aRadial] using (aRadial_hasDerivAt_sqrtTwo :
      HasDerivAt aRadial (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) (Real.sqrt 2))
  have hb' :
      HasDerivAt (fun r : ℝ => b (axisVec r))
        ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I) (Real.sqrt 2) := by
    simpa [bRadial] using (bRadial_hasDerivAt_sqrtTwo :
      HasDerivAt bRadial ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I) (Real.sqrt 2))
  have hder0 :
      HasDerivAt
          (fun r : ℝ =>
            (-(π * Complex.I) / (113218560 : ℂ)) * a (axisVec r) +
              (Complex.I / ((262080 : ℂ) * π)) * b (axisVec r))
          ((-(π * Complex.I) / (113218560 : ℂ)) *
              (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) +
            (Complex.I / ((262080 : ℂ) * π)) *
              ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I))
          (Real.sqrt 2) :=
    (ha'.const_mul (-(π * Complex.I) / (113218560 : ℂ))).add
      (hb'.const_mul (Complex.I / ((262080 : ℂ) * π)))
  have hder :
      HasDerivAt fhatRadial
          ((-(π * Complex.I) / (113218560 : ℂ)) *
              (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) +
            (Complex.I / ((262080 : ℂ) * π)) *
              ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I))
          (Real.sqrt 2) := by
    change HasDerivAt (fun r : ℝ => (FT f) (axisVec r))
      ((-(π * Complex.I) / (113218560 : ℂ)) *
          (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) +
        (Complex.I / ((262080 : ℂ) * π)) * ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I))
      (Real.sqrt 2)
    rw [fourier_f]
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hder0
  have hconst :
      (-(π * Complex.I) / (113218560 : ℂ)) *
            (-(4437504 : ℝ) * Real.sqrt 2 * Complex.I / (π : ℂ)) +
          (Complex.I / ((262080 : ℂ) * π)) * ((928 : ℝ) * (π : ℝ) * Real.sqrt 2 * Complex.I)
        =
        (-(5 : ℝ) * Real.sqrt 2 / 117 : ℂ) := by
    field_simp [hpi]
    norm_num
  exact HasDerivAt.congr_deriv hder hconst

/-- Paper special value: `fhatRadial 2 = 0`. -/
public theorem fhatRadial_two : fhatRadial 2 = 0 := by
  /- Paper: `\hat f(2)=0` (double root at `r=2`). -/
  have ha : a (axisVec (2 : ℝ)) = 0 := by
    simpa [aRadial] using (aRadial_two : aRadial 2 = 0)
  have hb : b (axisVec (2 : ℝ)) = 0 := by
    simpa [bRadial] using (bRadial_two : bRadial 2 = 0)
  change (FT f) (axisVec (2 : ℝ)) = (0 : ℂ)
  rw [fourier_f]
  simp [ha, hb]

/-- The root of `fhatRadial` at `2` is double, so the derivative vanishes. -/
public theorem fhatRadial_hasDerivAt_two : HasDerivAt fhatRadial 0 2 := by
  /- Paper: the root of `\hat f` at `r=2` is double, hence the derivative vanishes. -/
  have hpi : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have ha' :
      HasDerivAt (fun r : ℝ => a (axisVec r)) ((-3456 : ℂ) * Complex.I / (π : ℂ)) 2 := by
    simpa [aRadial] using (aRadial_hasDerivAt_two :
      HasDerivAt aRadial ((-3456 : ℂ) * Complex.I / (π : ℂ)) 2)
  have hb' :
      HasDerivAt (fun r : ℝ => b (axisVec r)) ((-8 : ℝ) * (π : ℝ) * Complex.I) 2 := by
    simpa [bRadial] using (bRadial_hasDerivAt_two :
      HasDerivAt bRadial ((-8 : ℝ) * (π : ℝ) * Complex.I) 2)
  have hder0 :
      HasDerivAt
          (fun r : ℝ =>
            (-(π * Complex.I) / (113218560 : ℂ)) * a (axisVec r) +
              (Complex.I / ((262080 : ℂ) * π)) * b (axisVec r))
          ((-(π * Complex.I) / (113218560 : ℂ)) * ((-3456 : ℂ) * Complex.I / (π : ℂ)) +
            (Complex.I / ((262080 : ℂ) * π)) * ((-8 : ℝ) * (π : ℝ) * Complex.I))
          2 :=
    (ha'.const_mul (-(π * Complex.I) / (113218560 : ℂ))).add
      (hb'.const_mul (Complex.I / ((262080 : ℂ) * π)))
  have hder :
      HasDerivAt fhatRadial
          ((-(π * Complex.I) / (113218560 : ℂ)) * ((-3456 : ℂ) * Complex.I / (π : ℂ)) +
            (Complex.I / ((262080 : ℂ) * π)) * ((-8 : ℝ) * (π : ℝ) * Complex.I))
          2 := by
    change HasDerivAt (fun r : ℝ => (FT f) (axisVec r))
      ((-(π * Complex.I) / (113218560 : ℂ)) * ((-3456 : ℂ) * Complex.I / (π : ℂ)) +
        (Complex.I / ((262080 : ℂ) * π)) * ((-8 : ℝ) * (π : ℝ) * Complex.I))
      2
    rw [fourier_f]
    simpa [mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hder0
  have hconst :
      (-(π * Complex.I) / (113218560 : ℂ)) * ((-3456 : ℂ) * Complex.I / (π : ℂ)) +
          (Complex.I / ((262080 : ℂ) * π)) * ((-8 : ℝ) * (π : ℝ) * Complex.I)
        = (0 : ℂ) := by
    field_simp [hpi]
    norm_num
  exact HasDerivAt.congr_deriv hder hconst

end

end SpherePacking.Dim24
