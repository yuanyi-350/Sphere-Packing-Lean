module
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
public import SpherePacking.Dim24.MagicFunction.Radial
public import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSRectAnalytic
public import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.MeasureTheory.Integral.ExpDecay
import SpherePacking.ForMathlib.IntervalIntegral


/-!
# Special values for the dim-24 eigenfunction `b`

This file introduces the one-variable restriction `bRadial` and proves basic identities at
`u = 0` used in the special-value computations (in particular, `bProfile 0 = 0`). It also records
the simple parametrisation rewrites needed to relate `ψT'` and `ψI'` on the relevant contour
segments.

Paper reference: `dim_24.tex`, the value list following equation (3.4).

## Main definitions
* `bRadial`

## Main statements
* `bProfile_zero`
-/


open scoped UpperHalfPlane

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

/-
Noncomputable because `axisVec` is noncomputable (it uses `EuclideanSpace.single` on `ℝ`).
-/
noncomputable section

/-- One-variable restriction of `b`, matching the paper's notation `b(r)` (with `r ≥ 0`). -/
@[expose] public def bRadial (r : ℝ) : ℂ := b (axisVec r)

namespace SpecialValuesAux

open MagicFunction.Parametrisations
open RealIntegrals

/-- Evaluate `b` in terms of its one-variable profile `bProfile`. -/
public lemma b_apply (x : ℝ²⁴) : b x = bProfile (‖x‖ ^ 2) := by
  -- `b` is defined via the radial Schwartz bridge.
  simp [Dim24.b]

/-- Express `bRadial` in terms of `bProfile`. -/
public lemma bRadial_eq (r : ℝ) : bRadial r = bProfile (r ^ 2) := by
  simp [bRadial, b_apply, norm_axisVec_sq]

-- Canonical versions of the `ψ`-shift/periodicity lemmas live in:
-- * `SpherePacking.Dim24.ModularForms.Psi.Relations` (for `ψI`), and
-- * `SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions` (for the total extensions).

section Zero

open Complex Set MeasureTheory Filter intervalIntegral
open scoped Interval Topology

lemma J₁'_zero :
    J₁' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z₁' t) := by
  simp [RealIntegrals.J₁']

lemma J₂'_zero :
    J₂' (0 : ℝ) = ∫ t in (0 : ℝ)..1, ψT' (z₂' t) := by
  simp [RealIntegrals.J₂']

lemma J₃'_zero :
    J₃' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z₃' t) := by
  simp [RealIntegrals.J₃']

lemma J₄'_zero :
    J₄' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t) := by
  simp [RealIntegrals.J₄']

lemma J₅'_zero :
    J₅' (0 : ℝ) = (-2 : ℂ) * ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
  simp [RealIntegrals.J₅']

lemma J₆'_zero :
    J₆' (0 : ℝ) = (-2 : ℂ) * ∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) := by
  simp [RealIntegrals.J₆']

/-- Relate the contour parametrisations `z₁'` and `z₅'` by translation by `1`. -/
public lemma z₁'_add_one_eq_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z₁' t + 1 = z₅' t := by
  simp [MagicFunction.Parametrisations.z₁'_eq_of_mem (t := t) ht,
    MagicFunction.Parametrisations.z₅'_eq_of_mem (t := t) ht, add_left_comm, add_comm]

/-- Rewrite `ψT'` along the `z₁'` segment as `ψI'` along the `z₅'` segment. -/
public lemma ψT'_z₁'_eq_ψI'_z₅' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₁' t) = ψI' (z₅' t) := by
  simpa [z₁'_add_one_eq_z₅' (t := t) ht] using
    (SpherePacking.Dim24.ψT'_eq_ψI'_add_one (z := z₁' t))

lemma J₁'_J₃'_J₅'_zero_sum : J₁' (0 : ℝ) + J₃' 0 + J₅' 0 = 0 := by
  have hJ1 :
      J₁' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    rw [J₁'_zero]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    simp [ψT'_z₁'_eq_ψI'_z₅' (t := t) htIcc]
  have hJ3 :
      J₃' (0 : ℝ) = ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := by
    rw [J₃'_zero]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    simp
      [SpherePacking.Dim24.Schwartz.J3Smooth.ψT'_z₃'_eq_ψI'_z₅' (t := t) htIcc]
  have hJ5 :
      J₅' (0 : ℝ) = (-2 : ℂ) * ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) := J₅'_zero
  -- Finish by linearity.
  simp [hJ1, hJ3, hJ5]
  ring

-- (The remaining contour-identity `J₂'(0) + J₄'(0) + J₆'(0) = 0` is proved below.)

end Zero

section Zero

open Complex Set MeasureTheory Filter intervalIntegral
open UpperHalfPlane ModularGroup MatrixGroups ModularForm SlashAction
open scoped Interval Topology Manifold

/-- Rewrite `ψT'` along `z₂'` as `ψI'` on the horizontal line `Im z = 1`. -/
public lemma ψT'_z₂'_eq_ψI'_add_one (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) := by
  have hz2 : z₂' t + 1 = (t : ℂ) + Complex.I := by
    simp [MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t) ht, add_left_comm, add_comm]
  simpa [hz2] using (SpherePacking.Dim24.ψT'_eq_ψI'_add_one (z := z₂' t))

/-- Express `J₂'(0) + J₄'(0)` as a single horizontal integral involving `ψS'`. -/
public lemma J₂'_J₄_as_ψS_horizontal :
    J₂' (0 : ℝ) + J₄' 0 = ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
  -- Rewrite `J₂' 0` using `ψT'(z) = ψI'(z+1)` on the segment `Im z = 1`.
  have hJ2 : J₂' (0 : ℝ) = ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) := by
    rw [J₂'_zero]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    simp [ψT'_z₂'_eq_ψI'_add_one (t := t) htIcc]
  -- Rewrite `J₄' 0` as the negatively oriented integral over `t ∈ [0,1]` along `Im z = 1`.
  have hJ4 : J₄' (0 : ℝ) = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
    rw [J₄'_zero]
    -- First, rewrite the parametrisation `z₄' t = (1 - t) + I`.
    have hEq :
        (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t)) =
          ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I) := by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      have htIcc : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
      have hz4 : z₄' t = (1 - (t : ℂ)) + Complex.I := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          z₄'_eq_of_mem (t := t) htIcc
      simp [hz4]
    -- Now substitute `u = 1 - t` in the integral.
    let f : ℝ → ℂ := fun u => ψT' ((u : ℂ) + Complex.I)
    have hneg :
        (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I)) =
          -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
      simpa [f] using
        (SpherePacking.ForMathlib.intervalIntegral_neg_one_mul_comp_one_sub_eq_neg (f := f))
    calc
      (∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' (z₄' t))
          = ∫ t in (0 : ℝ)..1, (-1 : ℂ) * ψT' ((1 - t : ℂ) + Complex.I) := hEq
      _ = -∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := hneg
  -- Use `ψS + ψT = ψI` pointwise on `Im z = 1`.
  have hrel :
      ∀ t : ℝ, ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I) =
        ψS' ((t : ℂ) + Complex.I) := by
    intro t
    have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
    have h := congrArg (fun F : ℍ → ℂ => F (UpperHalfPlane.mk ((t : ℂ) + Complex.I) hz))
      ψS_add_ψT_eq_ψI
    have h' :
        ψI' ((t : ℂ) + Complex.I) =
          ψS' ((t : ℂ) + Complex.I) + ψT' ((t : ℂ) + Complex.I) := by
      simpa [ψI', ψS', ψT', hz] using h.symm
    -- Rearrange `ψI' = ψS' + ψT'` into `ψI' - ψT' = ψS'`.
    exact Eq.symm (eq_sub_of_add_eq (id (Eq.symm h')))
  -- Integrate the pointwise identity.
  have continuous_ψI'_add_I : Continuous fun t : ℝ => ψI' ((t : ℂ) + Complex.I) := by
    simpa using SpherePacking.Dim24.PsiRewrites.continuous_ψI'_add_I
  have continuous_ψT'_add_I : Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I) := by
    simpa using SpherePacking.Dim24.PsiRewrites.continuous_ψT'_add_I
  have hInt :
      (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I)) -
          ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) =
      ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
    have hSub :
        ∫ t in (0 : ℝ)..1, (ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I)) =
          (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I)) -
            ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) := by
      simpa using
        (intervalIntegral.integral_sub (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun t : ℝ => ψI' ((t : ℂ) + Complex.I))
          (g := fun t : ℝ => ψT' ((t : ℂ) + Complex.I))
          (continuous_ψI'_add_I.intervalIntegrable
            (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ)))
          (continuous_ψT'_add_I.intervalIntegrable
            (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))))
    have hCongr :
        (∫ t in (0 : ℝ)..1, (ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I))) =
          ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) := by
      refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
      intro t ht
      simp [hrel t]
    simpa [hSub] using hCongr
  -- Finish.
  simpa [hJ2, hJ4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hInt

end Zero

section ZeroContour

open Set Complex Filter MeasureTheory UpperHalfPlane intervalIntegral
open scoped Interval Topology UpperHalfPlane Manifold

-- Canonical `ψS'` tail/shift/integrability lemmas live in `Dim24.PsiSPrelims`.
open PsiSPrelims

lemma J₂'_J₄'_J₆'_zero_sum : J₂' (0 : ℝ) + J₄' 0 + J₆' 0 = 0 := by
  -- Replace `J₂'(0)+J₄'(0)` by the horizontal `ψS'` integral at height `1`.
  rw [J₂'_J₄_as_ψS_horizontal]
  have hcont : ContinuousOn ψS' (Set.uIcc (0 : ℝ) 1 ×ℂ (Ici (1 : ℝ))) := continuousOn_ψS'_rect
  have hdiff :
      ∀ x ∈ ((Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Ioi (1 : ℝ))) \ (∅ : Set ℂ),
        DifferentiableAt ℂ ψS' x := by
    intro z hz
    have hzIm1 : z.im ∈ Ioi (1 : ℝ) := (mem_reProdIm.1 (by simpa using hz.1)).2
    have hzIm : 0 < z.im := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) (le_of_lt hzIm1)
    exact differentiableAt_ψS'_of_im_pos z hzIm
  have hint₁ :
      MeasureTheory.IntegrableOn (fun t : ℝ => ψS' ((0 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
        MeasureTheory.volume := by
    simpa using integrableOn_ψS'_vertical_left
  have hint₂ :
      MeasureTheory.IntegrableOn (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) (Ioi (1 : ℝ))
        MeasureTheory.volume := integrableOn_ψS'_vertical_right
  have hrect :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
          (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) -
            (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((0 : ℂ) + t * Complex.I)) = 0 := by
    simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1), max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)] using
      (integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ))
        (f := ψS')
        (x₁ := (0 : ℝ))
        (x₂ := (1 : ℝ))
        hcont
        (s := (∅ : Set ℂ))
        (by simp)
        hdiff
        hint₁
        hint₂
        htendsto_ψS')
  have hright :
      (∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) =
        -∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I) := by
    have hEq :
        (fun t : ℝ => ψS' ((1 : ℂ) + t * Complex.I)) =ᵐ[MeasureTheory.volume.restrict (Ioi (1 : ℝ))]
          fun t : ℝ => -ψS' (t * Complex.I) := by
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by simp : (0 : ℝ) < 1) (le_of_lt ht)
      simp [ψS'_add_one t ht0]
    have hEqInt :
        (∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((1 : ℂ) + t * Complex.I)) =
          ∫ (t : ℝ) in Ioi (1 : ℝ), -ψS' (t * Complex.I) := by
      simpa using (MeasureTheory.integral_congr_ae hEq)
    simpa [MeasureTheory.integral_neg] using hEqInt
  have hhor :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) -
          (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) = 0 := by
    have h' :
        (∫ (x : ℝ) in (0 : ℝ)..1, ψS' (x + (1 : ℝ) * Complex.I)) +
            (Complex.I • (-∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I))) -
              (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' ((0 : ℂ) + t * Complex.I)) = 0 := by
      simpa [hright] using hrect
    simpa [two_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, smul_neg] using h'
  have hJ6 :
      J₆' (0 : ℝ) =
        (-2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) := by
    rw [J₆'_zero]
    have hIci :
        (∫ t in Set.Ici (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t)) =
          ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t) := by
      exact integral_Ici_eq_integral_Ioi
    have hparam :
        (∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (z₆' t)) =
          ∫ t in Set.Ioi (1 : ℝ), (Complex.I : ℂ) * ψS' (t * Complex.I) := by
      refine MeasureTheory.integral_congr_ae ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
      intro t ht
      have ht' : t ∈ Set.Ici (1 : ℝ) := le_of_lt (by simpa [Set.mem_Ioi] using ht)
      simp [MagicFunction.Parametrisations.z₆'_eq_of_mem (t := t) ht', mul_comm]
    simpa [hIci, hparam, smul_eq_mul] using
      (MeasureTheory.integral_const_mul (μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
        (r := (Complex.I : ℂ)) (f := fun t : ℝ => ψS' (t * Complex.I)))
  have htail :
      (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) + J₆' (0 : ℝ) = 0 := by
    have : (∫ (x : ℝ) in (0 : ℝ)..1, ψS' ((x : ℂ) + Complex.I)) =
        (2 : ℂ) * (Complex.I • ∫ (t : ℝ) in Ioi (1 : ℝ), ψS' (t * Complex.I)) := by
      simpa [sub_eq_zero] using hhor
    simp [this, hJ6]
  simpa [add_assoc] using htail

/-- Special value: `bProfile 0 = 0`. -/
public lemma bProfile_zero : bProfile (0 : ℝ) = 0 := by
  -- Assemble `b'(0)` from the two cancellations.
  have h135 : J₁' (0 : ℝ) + J₃' 0 + J₅' 0 = 0 := J₁'_J₃'_J₅'_zero_sum
  have h246 : J₂' (0 : ℝ) + J₄' 0 + J₆' 0 = 0 := J₂'_J₄'_J₆'_zero_sum
  -- Unfold the one-variable profile.
  dsimp [bProfile, RealIntegrals.b']
  calc
    J₁' (0 : ℝ) + J₂' 0 + J₃' 0 + J₄' 0 + J₅' 0 + J₆' 0 =
        (J₁' (0 : ℝ) + J₃' 0 + J₅' 0) + (J₂' 0 + J₄' 0 + J₆' 0) := by ac_rfl
    _ = 0 := by simp [h135, h246]

end ZeroContour

-- (We introduce a periodicity lemma for the exponential when needed in the special-value proofs.)


end SpecialValuesAux

end

end SpherePacking.Dim24
