module
public import SpherePacking.Dim24.MagicFunction.B.Defs.Eigenfunction
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Final
public import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Basic
import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Derivatives.Rectangle
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSRectIdentity
import SpherePacking.Dim24.MagicFunction.B.Defs.J4Smooth
import SpherePacking.Dim24.ModularForms.Psi.Relations
import SpherePacking.Dim24.MagicFunction.B.Defs.PsiSPrelims
public import SpherePacking.ForMathlib.CauchyGoursat.OpenRectangular
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.MeasureTheory.Integral.ExpDecay


/-!
# Zeros of the magic function `b`

This file records the zero set of the dimension-24 magic function `b`, and the corresponding
vanishing and double-vanishing statements for the one-variable profile `bProfile` and the radial
function `bRadial`.

## Main statements
* `ZerosAuxB.bProfile_two_mul_nat`
* `ZerosAuxB.bProfile_hasDerivAt_zero_two_mul_nat_of_two_lt`
* `b_zero_of_norm_sq_eq_two_mul`
* `bRadial_hasDerivAt_zero_of_two_lt`

-/

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace ZerosAuxB

open scoped Real
open scoped UpperHalfPlane
open SpecialValuesAux
open MagicFunction.Parametrisations
open RealIntegrals
open Complex Set MeasureTheory Filter intervalIntegral
open scoped Interval Topology

private lemma mem_Icc01_of_mem_uIcc01 {t : ℝ} (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
    t ∈ Icc (0 : ℝ) 1 := by
  simpa [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht


-- Canonical versions of the `ψ`-shift/periodicity lemmas live in:
-- * `SpherePacking.Dim24.ModularForms.Psi.Relations` (for `ψI`), and
-- * `SpherePacking.Dim24.MagicFunction.B.Defs.PsiExtensions` (for the total extensions).

/-! #### The `J₁'+J₃'+J₅'` cancellation at even integers -/

-- This cancellation lemma is proved (once) in the `SpecialValuesAux` development:
-- `SpecialValuesAux.J₁'_J₃'_J₅'_zero_sum_of`.

/-!
The `J₂'+J₄'+J₆'` cancellation is the main complex-analytic step; we reuse the same open-rectangle
deformation argument as in `SpecialValues.lean`, but specialize later to `u = 2k`.
-/

/-! #### Setup for the open-rectangle deformation -/

open UpperHalfPlane ModularGroup MatrixGroups ModularForm SlashAction
open scoped Manifold

/-! #### Decay of `ψS'` on vertical strips -/

/-! #### The `J₂'+J₄'+J₆'` cancellation at even integers -/

-- This cancellation lemma is proved (once) in the `SpecialValuesAux` development:
-- `SpecialValuesAux.J₂'_J₄'_J₆'_zero_sum_of`.

/-- The profile `bProfile` vanishes at every even integer `u = 2k`. -/
public lemma bProfile_two_mul_nat (k : ℕ) : bProfile ((2 : ℝ) * k) = 0 := by
  refine SpecialValuesAux.bProfile_eq_zero_of (u := (2 : ℝ) * k) (hu := ?_) (hu0 := ?_)
  · simpa using expU_two_mul_nat_one (k := k)
  · positivity

/-!
### Double zeros for `k > 2`

We show that `bProfile` has a double zero at `u = 2k` for `k > 2`, hence `bRadial` has a double
zero at `r = √(2k)`.
-/
-- This double-zero lemma is proved (once) in the `SpecialValuesAux` development:
-- `SpecialValuesAux.J₁'_J₃'_J₅'_hasDerivAt_zero_of`.

lemma ψI'_sub_ψT'_eq_ψS'_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ψI' z - ψT' z = ψS' z := by
  have hz' : 0 < z.im := hz
  -- Use `ψS + ψT = ψI` on the upper half-plane.
  have hsum :
      ψS (UpperHalfPlane.mk z hz') + ψT (UpperHalfPlane.mk z hz') =
        ψI (UpperHalfPlane.mk z hz') :=
    congrArg (fun F : ℍ → ℂ => F (UpperHalfPlane.mk z hz')) ψS_add_ψT_eq_ψI
  -- Unfold the total extensions (all are in the `if` positive branch).
  have hsum' : ψS' z + ψT' z = ψI' z := by
    simpa [ψI', ψS', ψT', hz', add_comm, add_left_comm, add_assoc] using hsum
  -- Rearrange.
  exact Eq.symm (eq_sub_of_add_eq hsum')

lemma ψI_rect_integral_eq_vertical_ψS (u : ℝ) (hu : expU u 1 = 1) (hu4 : 4 < u) :
    (∫ x in (0 : ℝ)..1, ψI' ((x : ℂ) + Complex.I) * expU u ((x : ℂ) + Complex.I)) =
      (Complex.I : ℂ) • ∫ t in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I) :=
by
  -- Deform the contour for `f(z) = ψI' z * expU u z` between `x=0` and `x=1` above `im z = 1`.
  let f : ℂ → ℂ := fun z : ℂ => ψI' z * expU u z
  -- `f` is holomorphic on `im z > 0` (since `ψI` is holomorphic on `ℍ` and `expU` is entire).
  have hdiffOn :
      DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := by
    have hψI' : DifferentiableOn ℂ ψI' {z : ℂ | 0 < z.im} := by
      refine differentiableOn_ψI_ofComplex.congr ?_
      intro z hz
      have hz' : 0 < z.im := hz
      simp [ψI', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']
    have hExp : DifferentiableOn ℂ (expU u) {z : ℂ | 0 < z.im} := by
      exact (by
        unfold expU
        fun_prop : Differentiable ℂ (expU u)).differentiableOn
    simpa [f] using hψI'.mul hExp
  -- Continuity on the closed rectangle follows from differentiability on `im>0`.
  have hcont : ContinuousOn f ([[0, 1]] ×ℂ (Set.Ici (1 : ℝ))) := by
    refine hdiffOn.continuousOn.mono ?_
    intro z hz
    have : (1 : ℝ) ≤ z.im := by
      simpa [mem_reProdIm] using hz.2
    exact lt_of_lt_of_le (by norm_num) this
  -- Exponential growth bound for `ψI` at infinity via the `Δ` bound.
  have exists_invΔ :
      ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖(Δ z)⁻¹‖ ≤ C * Real.exp (2 * Real.pi * z.im) := by
    -- Extract an inverse-`Δ` bound from `Delta_isTheta_rexp.2`.
    have hO :
        (fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) =O[atImInfty] (Delta : ℍ → ℂ) :=
      Delta_isTheta_rexp.2
    rcases (Asymptotics.isBigO_iff.1 hO) with ⟨C, hC⟩
    let C' : ℝ := max C 1
    have hC'pos : 0 < C' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hC' :
        ∀ᶠ z in atImInfty, ‖Real.exp (-2 * Real.pi * z.im)‖ ≤ C' * ‖(Delta z : ℂ)‖ := by
      filter_upwards [hC] with z hz
      have hle : C ≤ C' := le_max_left _ _
      have hn : 0 ≤ ‖(Delta z : ℂ)‖ := norm_nonneg _
      have hle' : C * ‖(Delta z : ℂ)‖ ≤ C' * ‖(Delta z : ℂ)‖ := mul_le_mul_of_nonneg_right hle hn
      exact hz.trans hle'
    rcases (Filter.eventually_atImInfty.1 hC') with ⟨A, hA⟩
    refine ⟨C', max A 1, hC'pos, ?_⟩
    intro z hz
    have hAz : A ≤ z.im := le_trans (le_max_left _ _) hz
    have hineq := hA z hAz
    have hΔ : (Delta z : ℂ) = (Δ z : ℂ) := by simp [Delta_apply]
    have hexp : ‖Real.exp (-2 * Real.pi * z.im)‖ = Real.exp (-2 * Real.pi * z.im) := by
      simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
    have hΔne : (Δ z : ℂ) ≠ 0 := by
      simpa [Delta_apply] using (Δ_ne_zero z)
    have hnormpos : 0 < ‖(Δ z : ℂ)‖ := norm_pos_iff.2 hΔne
    have hbase : Real.exp (-2 * Real.pi * z.im) ≤ C' * ‖(Δ z : ℂ)‖ := by
      simpa [hexp, hΔ] using hineq
    have hone :
        (1 : ℝ) ≤ (C' * ‖(Δ z : ℂ)‖) * Real.exp (2 * Real.pi * z.im) := by
      have hbase' : Real.exp (-(2 * Real.pi * z.im)) ≤ C' * ‖(Δ z : ℂ)‖ := by
        have hexp : Real.exp (-(2 * Real.pi * z.im)) = Real.exp (-2 * Real.pi * z.im) := by
          congr 1
          ring
        rw [hexp]
        exact hbase
      have hmul :
          Real.exp (2 * Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im)) ≤
            Real.exp (2 * Real.pi * z.im) * (C' * ‖(Δ z : ℂ)‖) := by
        exact mul_le_mul_of_nonneg_left hbase' (by positivity : 0 ≤ Real.exp (2 * Real.pi * z.im))
      have hexp' : Real.exp (2 * Real.pi * z.im) * Real.exp (-(2 * Real.pi * z.im)) = 1 := by
        have hsum : (2 * Real.pi * z.im) + (-(2 * Real.pi * z.im)) = 0 := by ring
        simpa [hsum] using (Real.exp_add (2 * Real.pi * z.im) (-(2 * Real.pi * z.im))).symm
      linarith
    have hinv : (1 : ℝ) / ‖(Δ z : ℂ)‖ ≤ C' * Real.exp (2 * Real.pi * z.im) := by
      have hmul : (1 : ℝ) ≤ (C' * Real.exp (2 * Real.pi * z.im)) * ‖(Δ z : ℂ)‖ := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hone
      exact (div_le_iff₀ hnormpos).2 hmul
    simpa [Delta_apply, norm_inv, one_div] using hinv
  have exists_ψI_bound :
      ∃ C A : ℝ, 0 < C ∧ ∀ z : ℍ, A ≤ z.im → ‖ψI z‖ ≤ C * Real.exp (4 * Real.pi * z.im) := by
    rcases exists_invΔ with ⟨CΔ, AΔ, hCΔ, hInvΔ⟩
    let N : ℍ → ℂ :=
      fun z : ℍ =>
        7 * (H₄ z) ^ (5 : ℕ) * (H₂ z) ^ (2 : ℕ) +
          7 * (H₄ z) ^ (6 : ℕ) * (H₂ z) +
            2 * (H₄ z) ^ (7 : ℕ)
    have hNlim : Tendsto N atImInfty (𝓝 (2 : ℂ)) := by
      have hH2 : Tendsto H₂ atImInfty (𝓝 (0 : ℂ)) := H₂_tendsto_atImInfty
      have hH4 : Tendsto H₄ atImInfty (𝓝 (1 : ℂ)) := H₄_tendsto_atImInfty
      have h1 : Tendsto (fun z : ℍ => (H₄ z) ^ (5 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
        simpa using (hH4.pow 5)
      have h2 : Tendsto (fun z : ℍ => (H₂ z) ^ (2 : ℕ)) atImInfty (𝓝 (0 : ℂ)) := by
        simpa using (hH2.pow 2)
      have h3 : Tendsto (fun z : ℍ => (H₄ z) ^ (6 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
        simpa using (hH4.pow 6)
      have h4 : Tendsto (fun z : ℍ => (H₄ z) ^ (7 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
        simpa using (hH4.pow 7)
      have hterm1 :
          Tendsto (fun z : ℍ => (7 : ℂ) * (H₄ z) ^ 5 * (H₂ z) ^ 2) atImInfty (𝓝 (0 : ℂ)) := by
        have : Tendsto (fun z : ℍ => (H₄ z) ^ 5 * (H₂ z) ^ 2) atImInfty (𝓝 ((1 : ℂ) * (0 : ℂ))) :=
          h1.mul h2
        simpa [mul_assoc] using (tendsto_const_nhds.mul this)
      have hterm2 :
          Tendsto (fun z : ℍ => (7 : ℂ) * (H₄ z) ^ 6 * (H₂ z)) atImInfty (𝓝 (0 : ℂ)) := by
        have : Tendsto (fun z : ℍ => (H₄ z) ^ 6 * (H₂ z)) atImInfty (𝓝 ((1 : ℂ) * (0 : ℂ))) :=
          h3.mul hH2
        simpa [mul_assoc] using (tendsto_const_nhds.mul this)
      have hterm3 :
          Tendsto (fun z : ℍ => (2 : ℂ) * (H₄ z) ^ 7) atImInfty (𝓝 (2 : ℂ)) := by
        simpa [mul_assoc] using (tendsto_const_nhds.mul h4)
      have : Tendsto N atImInfty (𝓝 ((0 : ℂ) + (0 : ℂ) + (2 : ℂ))) := by
        simpa [N, add_assoc] using (hterm1.add (hterm2.add hterm3))
      simpa using this
    have hNbdd : ∀ᶠ z in atImInfty, ‖N z‖ ≤ 3 := by
      -- `N z → 2`, so eventually `‖N z - 2‖ < 1`, hence `‖N z‖ ≤ 3`.
      have hNear : ∀ᶠ z in atImInfty, N z ∈ Metric.ball (2 : ℂ) 1 := by
        have : Metric.ball (2 : ℂ) 1 ∈ 𝓝 (2 : ℂ) :=
          Metric.ball_mem_nhds (2 : ℂ) (by norm_num)
        exact hNlim.eventually this
      filter_upwards [hNear] with z hz
      have hz' : ‖N z - (2 : ℂ)‖ < 1 := by
        simpa [Metric.ball, Complex.dist_eq] using hz
      have : ‖N z‖ ≤ ‖(2 : ℂ)‖ + ‖N z - (2 : ℂ)‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (norm_add_le (2 : ℂ) (N z - (2 : ℂ)))
      have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      linarith
    rcases (Filter.eventually_atImInfty).1 hNbdd with ⟨A0, hA0⟩
    let A : ℝ := max AΔ A0
    let C : ℝ := 3 * (CΔ ^ 2)
    have hC : 0 < C := by
      have : (0 : ℝ) < (3 : ℝ) := by norm_num
      exact mul_pos this (pow_pos hCΔ 2)
    refine ⟨C, A, hC, ?_⟩
    intro z hz
    have hzΔ : AΔ ≤ z.im := le_trans (le_max_left _ _) hz
    have hz0 : A0 ≤ z.im := le_trans (le_max_right _ _) hz
    have hN : ‖N z‖ ≤ 3 := hA0 z hz0
    have hInv : ‖(Δ z)⁻¹‖ ≤ CΔ * Real.exp (2 * Real.pi * z.im) := hInvΔ z hzΔ
    have hInv2 : ‖(Δ z)⁻¹‖ ^ 2 ≤ (CΔ * Real.exp (2 * Real.pi * z.im)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hInv 2
    have hInv2' :
        ‖(Δ z)⁻¹‖ ^ 2 ≤ (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
      -- expand the square
      have : (CΔ * Real.exp (2 * Real.pi * z.im)) ^ 2 =
          (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by
        -- Reduce to a ring identity by treating `exp(2πy)` as an indeterminate.
        set t : ℝ := Real.exp (2 * Real.pi * z.im)
        have ht : t * t = Real.exp (4 * Real.pi * z.im) := by
          dsimp [t]
          have hsum : (2 * Real.pi * z.im) + (2 * Real.pi * z.im) = 4 * Real.pi * z.im := by ring
          simpa [hsum] using (Real.exp_add (2 * Real.pi * z.im) (2 * Real.pi * z.im)).symm
        calc
          (CΔ * Real.exp (2 * Real.pi * z.im)) ^ 2 = (CΔ * t) ^ 2 := by simp [t]
          _ = (CΔ ^ 2) * (t * t) := by
                simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
          _ = (CΔ ^ 2) * Real.exp (4 * Real.pi * z.im) := by simp [ht]
      exact hInv2.trans_eq this
    have hψI :
        ψI z = (N z) / (Δ z) ^ (2 : ℕ) := by
      simpa [N] using (SpherePacking.Dim24.ψI_eq_H z)
    have hψI' :
        ‖ψI z‖ ≤ ‖N z‖ * ‖(Δ z)⁻¹‖ ^ 2 := by
      -- `‖a / b^2‖ = ‖a‖ * ‖(b⁻¹)^2‖`.
      have hΔ0 : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
      -- rewrite and bound
      rw [hψI]
      simp [div_eq_mul_inv, norm_pow, norm_inv]
    nlinarith
  -- Integrability on vertical lines `Re z = a` (the bounds depend only on `Im z`).
  have hInt_vertical (a : ℝ) :
      MeasureTheory.IntegrableOn (fun t : ℝ => f ((a : ℂ) + t * Complex.I)) (Set.Ioi (1 : ℝ))
        MeasureTheory.volume := by
    rcases exists_ψI_bound with ⟨Cψ, Aψ, -, hψbd⟩
    let A : ℝ := max Aψ 1
    have hA1 : (1 : ℝ) ≤ A := le_max_right _ _
    have hAAψ : Aψ ≤ A := le_max_left _ _
    let b : ℝ := Real.pi * (u - 4)
    have hb : 0 < b := by positivity [Real.pi_pos, sub_pos.2 hu4]
    have hcont_f : ContinuousOn f {z : ℂ | 0 < z.im} := hdiffOn.continuousOn
    have hcont_map : Continuous fun t : ℝ => (a : ℂ) + t * Complex.I := by fun_prop
    have hmap_Icc :
        Set.MapsTo (fun t : ℝ => (a : ℂ) + t * Complex.I) (Set.Icc (1 : ℝ) A)
          {z : ℂ | 0 < z.im} := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
      simpa [Complex.add_im] using ht0
    have hIoc :
        MeasureTheory.IntegrableOn (fun t : ℝ => f ((a : ℂ) + t * Complex.I)) (Set.Ioc (1 : ℝ) A)
          MeasureTheory.volume := by
      have hcont_Icc :
          ContinuousOn (fun t : ℝ => f ((a : ℂ) + t * Complex.I)) (Set.Icc (1 : ℝ) A) :=
        hcont_f.comp hcont_map.continuousOn hmap_Icc
      have hIcc :
          MeasureTheory.IntegrableOn (fun t : ℝ => f ((a : ℂ) + t * Complex.I)) (Set.Icc (1 : ℝ) A)
            MeasureTheory.volume :=
        hcont_Icc.integrableOn_compact (μ := MeasureTheory.volume) isCompact_Icc
      exact hIcc.mono_set Set.Ioc_subset_Icc_self
    have hIoi :
        MeasureTheory.IntegrableOn (fun t : ℝ => f ((a : ℂ) + t * Complex.I)) (Set.Ioi A)
          MeasureTheory.volume := by
      have hgi :
          MeasureTheory.IntegrableOn (fun t : ℝ => (Cψ : ℝ) * Real.exp (-b * t)) (Set.Ioi A)
            MeasureTheory.volume := by
        simpa [mul_assoc] using ((exp_neg_integrableOn_Ioi A hb).const_mul Cψ)
      have hmeas :
          MeasureTheory.AEStronglyMeasurable (fun t : ℝ => f ((a : ℂ) + t * Complex.I))
            (MeasureTheory.volume.restrict (Set.Ioi A)) := by
        have hmap_Ioi :
            Set.MapsTo (fun t : ℝ => (a : ℂ) + t * Complex.I) (Set.Ioi A) {z : ℂ | 0 < z.im} := by
          intro t ht
          have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_trans hA1 (le_of_lt ht))
          simpa [Complex.add_im] using ht0
        have hcont_Ioi :
            ContinuousOn (fun t : ℝ => f ((a : ℂ) + t * Complex.I)) (Set.Ioi A) :=
          hcont_f.comp hcont_map.continuousOn hmap_Ioi
        exact hcont_Ioi.aestronglyMeasurable measurableSet_Ioi
      have hdom :
          ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi A)),
            ‖f ((a : ℂ) + t * Complex.I)‖ ≤ (Cψ : ℝ) * Real.exp (-b * t) := by
        refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_
        intro t ht
        have htA : A ≤ t := le_of_lt ht
        have ht1 : 1 ≤ t := le_trans hA1 htA
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht1
        have htim : 0 < ((a : ℂ) + t * Complex.I).im := by simpa [Complex.add_im] using ht0
        have hψ :
            ‖ψI' ((a : ℂ) + t * Complex.I)‖ ≤ Cψ * Real.exp (4 * Real.pi * t) := by
          have htAψ : Aψ ≤ t := le_trans hAAψ htA
          let zH : ℍ := ⟨(a : ℂ) + t * Complex.I, htim⟩
          have hzHim : zH.im = t := by simp [UpperHalfPlane.im, zH, Complex.add_im]
          have htAψ' : Aψ ≤ zH.im := by simpa [hzHim] using htAψ
          simpa [ψI', zH, hzHim, ht0] using (hψbd zH htAψ')
        have hexp : ‖expU u ((a : ℂ) + t * Complex.I)‖ = Real.exp (-Real.pi * u * t) := by
          simp [expU, Complex.norm_exp, mul_left_comm, mul_comm]
        have hmul :
            ‖f ((a : ℂ) + t * Complex.I)‖ ≤
              (Cψ * Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t) := by
          have hnexp : 0 ≤ ‖expU u ((a : ℂ) + t * Complex.I)‖ := norm_nonneg _
          have hmul' :
              ‖ψI' ((a : ℂ) + t * Complex.I)‖ * ‖expU u ((a : ℂ) + t * Complex.I)‖ ≤
                (Cψ * Real.exp (4 * Real.pi * t)) * ‖expU u ((a : ℂ) + t * Complex.I)‖ :=
            mul_le_mul_of_nonneg_right hψ hnexp
          have hmul'' :
              ‖ψI' ((a : ℂ) + t * Complex.I)‖ * ‖expU u ((a : ℂ) + t * Complex.I)‖ ≤
                (Cψ * Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t) := by
            simpa [hexp] using hmul'
          simpa [f, norm_mul, mul_assoc, mul_left_comm, mul_comm] using hmul''
        have hEq :
            (Cψ * Real.exp (4 * Real.pi * t)) * Real.exp (-Real.pi * u * t) =
              (Cψ : ℝ) * Real.exp (-b * t) := by
          have hprod :
              Real.exp (4 * Real.pi * t) * Real.exp (-Real.pi * u * t) =
                Real.exp ((4 * Real.pi * t) + (-Real.pi * u * t)) := by
            simpa using (Real.exp_add (4 * Real.pi * t) (-Real.pi * u * t)).symm
          grind only
        exact le_trans hmul (le_of_eq hEq)
      have hgi' :
          MeasureTheory.Integrable (fun t : ℝ => (Cψ : ℝ) * Real.exp (-b * t))
            (MeasureTheory.volume.restrict (Set.Ioi A)) := by
        simpa [MeasureTheory.IntegrableOn] using hgi
      have hf' :
          MeasureTheory.Integrable (fun t : ℝ => f ((a : ℂ) + t * Complex.I))
            (MeasureTheory.volume.restrict (Set.Ioi A)) :=
        MeasureTheory.Integrable.mono'
          (μ := MeasureTheory.volume.restrict (Set.Ioi A)) hgi' hmeas hdom
      simpa [MeasureTheory.IntegrableOn] using hf'
    have hunion :
        MeasureTheory.IntegrableOn (fun t : ℝ => f ((a : ℂ) + t * Complex.I))
          (Set.Ioc (1 : ℝ) A ∪ Set.Ioi A)
          MeasureTheory.volume :=
      hIoc.union hIoi
    simpa [Set.Ioc_union_Ioi_eq_Ioi hA1] using hunion
  have hInt_left :
      MeasureTheory.IntegrableOn (fun t : ℝ => f (0 + t * Complex.I)) (Set.Ioi (1 : ℝ))
        MeasureTheory.volume := by
    simpa using (hInt_vertical (a := (0 : ℝ)))
  have hInt_right :
      MeasureTheory.IntegrableOn (fun t : ℝ => f (1 + t * Complex.I)) (Set.Ioi (1 : ℝ))
        MeasureTheory.volume := by
    simpa using (hInt_vertical (a := (1 : ℝ)))
  -- Exponential decay of `f` as `im z → ∞` (using the same bound).
  have htendsto :
      ∀ ε > 0, ∃ M : ℝ, ∀ z : ℂ, M ≤ z.im → ‖f z‖ < ε := by
    rcases exists_ψI_bound with ⟨Cψ, Aψ, hCψ, hψbd⟩
    let b : ℝ := Real.pi * (u - 4)
    have hb : 0 < b := by positivity [Real.pi_pos, sub_pos.2 hu4]
    have hlim : Tendsto (fun y : ℝ => (Cψ : ℝ) * Real.exp (-b * y)) atTop (𝓝 (0 : ℝ)) := by
      have : Tendsto (fun y : ℝ => Real.exp (-b * y)) atTop (𝓝 (0 : ℝ)) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (by simpa using (neg_neg_of_pos hb)))
      simpa [mul_zero] using (tendsto_const_nhds.mul this)
    intro ε hε
    have hεevent : ∀ᶠ y : ℝ in atTop, dist ((Cψ : ℝ) * Real.exp (-b * y)) 0 < ε :=
      (Metric.tendsto_nhds.1 hlim ε hε)
    rcases (Filter.eventually_atTop.1 hεevent) with ⟨M0, hM0⟩
    refine ⟨max Aψ (max M0 1), ?_⟩
    intro z hz
    have hzA : Aψ ≤ z.im := le_trans (le_max_left Aψ (max M0 1)) hz
    have hzM : M0 ≤ z.im :=
      le_trans (le_trans (le_max_left M0 1) (le_max_right Aψ (max M0 1))) hz
    have hz1 : 1 ≤ z.im :=
      le_trans (le_trans (le_max_right M0 1) (le_max_right Aψ (max M0 1))) hz
    have htim : 0 < z.im := lt_of_lt_of_le (by norm_num) hz1
    have hψI :
        ‖ψI' z‖ ≤ Cψ * Real.exp (4 * Real.pi * z.im) := by
      have h' : ψI' z = ψI ⟨z, htim⟩ := by simp [ψI', htim]
      have := hψbd ⟨z, htim⟩ hzA
      simpa [h'] using this
    have hexp : ‖expU u z‖ = Real.exp (-Real.pi * u * z.im) := by
      simp [expU, Complex.norm_exp, mul_left_comm, mul_comm]
    have hmul :
        ‖f z‖ ≤ (Cψ * Real.exp (4 * Real.pi * z.im)) * Real.exp (-Real.pi * u * z.im) := by
      have hnexp : 0 ≤ ‖expU u z‖ := norm_nonneg _
      have hmul' :
          ‖ψI' z‖ * ‖expU u z‖ ≤ (Cψ * Real.exp (4 * Real.pi * z.im)) * ‖expU u z‖ :=
        mul_le_mul_of_nonneg_right hψI hnexp
      have hmul'' :
          ‖ψI' z‖ * ‖expU u z‖ ≤
            (Cψ * Real.exp (4 * Real.pi * z.im)) * Real.exp (-Real.pi * u * z.im) := by
        simpa [hexp] using hmul'
      simpa [f, norm_mul, mul_assoc, mul_left_comm, mul_comm] using hmul''
    have hEq :
        (Cψ * Real.exp (4 * Real.pi * z.im)) * Real.exp (-Real.pi * u * z.im) =
          (Cψ : ℝ) * Real.exp (-b * z.im) := by
      have hprod :
          Real.exp (4 * Real.pi * z.im) * Real.exp (-Real.pi * u * z.im) =
            Real.exp ((4 * Real.pi * z.im) + (-Real.pi * u * z.im)) := by
        simpa using (Eq.symm (Real.exp_add (4 * Real.pi * z.im) (-Real.pi * u * z.im)))
      grind only
    have hmul0 : ‖f z‖ ≤ (Cψ : ℝ) * Real.exp (-b * z.im) :=
      le_trans hmul (le_of_eq hEq)
    have hzlt : (Cψ : ℝ) * Real.exp (-b * z.im) < ε := by
      have := hM0 (z.im) hzM
      -- `dist x 0 = |x|` and both factors are nonnegative.
      simpa [Real.dist_eq, abs_of_nonneg (le_of_lt hCψ), abs_of_pos (Real.exp_pos _)] using this
    exact lt_of_le_of_lt hmul0 hzlt
  -- Apply the open-rectangle deformation with an empty exceptional set.
  have hdiff :
      ∀ z ∈ ((Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1)) ×ℂ (Ioi (1 : ℝ))) \ (∅ : Set ℂ),
        DifferentiableAt ℂ f z := by
    intro z hz
    have hzIm1 : z.im ∈ Ioi (1 : ℝ) := (mem_reProdIm.1 (by simpa using hz.1)).2
    have hzIm : 0 < z.im := lt_of_lt_of_le (by norm_num) (le_of_lt hzIm1)
    exact (hdiffOn z hzIm).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hzIm)
  have hEq :
      ((∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + Complex.I)) +
          (Complex.I : ℂ) * ∫ t : ℝ in Set.Ioi (1 : ℝ), f ((1 : ℂ) + t * Complex.I)) -
        (Complex.I : ℂ) * ∫ t : ℝ in Set.Ioi (1 : ℝ), f ((t : ℂ) * Complex.I) = 0 := by
    simpa [min_eq_left (zero_le_one : (0 : ℝ) ≤ 1), max_eq_right (zero_le_one : (0 : ℝ) ≤ 1),
      smul_eq_mul] using
      (integral_boundary_open_rect_eq_zero_of_differentiable_on_off_countable_of_integrable_on
        (y := (1 : ℝ)) (f := f) (x₁ := (0 : ℝ)) (x₂ := (1 : ℝ)) hcont (s := (∅ : Set ℂ))
        (by simp) hdiff hInt_left hInt_right htendsto)
  -- Isolate the bottom edge and rewrite the difference of vertical integrals using `ψS`.
  have hbottom :
      (∫ x : ℝ in (0 : ℝ)..1, f (x + Complex.I)) =
        (Complex.I : ℂ) • ∫ t : ℝ in Set.Ioi (1 : ℝ),
          (ψI' (t * Complex.I) - ψI' (t * Complex.I + 1)) * expU u (t * Complex.I) := by
    -- `bottom + right - left = 0` and rewrite `right` using `hu`.
    set A : ℂ := (Complex.I : ℂ) * ∫ t : ℝ in Set.Ioi (1 : ℝ), f ((1 : ℂ) + t * Complex.I)
    set B : ℂ := (Complex.I : ℂ) * ∫ t : ℝ in Set.Ioi (1 : ℝ), f ((t : ℂ) * Complex.I)
    have hBA : (∫ x : ℝ in (0 : ℝ)..1, f (x + Complex.I)) + A = B := by
      have : ((∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + Complex.I)) + A) - B = 0 := by
        simpa [A, B, smul_eq_mul] using hEq
      exact (sub_eq_zero.mp this)
    have hmain : (∫ x : ℝ in (0 : ℝ)..1, f (x + Complex.I)) = B - A :=
      eq_sub_of_add_eq hBA
    -- Rewrite `B - A` as a single integral.
    have hA' :
        A =
          (Complex.I : ℂ) *
            ∫ t : ℝ in Set.Ioi (1 : ℝ),
              ψI' (t * Complex.I + 1) * expU u (t * Complex.I) := by
      -- Use `expU` periodicity and unfold.
      have hcongr :
          (∫ t : ℝ in Set.Ioi (1 : ℝ), f ((1 : ℂ) + t * Complex.I)) =
            ∫ t : ℝ in Set.Ioi (1 : ℝ), ψI' (t * Complex.I + 1) * expU u (t * Complex.I) := by
        refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
        intro t ht
        have hadd : (1 : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I + 1 := by
          ac_rfl
        have hexp' :
            expU u ((t : ℂ) * Complex.I + 1) = expU u ((t : ℂ) * Complex.I) :=
          expU_add_one (u := u) (hu := hu) (z := (t : ℂ) * Complex.I)
        calc
          f ((1 : ℂ) + t * Complex.I) =
              ψI' ((1 : ℂ) + t * Complex.I) * expU u ((1 : ℂ) + t * Complex.I) := rfl
          _ = ψI' ((t : ℂ) * Complex.I + 1) * expU u ((t : ℂ) * Complex.I + 1) := by
              simp [hadd]
          _ = ψI' ((t : ℂ) * Complex.I + 1) * expU u ((t : ℂ) * Complex.I) := by
              simp [hexp']
      simp [A, hcongr]
    have hB' :
        B =
          (Complex.I : ℂ) *
            ∫ t : ℝ in Set.Ioi (1 : ℝ), ψI' (t * Complex.I) * expU u (t * Complex.I) := by
      simp [B, f]
    -- Combine.
    have hmain' :
        (∫ x : ℝ in (0 : ℝ)..1, f ((x : ℂ) + Complex.I)) = B - A := by
      simpa using hmain
    -- Prove linearity of the set integral for the relevant integrands.
    let g : ℝ → ℂ := fun t : ℝ => ψI' (t * Complex.I) * expU u (t * Complex.I)
    let h : ℝ → ℂ := fun t : ℝ => ψI' (t * Complex.I + 1) * expU u (t * Complex.I)
    have hInt_g : MeasureTheory.IntegrableOn g (Set.Ioi (1 : ℝ)) MeasureTheory.volume := by
      simpa [g, f, zero_add] using hInt_left
    have hEqOn_h :
        EqOn (fun t : ℝ => f ((1 : ℂ) + t * Complex.I)) h (Set.Ioi (1 : ℝ)) := by
      intro t ht
      have hadd : (1 : ℂ) + (t : ℂ) * Complex.I = (t : ℂ) * Complex.I + 1 := by
        ac_rfl
      have hexp' :
          expU u ((t : ℂ) * Complex.I + 1) = expU u ((t : ℂ) * Complex.I) :=
        expU_add_one (u := u) (hu := hu) (z := (t : ℂ) * Complex.I)
      calc
        f ((1 : ℂ) + t * Complex.I) =
            ψI' ((1 : ℂ) + t * Complex.I) * expU u ((1 : ℂ) + t * Complex.I) := rfl
        _ = ψI' ((t : ℂ) * Complex.I + 1) * expU u ((t : ℂ) * Complex.I + 1) := by
            simp [hadd]
        _ = h t := by
            simp [h, hexp']
    have hInt_h : MeasureTheory.IntegrableOn h (Set.Ioi (1 : ℝ)) MeasureTheory.volume :=
      hInt_right.congr_fun hEqOn_h measurableSet_Ioi
    have hgI :
        MeasureTheory.Integrable g (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using hInt_g
    have hhI :
        MeasureTheory.Integrable h (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
      simpa [MeasureTheory.IntegrableOn] using hInt_h
    have hsub :
        (∫ t : ℝ in Set.Ioi (1 : ℝ), g t) - (∫ t : ℝ in Set.Ioi (1 : ℝ), h t) =
          ∫ t : ℝ in Set.Ioi (1 : ℝ), (g t - h t) := by
      simpa using (MeasureTheory.integral_sub hgI hhI).symm
    have hgh :
        (fun t : ℝ => g t - h t) =
          fun t : ℝ =>
            (ψI' (t * Complex.I) - ψI' (t * Complex.I + 1)) * expU u (t * Complex.I) := by
      funext t
      -- `g t - h t = (ψI'(tI) - ψI'(tI+1)) * expU u (tI)`.
      simpa [g, h] using
        (sub_mul (ψI' (t * Complex.I)) (ψI' (t * Complex.I + 1)) (expU u (t * Complex.I))).symm
    -- Finish by rewriting the goal to `B - A` and using `integral_sub`.
    have hBA' :
        B - A =
          (Complex.I : ℂ) * ∫ t : ℝ in Set.Ioi (1 : ℝ),
            (ψI' (t * Complex.I) - ψI' (t * Complex.I + 1)) * expU u (t * Complex.I) := by
      -- Expand `A` and `B`, then use `integral_sub` (via `hsub`) and rewrite the integrand.
      grind only
    -- Convert `•` to `*` and conclude.
    simp [hmain', hBA', smul_eq_mul]
  -- Finally, convert the integrand difference to `ψS'`.
  have hdiffS :
      (Complex.I : ℂ) • ∫ t : ℝ in Set.Ioi (1 : ℝ),
          (ψI' (t * Complex.I) - ψI' (t * Complex.I + 1)) * expU u (t * Complex.I) =
        (Complex.I : ℂ) •
          ∫ t : ℝ in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I) := by
    refine congrArg (fun w : ℂ => (Complex.I : ℂ) • w) ?_
    refine MeasureTheory.setIntegral_congr_fun (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi ?_
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (le_of_lt ht)
    have hz : 0 < ((t : ℂ) * Complex.I).im := by simpa using ht0
    have : ψI' (t * Complex.I) - ψI' (t * Complex.I + 1) = ψS' (t * Complex.I) :=
      SpecialValuesAux.Deriv.ψI'_sub_ψI'_add_one_eq_ψS' (z := t * Complex.I) hz
    simp [this]
  -- Assemble and simplify.
  simpa [f] using (hbottom.trans hdiffS)

/-! #### Factorization for the `J₂'+J₄'+J₆'` block -/

lemma J₂'_eq_top_ψI_mul_expU_one_inv (u : ℝ) :
    J₂' u =
      (∫ t in (0 : ℝ)..1,
          ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) *
        (expU u 1)⁻¹ := by
  let w : ℂ := expU u 1
  have hw : w ≠ 0 := by simp [w, expU]
  dsimp [RealIntegrals.J₂', w]
  have hcongr :
      (∫ t in (0 : ℝ)..1, ψT' (z₂' t) * expU u (z₂' t)) =
        ∫ t in (0 : ℝ)..1,
          ψI' ((t : ℂ) + Complex.I) * (expU u ((t : ℂ) + Complex.I) * w⁻¹) := by
    refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
    intro t ht
    have htIcc : t ∈ Icc (0 : ℝ) 1 := mem_Icc01_of_mem_uIcc01 ht
    have hψ : ψT' (z₂' t) = ψI' ((t : ℂ) + Complex.I) :=
      ψT'_z₂'_eq_ψI'_add_one (t := t) htIcc
    have hz : z₂' t + 1 = (t : ℂ) + Complex.I := by
      simp [MagicFunction.Parametrisations.z₂'_eq_of_mem (t := t) htIcc, add_left_comm, add_comm]
    have hexp : expU u (z₂' t) = expU u ((t : ℂ) + Complex.I) * w⁻¹ := by
      have hmul := expU_add_one_mul (u := u) (z := z₂' t)
      have hstep : expU u ((t : ℂ) + Complex.I) = expU u (z₂' t) * w := by
        simpa [w, hz] using hmul
      have hmulInv := congrArg (fun z : ℂ => z * w⁻¹) hstep
      simpa [mul_assoc, hw] using hmulInv.symm
    simp [hψ, hexp]
  have hpull :
      (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * (expU u ((t : ℂ) + Complex.I) * w⁻¹)) =
        (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) * w⁻¹ := by
    simpa [mul_assoc] using
      (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (f := fun t : ℝ => ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) (w⁻¹))
  have htmp :
      (∫ t in (0 : ℝ)..1, ψT' (z₂' t) * expU u (z₂' t)) =
        (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) *
          (expU u 1)⁻¹ :=
    hcongr.trans hpull
  assumption

lemma J₆'_eq_neg_two_I_smul_vertical (u : ℝ) :
    J₆' u =
      (-2 : ℂ) *
        (Complex.I • ∫ t in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)) := by
  exact Deriv.J₆'_eq_vertical_Ioi u

lemma top_ψI_integral_eq_top_ψS_add_top_ψT (u : ℝ) :
    (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) =
      (∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) +
        ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
  have hψI : Continuous fun t : ℝ => ψI' ((t : ℂ) + Complex.I) := by
    simpa using SpherePacking.Dim24.PsiRewrites.continuous_ψI'_add_I
  have hψS : Continuous fun t : ℝ => ψS' ((t : ℂ) + Complex.I) := by
    simpa using SpherePacking.Dim24.PsiRewrites.continuous_ψS'_add_I
  have hψT : Continuous fun t : ℝ => ψT' ((t : ℂ) + Complex.I) := by
    simpa using SpherePacking.Dim24.PsiRewrites.continuous_ψT'_add_I
  have hE : Continuous fun t : ℝ => expU u ((t : ℂ) + Complex.I) := by
    have :
        Continuous fun t : ℝ =>
          Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) + Complex.I) := by
      fun_prop
    simpa [expU] using this.cexp
  have hI :
      IntervalIntegrable (fun t : ℝ => ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
        MeasureTheory.volume (0 : ℝ) 1 :=
    (hψI.mul hE).intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
  have hT :
      IntervalIntegrable (fun t : ℝ => ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
        MeasureTheory.volume (0 : ℝ) 1 :=
    (hψT.mul hE).intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
  have hS :
      IntervalIntegrable (fun t : ℝ => ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))
        MeasureTheory.volume (0 : ℝ) 1 :=
    (hψS.mul hE).intervalIntegrable (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := (1 : ℝ))
  have hSub :
      ∫ t in (0 : ℝ)..1,
          (ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) -
            ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) =
        (∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)) -
          ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) :=
    intervalIntegral.integral_sub hI hT
  have hCongr :
      (∫ t in (0 : ℝ)..1,
          (ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) -
            ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I))) =
        ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) := by
    refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
    intro t ht
    have hz : 0 < (((t : ℂ) + Complex.I).im) := by simp
    have hrel : ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I) = ψS' ((t : ℂ) + Complex.I) :=
      ψI'_sub_ψT'_eq_ψS'_of_im_pos (z := (t : ℂ) + Complex.I) hz
    have hfac :
        ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) -
            ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I) =
          (ψI' ((t : ℂ) + Complex.I) - ψT' ((t : ℂ) + Complex.I)) *
            expU u ((t : ℂ) + Complex.I) := by
      simp [sub_mul]
    simp [hfac, hrel]
  simp_all

lemma J₂'_J₄'_J₆'_factor_smooth (u : ℝ) (hu0 : 0 ≤ u) :
    J₂' u + J₄' u + J₆' u =
      ((expU u 1)⁻¹ - 1) * ((-J₄' u) + (-1 / 2 : ℂ) * J₆' u) := by
  -- Abbreviations for the four integrals on the line `Im z = 1` and the vertical tail.
  let HI : ℂ :=
    ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)
  let HT : ℂ :=
    ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)
  let HS : ℂ :=
    ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u ((t : ℂ) + Complex.I)
  let V : ℂ := ∫ t in Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u (t * Complex.I)
  let w : ℂ := expU u 1
  have hHI : HI = HS + HT := by
    simpa [HI, HS, HT] using (top_ψI_integral_eq_top_ψS_add_top_ψT (u := u))
  have hJ2 : J₂' u = HI * w⁻¹ := by
    simpa [HI, w] using (J₂'_eq_top_ψI_mul_expU_one_inv (u := u))
  have hJ4 : -J₄' u = HT := by
    have h := SpecialValuesAux.Deriv.J₄'_eq_neg_topEdge (u := u)
    have h' := congrArg Neg.neg h
    simpa [HT, neg_neg, sub_eq_add_neg, add_assoc] using h'
  have hJ4' : J₄' u = -HT := by
    have h'' := congrArg Neg.neg hJ4
    simpa using h''
  have hJ6 : J₆' u = (-2 : ℂ) * (Complex.I • V) := by
    simpa [V] using (J₆'_eq_neg_two_I_smul_vertical (u := u))
  have hHS : HS = (1 + w) * (Complex.I • V) := by
    simpa [HS, V, w] using (ψS_rect_integral_eq_one_add_expU_one_mul_vertical (u := u) hu0)
  have hIV : (Complex.I • V) = (-1 / 2 : ℂ) * J₆' u := by
    grind only
  -- Expand the factorization in terms of `HS,HT,V` and simplify.
  have hw0 : w ≠ 0 := by simp [w, expU]
  calc
    J₂' u + J₄' u + J₆' u
        = (HI * w⁻¹) + (-HT) + ((-2 : ℂ) * (Complex.I • V)) := by
            simp [hJ2, hHI, hJ4', hJ6, add_assoc, HT]
    _ = (w⁻¹ * HS + (w⁻¹ - 1) * HT) + ((-2 : ℂ) * (Complex.I • V)) := by
          -- distribute `w⁻¹` and regroup
          simp [hHI, HS, HT, mul_add, add_assoc, add_comm, sub_eq_add_neg, mul_left_comm, mul_comm]
          ring_nf
    _ = ((w⁻¹ - 1) * (HT + (Complex.I • V))) := by
          -- Use `HS = (1+w) * I•V` and simplify.
          simp [hHS, smul_eq_mul, sub_eq_add_neg, add_assoc, add_comm]
          field_simp [hw0]
          ring_nf
    _ = ((expU u 1)⁻¹ - 1) * ((-J₄' u) + (-1 / 2 : ℂ) * J₆' u) := by
          -- Replace `HT` and `I•V` by `-J₄'` and `(-1/2) * J₆'`.
          lia

/-- For `k > 2`, the profile `bProfile` has derivative `0` at `u = 2k` (a double zero). -/
public lemma bProfile_hasDerivAt_zero_two_mul_nat_of_two_lt (k : ℕ) (hk : 2 < k) :
    HasDerivAt bProfile 0 ((2 : ℝ) * k) := by
  -- Combine the `J₁/J₃/J₅` and `J₂/J₄/J₆` blocks.
  set u0 : ℝ := (2 : ℝ) * k
  have hu : expU u0 1 = 1 := by simpa [u0] using expU_two_mul_nat_one (k := k)
  have hu4 : 4 < u0 := by
    have hk' : (2 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have : (4 : ℝ) < (2 : ℝ) * (k : ℝ) := by nlinarith
    simpa [u0] using this
  have h135 : HasDerivAt (fun u : ℝ => J₁' u + J₃' u + J₅' u) 0 u0 :=
    J₁'_J₃'_J₅'_hasDerivAt_zero_of (u0 := u0) hu
  -- The `J₂/J₄/J₆` block has a double zero at even integers `> 4` via the `ψI` rectangle identity.
  -- We only need the conclusion at `u0`.
  have h246 : HasDerivAt (fun u : ℝ => J₂' u + J₄' u + J₆' u) 0 u0 := by
    have hu0pos : 0 < u0 := by
      have : (0 : ℝ) < (2 : ℝ) * (k : ℝ) := by nlinarith
      simpa [u0] using this
    have hu0' : 0 ≤ u0 := le_of_lt hu0pos
    let a : ℝ → ℂ := fun u : ℝ => (expU u 1)⁻¹ - 1
    let b : ℝ → ℂ := fun u : ℝ => (-J₄' u) + (-1 / 2 : ℂ) * J₆' u
    have hEq :
        (fun u : ℝ => J₂' u + J₄' u + J₆' u) =ᶠ[𝓝 u0] fun u : ℝ => a u * b u := by
      filter_upwards [isOpen_Ioi.mem_nhds hu0pos] with u hu
      have hu' : 0 ≤ u := le_of_lt hu
      simpa [a, b, mul_assoc, add_assoc, add_left_comm, add_comm] using
        (J₂'_J₄'_J₆'_factor_smooth (u := u) hu')
    have ha : HasDerivAt a (-(expU u0 1)⁻¹ * ((Real.pi : ℂ) * Complex.I)) u0 := by
      have hsub :
          HasDerivAt (fun u : ℝ => (expU u 1)⁻¹ - 1) (-(expU u0 1)⁻¹ * ((Real.pi : ℂ) * Complex.I)) u0 :=
        (hasDerivAt_expU_one_inv (u0 := u0)).sub_const (1 : ℂ)
      simpa [a] using hsub
    have hb_diff : DifferentiableAt ℝ b u0 := by
      have hJ4 : DifferentiableAt ℝ RealIntegrals.J₄' u0 :=
        (Schwartz.J4Smooth.contDiff_J₄'.contDiffAt (x := u0)).differentiableAt (by simp)
      have hIoi : Set.Ioi (-1 : ℝ) ∈ nhds u0 := by
        have : (-1 : ℝ) < u0 := lt_of_lt_of_le (by norm_num) hu0'
        exact isOpen_Ioi.mem_nhds this
      have hJ6 : DifferentiableAt ℝ RealIntegrals.J₆' u0 :=
        by
          have hcont := Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1
          exact (hcont.contDiffAt (x := u0) hIoi).differentiableAt (by simp)
      have hmul : DifferentiableAt ℝ (fun u : ℝ => (-1 / 2 : ℂ) * RealIntegrals.J₆' u) u0 :=
        ((differentiableAt_const (-1 / 2 : ℂ) :
          DifferentiableAt ℝ (fun _ : ℝ => (-1 / 2 : ℂ)) u0)).mul hJ6
      simpa [b, add_assoc, mul_assoc] using (hJ4.neg.add hmul)
    have hb : HasDerivAt b (deriv b u0) u0 := hb_diff.hasDerivAt
    have ha0 : a u0 = 0 := by simp [a, hu]
    have hb0 : b u0 = 0 := by
      -- Auxiliary integrals at `u0`.
      let HI : ℂ :=
        ∫ t in (0 : ℝ)..1, ψI' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I)
      let HT : ℂ :=
        ∫ t in (0 : ℝ)..1, ψT' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I)
      let HS : ℂ :=
        ∫ t in (0 : ℝ)..1, ψS' ((t : ℂ) + Complex.I) * expU u0 ((t : ℂ) + Complex.I)
      let V : ℂ := ∫ t in Set.Ioi (1 : ℝ), ψS' (t * Complex.I) * expU u0 (t * Complex.I)
      have hrectHI : HI = (Complex.I : ℂ) • V := by
        simpa [HI, V] using (ψI_rect_integral_eq_vertical_ψS (u := u0) (hu := hu) (hu4 := hu4))
      have hHI : HI = HS + HT := by
        simpa [HI, HS, HT] using (top_ψI_integral_eq_top_ψS_add_top_ψT (u := u0))
      have hsum : J₂' u0 + J₄' u0 + J₆' u0 = 0 := J₂'_J₄'_J₆'_zero_sum_of (u := u0) hu hu0'
      have hJ2 : J₂' u0 = HI := by
        simpa [HI, hu] using (J₂'_eq_top_ψI_mul_expU_one_inv (u := u0))
      have hJ4 : J₄' u0 = -HT := by
        simpa [HT] using (SpecialValuesAux.Deriv.J₄'_eq_neg_topEdge (u := u0))
      have hJ6 : J₆' u0 = (-2 : ℂ) * (Complex.I • V) := by
        simpa [V] using (J₆'_eq_neg_two_I_smul_vertical (u := u0))
      grind only
    have hprod : HasDerivAt (fun u : ℝ => a u * b u) 0 u0 := by
      have hmul := ha.mul hb
      simpa [ha0, hb0] using hmul
    exact hprod.congr_of_eventuallyEq hEq
  have hb :
      (fun u : ℝ => bProfile u) =
        fun u : ℝ => (J₁' u + J₃' u + J₅' u) + (J₂' u + J₄' u + J₆' u) := by
    funext u
    simp [bProfile, RealIntegrals.b', add_assoc, add_left_comm]
  have hsum : HasDerivAt (fun u : ℝ => (J₁' u + J₃' u + J₅' u) + (J₂' u + J₄' u + J₆' u)) 0 u0 := by
    simpa using h135.add h246
  simpa [hb] using hsum

end ZerosAuxB

/-- Zeros of `b` on the Leech radii `‖x‖ = √(2k)` for integers `k` (in particular `k ≥ 2`).

Faithfulness note:
In `dim_24.tex` (Section 3), `b(r)` has zeros at `r=2` and at all `r=√(2k)` with `k>2`.
However, at `r=√2` and `r=2` there is a pole/zero cancellation, so these roots are *simple* in `r`
(the paper gives `b(√2)=0`, `b'(√2) ≠ 0`, `b(2)=0`, `b'(2) ≠ 0`).
-/
public theorem b_zero_of_norm_sq_eq_two_mul (k : ℕ) :
    ∀ x : ℝ²⁴, ‖x‖ ^ 2 = (2 : ℝ) * k → b x = 0 := by
  /- Proof sketch:
  Use the analytic continuation formula (paper (3.4) and its continuation (3.5)):
  - for `k>2`, the non-sine factor is analytic at `r=√(2k)`, so `sin(π r^2/2)^2` forces vanishing;
  - for `k=2`, the same continuation yields a simple zero at `r=2` after cancellation. -/
  intro x hx
  have hb : b x = bProfile (‖x‖ ^ 2) := SpecialValuesAux.b_apply (x := x)
  -- Reduce to the even-integer vanishing of the profile.
  simpa [hb, hx] using (ZerosAuxB.bProfile_two_mul_nat (k := k))

/-- For `k > 2`, the one-variable profile has at least a double root at `r = √(2k)`. -/
public theorem bRadial_hasDerivAt_zero_of_two_lt (k : ℕ) (hk : 2 < k) :
    HasDerivAt bRadial 0 (Real.sqrt ((2 : ℝ) * k)) := by
  /- Proof sketch:
  As for `a`: for `k>2` the continuation shows the non-sine term is analytic at `r=√(2k)`,
  so `sin(π r^2/2)^2` enforces vanishing to second order in `r`. -/
  -- Reduce to the profile in the variable `u = r^2`.
  have hbEq : bRadial = fun r : ℝ => bProfile (r ^ 2) := by
    funext r
    simpa using (SpecialValuesAux.bRadial_eq (r := r))
  set r0 : ℝ := Real.sqrt ((2 : ℝ) * k)
  have hr0 : 0 ≤ r0 := by
    have : (0 : ℝ) ≤ (2 : ℝ) * k := by positivity
    simp [r0]
  have hr0sq : r0 ^ 2 = (2 : ℝ) * k := by
    have : 0 ≤ ((2 : ℝ) * k) := by positivity
    simpa [r0] using (Real.sq_sqrt this)
  have hbprof : HasDerivAt bProfile 0 ((2 : ℝ) * k) :=
    ZerosAuxB.bProfile_hasDerivAt_zero_two_mul_nat_of_two_lt (k := k) hk
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r0) r0 := by
    simpa [pow_two, two_mul, mul_assoc] using (hasDerivAt_pow 2 r0)
  have hbprof' : HasDerivAt bProfile (0 : ℂ) (r0 ^ 2) := by
    simpa [hr0sq] using hbprof
  have hcomp : HasDerivAt (fun r : ℝ => bProfile (r ^ 2)) (0 : ℂ) r0 := by
    let inst : IsScalarTower ℝ ℝ ℂ := ⟨by intro a b z; simp [smul_eq_mul, mul_assoc]⟩
    have hcomp' : HasDerivAt (bProfile ∘ fun r : ℝ => r ^ 2) ((2 * r0) • (0 : ℂ)) r0 :=
      @HasDerivAt.scomp ℝ _ ℂ _ _ r0 ℝ _ _ _ inst (fun r : ℝ => r ^ 2) (2 * r0) bProfile (0 : ℂ) hbprof' hsq
    simpa [Function.comp] using hcomp'
  simpa [hbEq] using hcomp

end

end SpherePacking.Dim24
