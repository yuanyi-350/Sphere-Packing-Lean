module
import SpherePacking.Dim8.MagicFunction.b.Eigenfunction.PermJ12ContourDeformation
public import SpherePacking.Dim8.MagicFunction.b.Schwartz.Basic
import SpherePacking.Dim8.MagicFunction.b.Eigenfunction.PermJ12CurveIntegrals
import SpherePacking.Dim8.MagicFunction.b.Eigenfunction.PermJ12FourierJ1
import SpherePacking.Dim8.MagicFunction.b.Eigenfunction.PermJ12FourierJ2
import SpherePacking.Dim8.MagicFunction.b.Eigenfunction.PermJ5
import SpherePacking.Contour.GaussianIntegral
import SpherePacking.Contour.PermJ12FourierCurveIntegral
import SpherePacking.Contour.PermJ12Fourier
import SpherePacking.ForMathlib.GaussianFourierCommon


/-!
# Fourier permutations for `b`

This file combines contour permutation identities for the integrals defining `b` to show that `b`
is a `(-1)`-eigenfunction of the Fourier transform on `EuclideanSpace ℝ (Fin 8)`.

## Main statement
* `eig_b`
-/

namespace MagicFunction.b.Fourier

noncomputable section

open scoped FourierTransform RealInnerProductSpace Topology

open MagicFunction.b.SchwartzIntegrals MagicFunction.FourierEigenfunctions SchwartzMap

local notation "ℝ⁸" => EuclideanSpace ℝ (Fin 8)

section Integral_Permutations

open scoped Real

open Set Complex Real MeasureTheory MagicFunction.Parametrisations intervalIntegral
open SpherePacking.ForMathlib
open SpherePacking.Integration
open SpherePacking.Contour
open Filter
open scoped Interval

private lemma integrable_permJ1Kernel' (w : ℝ⁸) :
    Integrable (permJ1Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) := by
  let sProd : Set (ℝ⁸ × ℝ) := (Set.univ : Set ℝ⁸) ×ˢ Ioc (0 : ℝ) 1
  have hsProd : MeasurableSet sProd := by
    simpa [sProd] using (MeasurableSet.univ.prod measurableSet_Ioc)
  have hmeas :
      AEStronglyMeasurable (permJ1Kernel w) ((volume : Measure ℝ⁸).prod μIoc01) := by
    let μProd : Measure (ℝ⁸ × ℝ) := (volume : Measure ℝ⁸).prod (volume : Measure ℝ)
    have hμ : ((volume : Measure ℝ⁸).prod μIoc01) = μProd.restrict sProd := by
      simpa [sProd, μProd] using
        (SpherePacking.Integration.prod_muIoc01_eq_restrict (μ := (volume : Measure ℝ⁸)))
    have hcontψ : ContinuousOn (fun t : ℝ => ψT' (z₁line t)) (Ioc (0 : ℝ) 1) :=
      continuousOn_ψT'_z₁line
    have hcont : ContinuousOn (permJ1Kernel w) sProd := by
      have hphase : Continuous fun p : ℝ⁸ × ℝ => cexp ((-2 * (π * ⟪p.1, w⟫)) * I) := by
        have hinner : Continuous fun p : ℝ⁸ × ℝ => (⟪p.1, w⟫ : ℝ) := by
          simpa using (continuous_fst.inner continuous_const)
        have hreal : Continuous fun p : ℝ⁸ × ℝ => (-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ)) :=
          continuous_const.mul (continuous_const.mul hinner)
        have harg :
            Continuous fun p : ℝ⁸ × ℝ =>
              ((((-2 : ℝ) * ((π : ℝ) * (⟪p.1, w⟫ : ℝ))) : ℝ) : ℂ) * (Complex.I : ℂ) :=
          (Complex.continuous_ofReal.comp hreal).mul continuous_const
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg)
      have hψ : ContinuousOn (fun p : ℝ⁸ × ℝ => ψT' (z₁line p.2)) sProd := by
        refine hcontψ.comp continuousOn_snd ?_
        intro p hp
        exact (Set.mem_prod.mp hp).2
      have hgauss :
          Continuous fun p : ℝ⁸ × ℝ =>
            cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)) := by
        have hnormsq : Continuous fun p : ℝ⁸ × ℝ => (‖p.1‖ ^ 2 : ℝ) :=
          (continuous_fst.norm.pow 2)
        have hz : Continuous fun p : ℝ⁸ × ℝ => z₁line p.2 :=
          continuous_z₁line.comp continuous_snd
        have harg' :
            Continuous fun p : ℝ⁸ × ℝ =>
              (π : ℂ) * I * (((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2)) :=
          continuous_const.mul ((continuous_ofReal.comp hnormsq).mul hz)
        simpa [mul_assoc] using (Complex.continuous_exp.comp harg')
      have hconst : ContinuousOn (fun _p : ℝ⁸ × ℝ => (Complex.I : ℂ)) sProd :=
        continuousOn_const
      have hmul1 :
          ContinuousOn (fun p : ℝ⁸ × ℝ => (Complex.I : ℂ) * ψT' (z₁line p.2)) sProd :=
        hconst.mul hψ
      have hmul2 :
          ContinuousOn
            (fun p : ℝ⁸ × ℝ =>
              ((Complex.I : ℂ) * ψT' (z₁line p.2)) *
                cexp ((π : ℂ) * I * ((‖p.1‖ ^ 2 : ℝ) : ℂ) * (z₁line p.2))) sProd :=
        hmul1.mul hgauss.continuousOn
      refine (hphase.continuousOn.mul hmul2).congr ?_
      intro p _hp
      simp [permJ1Kernel, mul_assoc]
    have hker : AEStronglyMeasurable (permJ1Kernel w) (μProd.restrict sProd) := by
      simpa [μProd] using (hcont.aestronglyMeasurable (μ := μProd) (s := sProd) hsProd)
    simpa [hμ] using hker
  exact
    (MeasureTheory.integrable_prod_iff' (μ := (volume : Measure ℝ⁸)) (ν := μIoc01) hmeas).2
      ⟨ae_integrable_permJ1Kernel_slice (w := w), integrable_integral_norm_permJ1Kernel (w := w)⟩

private lemma integral_permJ1Kernel_x' (w : ℝ⁸) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    (∫ x : ℝ⁸, permJ1Kernel w (x, t)) = (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  have hz : 0 < (z₁line t).im := by simpa [z₁line] using ht.1
  let c : ℂ := (Complex.I : ℂ) * ψT' (z₁line t)
  have hfactor :
      (fun x : ℝ⁸ ↦ permJ1Kernel w (x, t)) =
        fun x : ℝ⁸ ↦
          c *
            (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
              cexp ((π : ℂ) * I * ((‖x‖ ^ 2 : ℝ) : ℂ) * (z₁line t))) := by
    funext x
    dsimp [permJ1Kernel, c]
    simp [mul_assoc, mul_left_comm, mul_comm]
  have hgauss :=
    SpherePacking.Contour.integral_const_mul_phase_gaussian_pi_mul_I_mul_even
      (k := 4) (w := w) (z := z₁line t) hz (c := c)
  calc
    (∫ x : ℝ⁸, permJ1Kernel w (x, t)) =
        c * ((((I : ℂ) / (z₁line t)) ^ (4 : ℕ)) *
          cexp ((π : ℂ) * I * (‖w‖ ^ 2 : ℝ) * (-1 / (z₁line t)))) := by
          simpa [hfactor] using hgauss
    _ = (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
          simp [c, Ψ₁_fourier, mul_assoc, mul_left_comm, mul_comm]

private lemma integral_permJ1Kernel_x_ae' (w : ℝ⁸) :
    (fun t : ℝ => (∫ x : ℝ⁸, permJ1Kernel w (x, t) ∂(volume : Measure _))) =ᵐ[μIoc01]
      fun t : ℝ => (Complex.I : ℂ) * Ψ₁_fourier (‖w‖ ^ 2) (z₁line t) := by
  simpa [SpherePacking.Integration.μIoc01] using
    (ae_restrict_iff' (μ := (volume : Measure ℝ)) (s := Ioc (0 : ℝ) 1) measurableSet_Ioc).2 <|
      .of_forall fun t ht => by simpa using (integral_permJ1Kernel_x' (w := w) (t := t) ht)

private lemma fourier_J₁_eq_curveIntegral' (w : ℝ⁸) :
    𝓕 (J₁ : ℝ⁸ → ℂ) w =
      (∫ᶜ z in Path.segment (-1 : ℂ) ((-1 : ℂ) + Complex.I),
        scalarOneForm (Ψ₁_fourier (‖w‖ ^ 2)) z) := by
  simpa using
    SpherePacking.Contour.fourier_J₁_eq_curveIntegral_of
      (fun x => by simpa using (J₁_apply (x := x)))
      phase_mul_J₁'_eq_integral_permJ1Kernel
      integrable_permJ1Kernel'
      integral_permJ1Kernel_x_ae'
      (fun w' => by
        simpa using (SpherePacking.Contour.integral_I_mul_muIoc01_z₁line (F := Ψ₁_fourier (‖w'‖ ^ 2))))
      w

theorem perm_J₁_J₂ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) ((J₁ : SchwartzMap ℝ⁸ ℂ) + J₂) =
      -((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) := by
  refine SpherePacking.Contour.perm_J₁_J₂_of
      (J₁ := (J₁ : SchwartzMap ℝ⁸ ℂ))
      (J₂ := J₂)
      (J₃ := (J₃ : SchwartzMap ℝ⁸ ℂ))
      (J₄ := J₄)
      (Ψ₁_fourier := Ψ₁_fourier)
      (Ψ₁' := Ψ₁')
      (h := by
        refine ⟨perm_J12_contour, ?_, ?_, ?_⟩
        · intro w
          simpa [SchwartzMap.fourier_coe] using (fourier_J₁_eq_curveIntegral' (w := w))
        · intro w
          simpa [SchwartzMap.fourier_coe] using (fourier_J₂_eq_curveIntegral (w := w))
        · intro w
          simpa [J₃_apply, J₄_apply, add_assoc, add_left_comm, add_comm] using
            (J₃'_add_J₄'_eq_curveIntegral_segments (r := ‖w‖ ^ (2 : ℕ))).symm)

theorem perm_₃_J₄ :
    FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) =
      -((J₁ : SchwartzMap ℝ⁸ ℂ) + J₂) := by
  let FT := FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ)
  have hsymm : FT.symm ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) = FT ((J₃ : SchwartzMap ℝ⁸ ℂ) + J₄) := by
    ext x
    simp only [FT, FourierTransform.fourierCLE_symm_apply, FourierTransform.fourierCLE_apply,
      fourier_coe, fourierInv_coe, fourierInv_eq_fourier_comp_neg]
    suffices (fun y : ℝ⁸ ↦ (J₃ + J₄) (-y)) = fun y ↦ (J₃ + J₄) y by
      simpa using congrArg (fun f : ℝ⁸ → ℂ => (𝓕 f) x) this
    funext y
    simp [J₃, J₄, schwartzMap_multidimensional_of_schwartzMap_real, compCLM_apply]
  simpa [FT] using
    SpherePacking.Contour.perm_J₃_J₄_of
      (J₁ := (J₁ : SchwartzMap ℝ⁸ ℂ))
      (J₂ := J₂)
      (J₃ := (J₃ : SchwartzMap ℝ⁸ ℂ))
      (J₄ := J₄)
      (hsymm := hsymm)
      (perm_J₁_J₂ := perm_J₁_J₂)

end Integral_Permutations

section Eigenfunction

/--
The Schwartz function `b` is a `(-1)`-eigenfunction of the Fourier transform on `ℝ⁸`.
-/
public theorem eig_b : FourierTransform.fourierCLE ℂ (SchwartzMap ℝ⁸ ℂ) b = -b := by
  rw [b_eq_sum_integrals_SchwartzIntegrals]
  have hrw : J₁ + J₂ + J₃ + J₄ + J₅ + J₆ = (J₁ + J₂) + (J₃ + J₄) + J₅ + J₆ := by ac_rfl
  rw [hrw, map_add, map_add, map_add, perm_J₁_J₂, perm_J₅, perm_₃_J₄, perm_J₆]
  abel

end Eigenfunction

end

end MagicFunction.b.Fourier
