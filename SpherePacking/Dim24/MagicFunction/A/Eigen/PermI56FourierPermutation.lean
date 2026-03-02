module
public import SpherePacking.Dim24.MagicFunction.A.Eigen.PermI56KernelSetup
import SpherePacking.ForMathlib.GaussianFourierCommon

/-!
# Fourier permutation for `I₅` and `I₆`

This file proves the permutation identities `𝓕 I₅ = I₆` and `𝓕 I₆ = I₅` used in the
dimension-24 Fourier eigenfunction proof for the magic function `a`.

## Main statements
* `perm_I₅`
* `perm_I₆`
-/

open scoped FourierTransform
open Complex Real

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24.AFourier
open MeasureTheory Set Complex Real Filter
open scoped Interval Topology RealInnerProductSpace UpperHalfPlane Manifold

noncomputable section
namespace PermI56

open Complex Real Set MeasureTheory Filter intervalIntegral
open scoped Interval
open MagicFunction.Parametrisations

local notation "FT" => FourierTransform.fourierCLE ℂ (SchwartzMap ℝ²⁴ ℂ)

/-- Fourier permutation identity: `𝓕 I₅ = I₆`. -/
public theorem perm_I₅ : FT I₅ = I₆ := by
  ext w
  -- Reduce to the underlying function equality `𝓕 I₅ = I₆`.
  simp only [FourierTransform.fourierCLE_apply, I₆_apply]
  change 𝓕 (I₅ : ℝ²⁴ → ℂ) w = _
  rw [fourier_eq' (I₅ : ℝ²⁴ → ℂ) w]
  simp only [smul_eq_mul, I₅_apply]
  -- Normalize the Fourier phase factor so it matches the lemmas in this file.
  have hphase :
      (fun v : ℝ²⁴ ↦ cexp (↑(-2 * π * ⟪v, w⟫) * I) * RealIntegrals.I₅' (‖v‖ ^ 2)) =
        fun v : ℝ²⁴ ↦ cexp (↑(-2 * (π * ⟪v, w⟫)) * I) * RealIntegrals.I₅' (‖v‖ ^ 2) := by
    funext v
    have hmul : (-2 * π * ⟪v, w⟫) = -2 * (π * ⟪v, w⟫) := by ring
    rw [hmul]
  have hphase_int :
      (∫ v : ℝ²⁴, cexp (↑(-2 * π * ⟪v, w⟫) * I) * RealIntegrals.I₅' (‖v‖ ^ 2)) =
        ∫ v : ℝ²⁴, cexp (↑(-2 * (π * ⟪v, w⟫)) * I) * RealIntegrals.I₅' (‖v‖ ^ 2) :=
    congrArg (fun F : ℝ²⁴ → ℂ => ∫ v : ℝ²⁴, F v) hphase
  rw [hphase_int]
  have hI5' (x : ℝ²⁴) :
      RealIntegrals.I₅' (‖x‖ ^ 2) = (-2 : ℂ) * ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s := by
    simpa using (complete_change_of_variables (r := ‖x‖ ^ 2))
  -- Move the `x`-dependent phase factor inside the `s`-integral so we can use Fubini.
  let μs : Measure ℝ := (volume : Measure ℝ).restrict (Ici (1 : ℝ))
  have hmul :
      (fun x : ℝ²⁴ ↦
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s) =
        fun x : ℝ²⁴ ↦
          ∫ s in Ici (1 : ℝ), cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * g (‖x‖ ^ 2) s := by
    ext x
    exact Eq.symm (MeasureTheory.integral_const_mul (cexp (↑(-2 * (π * ⟪x, w⟫)) * I)) (g (‖x‖ ^ 2)))
  -- Apply Fubini to swap the order of integration.
  let fker : ℝ²⁴ → ℝ → ℂ := fun x s => permI5Kernel w (x, s)
  have hint : Integrable (Function.uncurry fker) ((volume : Measure ℝ²⁴).prod μs) := by
    have h := integrable_permI5Kernel (w := w)
    have huncurry : Function.uncurry fker = permI5Kernel w := by
      rfl
    simpa [μs, μIciOne_def, μvol_def, μvol24_def, huncurry] using h
  have hswap :=
    (MeasureTheory.integral_integral_swap (μ := (volume : Measure ℝ²⁴)) (ν := μs) (f := fker) hint)
  -- Compute the inner integral using the Gaussian Fourier transform.
  have hinner (s : ℝ) (hs : s ∈ Ici (1 : ℝ)) :
      (∫ x : ℝ²⁴,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * g (‖x‖ ^ 2) s) =
        (-I : ℂ) * varphi' (I * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
    have hs_ne0 : (s : ℝ) ≠ 0 := ne_of_gt hs0
    have hcancel : ((s ^ (-12 : ℤ)) : ℂ) * (s ^ 12 : ℂ) = 1 :=
      zpow_neg_twelve_mul_pow_twelve (s := s) hs_ne0
    have hfactor :
        (fun x : ℝ²⁴ ↦
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * g (‖x‖ ^ 2) s) =
          fun x : ℝ²⁴ ↦
            ((-I : ℂ) * varphi' (I * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) := by
      funext x
      dsimp [g]
      -- Normalize the Gaussian factor `cexp ((-π) * r / s)` to the exact form used in the RHS.
      have harg :
          ((‖x‖ ^ 2 : ℝ) : ℂ) * (-π : ℂ) / (s : ℂ) =
            (-π : ℂ) * ((‖x‖ : ℂ) ^ (2 : ℕ)) / (s : ℂ) := by
        simp [div_eq_mul_inv, mul_left_comm, mul_comm]
      have hcexp :
          cexp (((‖x‖ ^ 2 : ℝ) : ℂ) * (-π : ℂ) / (s : ℂ)) =
            cexp ((-π : ℂ) * ((‖x‖ : ℂ) ^ (2 : ℕ)) / (s : ℂ)) :=
        congrArg cexp harg
      -- With the Gaussian factor rewritten, the remaining equality is by
      -- commutativity/associativity.
      simp
      ac_rfl
    calc
      (∫ x : ℝ²⁴,
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * g (‖x‖ ^ 2) s)
          =
          ∫ x : ℝ²⁴,
            ((-I : ℂ) * varphi' (I * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
              (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s)) :=
            congrArg (fun F : ℝ²⁴ → ℂ => ∫ x : ℝ²⁴, F x) hfactor
      _ =
          ((-I : ℂ) * varphi' (I * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
            ∫ x : ℝ²⁴, cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * cexp (-π * (‖x‖ ^ 2) / s) := by
            exact MeasureTheory.integral_const_mul (-I * varphi' (I * ↑s) * ↑s ^ (-12)) fun a =>
              cexp (↑(-2 * (π * ⟪a, w⟫)) * I) * cexp (-↑π * ↑‖a‖ ^ 2 / ↑s)
      _ =
          ((-I : ℂ) * varphi' (I * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
            ((s ^ 12 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s)) := by
            rw [SpherePacking.ForMathlib.integral_phase_gaussian_even
              (k := 12) (w := w) (s := s) hs0]
      _ = (-I : ℂ) * varphi' (I * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
            -- cancel `s^(-12) * s^12`.
            calc
              ((-I : ℂ) * varphi' (I * (s : ℂ)) * ((s ^ (-12 : ℤ)) : ℂ)) *
                  ((s ^ 12 : ℂ) * cexp (-π * (‖w‖ ^ 2) * s)) =
                  (-I : ℂ) * varphi' (I * (s : ℂ)) * (((s ^ (-12 : ℤ)) : ℂ) * (s ^ 12 : ℂ)) *
                    cexp (-π * (‖w‖ ^ 2) * s) := by
                      ac_rfl
              _ = (-I : ℂ) * varphi' (I * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) := by
                      rw [hcancel]
                      simp [mul_assoc]
  -- Use the swap and simplify to `I₆'`.
  have hswap' :
      (∫ x : ℝ²⁴, ∫ s : ℝ, fker x s ∂μs) =
          ∫ s : ℝ, ∫ x : ℝ²⁴, fker x s ∂(volume : Measure ℝ²⁴) ∂μs := by
    simpa using hswap
  -- Assemble the computation.
  calc
    (∫ x : ℝ²⁴,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            (RealIntegrals.I₅' (‖x‖ ^ 2)))
        =
        ∫ x : ℝ²⁴,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s) := by
          refine MeasureTheory.integral_congr_ae ?_
          refine ae_of_all _ ?_
          intro x
          simp [hI5' x, mul_assoc]
    _ =
        (-2 : ℂ) * ∫ x : ℝ²⁴,
          cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
            ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s := by
          -- Pull the scalar `(-2)` out of the `x`-integral.
          have hmul :
              (fun x : ℝ²⁴ ↦
                  cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                    ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s)) =
                fun x : ℝ²⁴ ↦
                  (-2 : ℂ) *
                    (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                      ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s) := by
            funext x
            ac_rfl
          calc
            (∫ x : ℝ²⁴,
                cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                  ((-2 : ℂ) * ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s)) =
                ∫ x : ℝ²⁴,
                  (-2 : ℂ) *
                    (cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                      ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s) := by
                exact congrArg (fun F : ℝ²⁴ → ℂ => ∫ x : ℝ²⁴, F x) hmul
            _ =
                (-2 : ℂ) * ∫ x : ℝ²⁴,
                  cexp (↑(-2 * (π * ⟪x, w⟫)) * I) *
                    ∫ s in Ici (1 : ℝ), g (‖x‖ ^ 2) s := by
                exact MeasureTheory.integral_const_mul (-2) fun a =>
                  cexp (↑(-2 * (π * ⟪a, w⟫)) * I) * ∫ (s : ℝ) in Ici 1, g (‖a‖ ^ 2) s
    _ =
        (-2 : ℂ) *
          ∫ x : ℝ²⁴, ∫ s in Ici (1 : ℝ),
            cexp (↑(-2 * (π * ⟪x, w⟫)) * I) * g (‖x‖ ^ 2) s := by
          congr 1
          exact congrArg (fun F : ℝ²⁴ → ℂ => ∫ x : ℝ²⁴, F x) hmul
    _ = (-2 : ℂ) * ∫ x : ℝ²⁴, ∫ s : ℝ, fker x s ∂μs := by
          simp [fker, permI5Kernel, μs, mul_assoc]
    _ = (-2 : ℂ) * ∫ s : ℝ, ∫ x : ℝ²⁴, fker x s ∂(volume : Measure ℝ²⁴) ∂μs := by
          simp [hswap']
    _ = (-2 : ℂ) * ∫ s : ℝ,
          (-I : ℂ) * varphi' (I * (s : ℂ)) * cexp (-π * (‖w‖ ^ 2) * s) ∂μs := by
          congr 1
          refine MeasureTheory.integral_congr_ae ?_
          refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
          intro s hs
          simpa [fker, permI5Kernel] using (hinner s hs)
    _ = RealIntegrals.I₆' (‖w‖ ^ 2) := by
          -- Unfold `I₆'` and rewrite `z₆' t = I*t` on `Ici 1`.
          have hz6_congr :
              (∫ t in Ici (1 : ℝ),
                  (I : ℂ) *
                    (varphi' (z₆' t) *
                      cexp (I * (↑π * (z₆' t * (↑‖w‖ ^ (2 : ℕ))))))) =
                ∫ t in Ici (1 : ℝ),
                  (I : ℂ) *
                    (varphi' (I * (t : ℂ)) *
                      cexp (-(↑t * (↑π * (↑‖w‖ ^ (2 : ℕ)))))) := by
            refine MeasureTheory.integral_congr_ae ?_
            refine (ae_restrict_iff' measurableSet_Ici).2 <| .of_forall ?_
            intro t ht
            have hz : z₆' t = (Complex.I : ℂ) * t := z₆'_eq_of_mem ht
            have hexp :
                (I : ℂ) * (↑π * (I * (↑t * (↑‖w‖ ^ (2 : ℕ))))) =
                  -(↑t * (↑π * (↑‖w‖ ^ (2 : ℕ)))) := by
              have hrewrite :
                  (I : ℂ) * (↑π * (I * (↑t * (↑‖w‖ ^ (2 : ℕ))))) =
                    (I : ℂ) * (I * (↑t * (↑π * (↑‖w‖ ^ (2 : ℕ))))) := by
                simp [mul_left_comm]
              -- Now use `I*I = -1`.
              calc
                (I : ℂ) * (↑π * (I * (↑t * (↑‖w‖ ^ (2 : ℕ))))) =
                    (I : ℂ) * (I * (↑t * (↑π * (↑‖w‖ ^ (2 : ℕ))))) := hrewrite
                _ = -(↑t * (↑π * (↑‖w‖ ^ (2 : ℕ)))) := by
                      -- `simp` does not reassociate `I * (I * A)` into `(I * I) * A`,
                      -- so we do this step explicitly and then use `I*I = -1`.
                      set A : ℂ := (↑t * (↑π * (↑‖w‖ ^ (2 : ℕ))))
                      calc
                        (I : ℂ) * (I * A) = ((I : ℂ) * I) * A := by
                          simpa using (mul_assoc (I : ℂ) I A).symm
                        _ = (-1 : ℂ) * A := by simp
                        _ = -A := by simp
            -- Rewrite `z₆' t` and the exponential argument; the two integrands become
            -- definitionally equal.
            simp [hz, hexp, mul_assoc]
          -- Now `I₆'` is exactly the same integral, and the remaining minus signs cancel.
          simp only [neg_mul, mul_comm, mul_neg, mul_assoc, RealIntegrals.I₆',
            RealIntegrals.RealIntegrands.Φ₆, RealIntegrals.ComplexIntegrands.Φ₆', ofReal_pow,
            mul_left_comm, μs]
          rw [hz6_congr]
          -- The remaining goal is sign bookkeeping: pull the inner negation out of the
          -- restricted integral.
          let F : ℝ → ℂ := fun s =>
            I * (varphi' (I * (s : ℂ)) * cexp (-(↑s * ((↑π : ℂ) * (↑‖w‖ ^ (2 : ℕ))))))
          have hnegI :
              (∫ s in Ici (1 : ℝ), -F s ∂volume) = -(∫ s in Ici (1 : ℝ), F s ∂volume) := by
            exact MeasureTheory.integral_neg F
          have hsign :
              -(2 * (∫ s in Ici (1 : ℝ), -F s ∂volume)) = 2 * (∫ t in Ici (1 : ℝ), F t) := by
            calc
              -(2 * (∫ s in Ici (1 : ℝ), -F s ∂volume)) =
                  -(2 * (-(∫ s in Ici (1 : ℝ), F s ∂volume))) := by
                simp [hnegI]
              _ = 2 * (∫ s in Ici (1 : ℝ), F s ∂volume) := by
                ring
              _ = 2 * (∫ t in Ici (1 : ℝ), F t ∂volume) := by
                rfl
              _ = 2 * (∫ t in Ici (1 : ℝ), F t) := by
                simp (config := { failIfUnchanged := false })
          -- Avoid `simp` here: it rewrites the integration measure printing and obscures
          -- definitional equality.
          change -(2 * (∫ s in Ici (1 : ℝ), -F s ∂volume)) = 2 * (∫ t in Ici (1 : ℝ), F t)
          exact hsign

/-- Fourier permutation identity: `𝓕 I₆ = I₅`. -/
public theorem perm_I₆ : FT I₆ = I₅ := by
  -- Derive from `perm_I₅` using that `I₅` and `I₆` are even (radial) functions.
  have heven : (fun x : ℝ²⁴ ↦ (I₆) (-x)) = fun x ↦ (I₆) x := by
    funext x
    simp [I₆, mkRadial]
  have hsymm :
      (FT).symm I₆ = FT I₆ :=
    fourierTransformCLE_symm_eq_of_even (f := I₆) heven
  have h := congrArg (FT).symm perm_I₅
  simp_all

end PermI56

end

end SpherePacking.Dim24.AFourier
