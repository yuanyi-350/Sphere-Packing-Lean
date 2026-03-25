module
public import SpherePacking.Dim24.MagicFunction.B.SpecialValues.Basic
public import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU
import SpherePacking.Dim24.MagicFunction.B.Defs.J3Smooth
import SpherePacking.Dim24.MagicFunction.B.Defs.J2Smooth
import SpherePacking.Dim24.MagicFunction.B.Defs.J4Smooth


/-!
# Factorization of `J₁' + J₃' + J₅'`

This file rewrites the sum `J₁' u + J₃' u + J₅' u` so that its dependence on `expU u 1` is
explicit. In particular, the factor `((expU u 1)⁻¹ + expU u 1 - 2)` vanishes to second order when
`expU u 1 = 1`, which is used later to show double zeros at even parameters.

## Main statements
* `J₁'_J₃'_J₅'_factor`
* `J₁'_J₃'_J₅'_hasDerivAt_zero_of`
-/

open scoped Real
open scoped Interval

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

namespace SpecialValuesAux

section EvenU

open intervalIntegral
open MagicFunction.Parametrisations RealIntegrals

-- `expU` and its basic shift lemmas live in the shared module
-- `SpherePacking.Dim24.MagicFunction.SpecialValuesExpU`.


lemma expU_z₁'_mul (u : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    expU u (z₁' t) = expU u (z₅' t) * (expU u 1)⁻¹ := by
  have hz : z₁' t + 1 = z₅' t := z₁'_add_one_eq_z₅' (t := t) ht
  have hne : expU u 1 ≠ 0 := by simp [expU]
  simpa [hz] using (expU_add_one_mul_inv (u := u) (z := z₁' t) hne)

lemma expU_z₃'_mul (u : ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    expU u (z₃' t) = expU u (z₅' t) * expU u 1 := by
  have hz : z₃' t = z₅' t + 1 := z₃'_eq_z₅'_add_one (t := t) ht
  have hz' : z₅' t + 1 = z₃' t := hz.symm
  simpa [hz'] using (expU_add_one_mul (u := u) (z := z₅' t))

/-- Factorization of the `J₁'/J₃'/J₅'` block, isolating the dependence on `expU u 1`. -/
public lemma J₁'_J₃'_J₅'_factor (u : ℝ) :
    J₁' u + J₃' u + J₅' u =
      (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)) *
        ((expU u 1)⁻¹ + expU u 1 - 2) := by
  -- Work with the integral *without* the common `I` factor, then reinsert it at the end.
  let I0 : ℂ := ∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t)
  have hJ1 : J₁' u = (Complex.I : ℂ) * I0 * (expU u 1)⁻¹ := by
    -- Rewrite `ψT'(z₁' t)` as `ψI'(z₅' t)` and shift by `-1` in the exponential.
    dsimp [RealIntegrals.J₁', I0]
    have hcongr :
        (∫ t in (0 : ℝ)..1, ψT' (z₁' t) * expU u (z₁' t)) =
          ∫ t in (0 : ℝ)..1, ψI' (z₅' t) * (expU u (z₅' t) * (expU u 1)⁻¹) := by
      refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
      have hψ : ψT' (z₁' t) = ψI' (z₅' t) := ψT'_z₁'_eq_ψI'_z₅' (t := t) htIcc
      have hexp : expU u (z₁' t) = expU u (z₅' t) * (expU u 1)⁻¹ :=
        expU_z₁'_mul (u := u) (t := t) htIcc
      simp [hψ, hexp]
    -- Pull out `(expU u 1)⁻¹` on the right.
    have hmul :
        (∫ t in (0 : ℝ)..1, ψI' (z₅' t) * (expU u (z₅' t) * (expU u 1)⁻¹)) =
          (∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t)) * (expU u 1)⁻¹ := by
      simpa [mul_assoc] using
        (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun t : ℝ => ψI' (z₅' t) * expU u (z₅' t))
          ((expU u 1)⁻¹))
    -- Now use linearity to pull out the constant `I`.
    calc
      (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z₁' t) * expU u (z₁' t)) =
          (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1, ψT' (z₁' t) * expU u (z₁' t) := by
            have hrew :
                (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z₁' t) * expU u (z₁' t)) =
                  ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * (ψT' (z₁' t) * expU u (z₁' t)) := by
              congr with t
              simp [mul_assoc]
            rw [hrew]
            exact intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
              (a := (0 : ℝ)) (b := (1 : ℝ)) (Complex.I : ℂ)
              (fun t : ℝ => ψT' (z₁' t) * expU u (z₁' t))
      _ = (Complex.I : ℂ) * ((∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t)) * (expU u 1)⁻¹) := by
            simp [hcongr, hmul]
      _ = (Complex.I : ℂ) * I0 * (expU u 1)⁻¹ := by simp [I0, mul_assoc]
  have hJ3 : J₃' u = (Complex.I : ℂ) * I0 * expU u 1 := by
    dsimp [RealIntegrals.J₃', I0]
    have hcongr :
        (∫ t in (0 : ℝ)..1, ψT' (z₃' t) * expU u (z₃' t)) =
          ∫ t in (0 : ℝ)..1, ψI' (z₅' t) * (expU u (z₅' t) * expU u 1) := by
      refine intervalIntegral.integral_congr (μ := MeasureTheory.volume) ?_
      intro t ht
      have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
        simpa [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
      have hψ : ψT' (z₃' t) = ψI' (z₅' t) :=
        Schwartz.J3Smooth.ψT'_z₃'_eq_ψI'_z₅' (t := t) htIcc
      have hexp : expU u (z₃' t) = expU u (z₅' t) * expU u 1 :=
        expU_z₃'_mul (u := u) (t := t) htIcc
      simp [hψ, hexp]
    have hmul :
        (∫ t in (0 : ℝ)..1, ψI' (z₅' t) * (expU u (z₅' t) * expU u 1)) =
          (∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t)) * expU u 1 := by
      simpa [mul_assoc] using
        (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume)
          (a := (0 : ℝ)) (b := (1 : ℝ))
          (f := fun t : ℝ => ψI' (z₅' t) * expU u (z₅' t))
          (expU u 1))
    calc
      (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z₃' t) * expU u (z₃' t)) =
          (Complex.I : ℂ) * ∫ t in (0 : ℝ)..1, ψT' (z₃' t) * expU u (z₃' t) := by
            have hrew :
                (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψT' (z₃' t) * expU u (z₃' t)) =
                  ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * (ψT' (z₃' t) * expU u (z₃' t)) := by
              congr with t
              simp [mul_assoc]
            rw [hrew]
            exact intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
              (a := (0 : ℝ)) (b := (1 : ℝ)) (Complex.I : ℂ)
              (fun t : ℝ => ψT' (z₃' t) * expU u (z₃' t))
      _ = (Complex.I : ℂ) * ((∫ t in (0 : ℝ)..1, ψI' (z₅' t) * expU u (z₅' t)) * expU u 1) := by
            simp [hcongr, hmul]
      _ = (Complex.I : ℂ) * I0 * expU u 1 := by simp [I0, mul_assoc]
  have hJ5 : J₅' u = (-2 : ℂ) * (Complex.I : ℂ) * I0 := by
    -- Rewrite `J₅'` using the local `expU` abbreviation, then pull out the constant `I`.
    dsimp [RealIntegrals.J₅']
    have hcexp : ∀ t : ℝ,
        Complex.exp (Real.pi * Complex.I * (u : ℂ) * (z₅' t)) = expU u (z₅' t) := by
      tauto
    -- Replace the exponential factor with `expU`.
    have hJ5' :
        (∫ t in (0 : ℝ)..1,
            (Complex.I : ℂ) * ψI' (z₅' t) * Complex.exp (Real.pi * Complex.I * (u : ℂ) * (z₅' t))) =
          ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t) := by
      rfl
    -- Pull out `I` and identify the remaining integral with `I0`.
    have hI :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)) =
          (Complex.I : ℂ) * I0 := by
      -- First rewrite `I * ψI' * expU` as `I * (ψI' * expU)`.
      have hrew :
          (fun t : ℝ => (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)) =
            fun t : ℝ => (Complex.I : ℂ) * (ψI' (z₅' t) * expU u (z₅' t)) := by
        funext t
        simp [mul_assoc]
      -- Now pull the scalar out of the integral.
      rw [hrew]
      exact intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
        (a := (0 : ℝ)) (b := (1 : ℝ)) (Complex.I : ℂ)
        (fun t : ℝ => ψI' (z₅' t) * expU u (z₅' t))
    -- The definition of `I0` uses `ψI' * expU`; rewrite it in the `cexp * ψI'` form that
    -- appears after unfolding `J₅'`.
    grind only
  -- Convert back to the integral with the common `I` factor inside.
  have hI0 :
      (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)) =
        (Complex.I : ℂ) * I0 := by
    dsimp [I0]
    have hrew :
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)) =
          ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * (ψI' (z₅' t) * expU u (z₅' t)) := by
      congr with t
      simp [mul_assoc]
    rw [hrew]
    exact intervalIntegral.integral_const_mul (μ := MeasureTheory.volume)
      (a := (0 : ℝ)) (b := (1 : ℝ)) (Complex.I : ℂ)
      (fun t : ℝ => ψI' (z₅' t) * expU u (z₅' t))
  -- Assemble the factorization.
  -- Use commutativity in `ℂ` to align the product order.
  calc
    J₁' u + J₃' u + J₅' u =
        (Complex.I : ℂ) * I0 * ((expU u 1)⁻¹ + expU u 1 - 2) := by
          simp [hJ1, hJ3, hJ5]
          ring
    _ =
        (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)) *
          ((expU u 1)⁻¹ + expU u 1 - 2) := by
          -- Rewrite the left-hand product into `((I*I0) * factor)` and then substitute `hI0`.
          exact Eq.symm
            (Complex.ext
              (congrArg Complex.re
                (congrFun (congrArg HMul.hMul hI0) ((expU u 1)⁻¹ + expU u 1 - 2)))
              (congrArg Complex.im
                (congrFun (congrArg HMul.hMul hI0) ((expU u 1)⁻¹ + expU u 1 - 2))))
public instance : ContinuousSMul ℝ ℂ :=
  ⟨Complex.continuous_ofReal.comp continuous_fst |>.mul continuous_snd⟩
/-- If `expU u0 1 = 1`, then `u ↦ J₁' u + J₃' u + J₅' u` has derivative `0` at `u0`. -/
public lemma J₁'_J₃'_J₅'_hasDerivAt_zero_of (u0 : ℝ) (hu : expU u0 1 = 1) :
    HasDerivAt (fun u : ℝ => J₁' u + J₃' u + J₅' u) 0 u0 := by
  -- Use the factorization `J₁'+J₃'+J₅' = g(u) * h(u)` and note that `h` has a double zero
  -- whenever `expU u0 1 = 1`.
  let g : ℝ → ℂ :=
    fun u => ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * ψI' (z₅' t) * expU u (z₅' t)
  let w : ℝ → ℂ := fun u => expU u 1
  let c : ℂ := (Real.pi : ℂ) * Complex.I
  let h : ℝ → ℂ := fun u => (w u)⁻¹ + w u - 2
  have hfac : (fun u : ℝ => J₁' u + J₃' u + J₅' u) = fun u => g u * h u := by
    funext u
    simp [g, h, w, J₁'_J₃'_J₅'_factor (u := u), mul_assoc, mul_comm]
  have hw0 : w u0 = 1 := hu
  have hh0 : h u0 = 0 := by
    simp [h, w, hw0]
    ring
  -- Derivative of `w(u) = exp(π i u)`.
  have hw (x : ℝ) : HasDerivAt w (w x * c) x := by
    -- Work over `ℂ` and then restrict to `ℝ` via `HasDerivAt.comp_ofReal`.
    exact hasDerivAt_expU_one x
  -- `h(u) = w(u)⁻¹ + w(u) - 2` has derivative `0` at `u0` when `w u0 = 1`.
  have hh : HasDerivAt h 0 u0 := by
    -- Avoid `HasDerivAt.fun_inv` (it requires `ℝ → ℝ`): use `w(-u) = (w u)⁻¹` for the exponential.
    exact hasDerivAt_factor_even u0 hu
  -- `g` is differentiable at `u0` since it is a scalar multiple of `J₅'`.
  have hg_diff : DifferentiableAt ℝ g u0 := by
    -- `J₅'` is smooth; `g` is obtained from it by scaling.
    have hJ5 : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.J₅' := Schwartz.J5Smooth.contDiff_J₅'
    have hJ5diff : DifferentiableAt ℝ RealIntegrals.J₅' u0 :=
      (hJ5.contDiffAt (x := u0)).differentiableAt (by simp)
    -- `J₅' u = (-2) * g u`.
    have hg : g = fun u : ℝ => ((-2 : ℂ)⁻¹) * RealIntegrals.J₅' u := by
      funext u
      -- Unfold `J₅'` and `g`.
      simp [g, RealIntegrals.J₅', expU, mul_assoc, mul_left_comm, mul_comm]
    have hconst : DifferentiableAt ℝ (fun _ : ℝ => ((-2 : ℂ)⁻¹)) u0 := by
      simp
    -- Avoid `simp` rewriting away the minus sign: rewrite the goal and apply the product rule.
    rw [hg]
    change DifferentiableAt ℝ ((fun _ : ℝ => ((-2 : ℂ)⁻¹)) * RealIntegrals.J₅') u0
    exact hconst.mul hJ5diff
  have hg : HasDerivAt g (deriv g u0) u0 := hg_diff.hasDerivAt
  -- Product rule: the derivative vanishes because `h u0 = 0` and `h' u0 = 0`.
  have hprod : HasDerivAt (fun u : ℝ => g u * h u) 0 u0 := by
    have := hg.mul hh
    -- The product-rule derivative simplifies using `h u0 = 0`.
    have : HasDerivAt (fun u : ℝ => g u * h u) ((deriv g u0) * (h u0) + (g u0) * 0) u0 := by
      simpa using this
    simpa [hh0] using this
  simpa [hfac] using hprod

public lemma bProfile_hasDerivAt_of_expU_eq_one (u0 : ℝ) (hu : expU u0 1 = 1) (hu0 : 0 ≤ u0) :
    HasDerivAt bProfile (deriv (fun u : ℝ => J₂' u + J₄' u + J₆' u) u0) u0 := by
  -- The `J₁+J₃+J₅` contribution has derivative `0` at even `u`.
  let f135 : ℝ → ℂ := fun u : ℝ => J₁' u + J₃' u + J₅' u
  let f246 : ℝ → ℂ := fun u : ℝ => J₂' u + J₄' u + J₆' u
  have hb : bProfile = fun u : ℝ => f135 u + f246 u := by
    funext u
    simp [bProfile, RealIntegrals.b', f135, f246, add_assoc, add_left_comm]
  have h135 : HasDerivAt f135 0 u0 := J₁'_J₃'_J₅'_hasDerivAt_zero_of (u0 := u0) hu
  have hf246_diff : DifferentiableAt ℝ f246 u0 := by
    have hJ2 : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.J₂' := Schwartz.J2Smooth.contDiff_J₂'
    have hJ4 : ContDiff ℝ (⊤ : ℕ∞) RealIntegrals.J₄' := Schwartz.J4Smooth.contDiff_J₄'
    have h2 : DifferentiableAt ℝ RealIntegrals.J₂' u0 :=
      (hJ2.contDiffAt (x := u0)).differentiableAt (by simp)
    have h4 : DifferentiableAt ℝ RealIntegrals.J₄' u0 :=
      (hJ4.contDiffAt (x := u0)).differentiableAt (by simp)
    have hIoi : Set.Ioi (-1 : ℝ) ∈ nhds u0 := by
      have : (-1 : ℝ) < u0 := lt_of_lt_of_le (by norm_num) hu0
      exact (isOpen_Ioi.mem_nhds this)
    have h6 : DifferentiableAt ℝ RealIntegrals.J₆' u0 :=
      (Schwartz.J6Smooth.contDiffOn_J₆'_Ioi_neg1.contDiffAt (x := u0) hIoi).differentiableAt
        (by simp)
    simpa [f246, add_assoc] using (h2.add (h4.add h6))
  have h246 : HasDerivAt f246 (deriv f246 u0) u0 := hf246_diff.hasDerivAt
  have hsum : HasDerivAt (fun u : ℝ => f135 u + f246 u) (deriv f246 u0) u0 := by
    simpa using (h135.add h246)
  simpa [hb, f246] using hsum


end SpecialValuesAux.EvenU
end

end SpherePacking.Dim24
