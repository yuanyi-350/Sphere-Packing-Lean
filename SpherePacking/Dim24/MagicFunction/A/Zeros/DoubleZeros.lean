module
public import SpherePacking.Dim24.MagicFunction.A.Defs
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Radial
import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Final.Values
import SpherePacking.Dim24.MagicFunction.A.Zeros.ContourIdentities
import SpherePacking.Dim24.MagicFunction.A.LaplaceZeros
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.HolomorphyHelpers
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailBounds
import SpherePacking.Dim24.MagicFunction.A.LaplaceZerosTail.TailDeform
import SpherePacking.Dim24.MagicFunction.SpecialValuesExpU
import SpherePacking.Dim24.MagicFunction.A.Eigen.Prelude


/-!
# Double zeros for `a` at even Leech radii

This file packages the "double zero" input needed in the analytic construction of the `+1`
eigenfunction: the radial Schwartz function `a` vanishes at the Leech radii, and for `k > 2` the
one-variable profile has vanishing derivative at `r = √(2k)`.

## Main statements
* `ZerosAux.a_zero_of_norm_sq_eq_two_mul`
* `ZerosAux.aRadial_hasDerivAt_zero_of_two_lt`
-/


open Complex

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace SpherePacking.Dim24

noncomputable section

open UpperHalfPlane MatrixGroups


namespace ZerosAux

open scoped Real
open scoped UpperHalfPlane
open SpecialValuesAux
open MagicFunction.Parametrisations
open RealIntegrals RealIntegrals.ComplexIntegrands
open Complex Set MeasureTheory Filter intervalIntegral
open scoped Interval Topology

lemma a_apply (x : ℝ²⁴) : a x = aProfile (‖x‖ ^ 2) := by
  simp [Dim24.a, Dim24.aAux]

lemma aProfile_four : aProfile (4 : ℝ) = 0 :=
  by simpa using (SpherePacking.Dim24.aProfile_four : aProfile (4 : ℝ) = 0)


/-!
### Double zeros for the profile at even integers `> 4`

The contour/Laplace representation shows that for `u > 4`, `aProfile u` factors as
`(exp(π i u) + exp(-π i u) - 2) * (...integral...)`. The even-integer factor has a double zero, so
the derivative of `aProfile` vanishes at `u = 2k` for `k > 2`.
-/

lemma hasDerivAt_mul_of_hasDerivAt_zero_of_continuousAt
    {f g : ℝ → ℂ} {x0 : ℝ} (hf : HasDerivAt f 0 x0) (hf0 : f x0 = 0) (hg : ContinuousAt g x0) :
    HasDerivAt (fun x : ℝ => f x * g x) 0 x0 := by
  -- Reduce to a little‑o estimate using boundedness of `g` near `x0`.
  rw [hasDerivAt_iff_isLittleO] at hf ⊢
  have hf' : (fun x : ℝ => f x) =o[𝓝 x0] fun x : ℝ => x - x0 := by
    -- From `hf` we get `f x - f x0 = o(x-x0)`, and `f x0 = 0`.
    simp_all
  -- A local bound `‖g x‖ ≤ ‖g x0‖ + 1`.
  have hgbound :
      ∀ᶠ x in 𝓝 x0, ‖g x‖ ≤ ‖g x0‖ + 1 := by
    have hlt : ∀ᶠ x in 𝓝 x0, ‖g x‖ < ‖g x0‖ + 1 :=
      (hg.norm.tendsto).eventually (Iio_mem_nhds (by linarith [show (0 : ℝ) < 1 by norm_num]))
    exact hlt.mono fun _ hx => le_of_lt hx
  -- Unfold `IsLittleO` into the usual `∀ c>0, ...` form.
  rw [Asymptotics.isLittleO_iff] at hf' ⊢
  intro c hc
  have hMpos : 0 < ‖g x0‖ + 1 := by linarith [norm_nonneg (g x0)]
  have hfM := (hf' (c := c / (‖g x0‖ + 1)) (div_pos hc hMpos))
  filter_upwards [hfM, hgbound] with x hxF hxG
  have hnorm_mul : ‖f x * g x‖ ≤ ‖f x‖ * ‖g x‖ :=
    (norm_mul (f x) (g x)).le
  have hxF' : ‖f x‖ * ‖g x‖ ≤ ((c / (‖g x0‖ + 1)) * ‖x - x0‖) * ‖g x‖ :=
    mul_le_mul_of_nonneg_right hxF (norm_nonneg _)
  have hxG' :
      ((c / (‖g x0‖ + 1)) * ‖x - x0‖) * ‖g x‖ ≤
        ((c / (‖g x0‖ + 1)) * ‖x - x0‖) * (‖g x0‖ + 1) := by
    exact mul_le_mul_of_nonneg_left hxG (by positivity)
  have hstep :
      ‖f x * g x‖ ≤ (c / (‖g x0‖ + 1)) * ‖x - x0‖ * (‖g x0‖ + 1) := by
    have := hnorm_mul.trans (hxF'.trans hxG')
    simpa [mul_assoc] using this
  -- `f x0 = 0`, so the subtraction term vanishes.
  have : ‖f x * g x - (f x0 * g x0)‖ ≤ c * ‖x - x0‖ := by
    have hne : (‖g x0‖ + 1) ≠ 0 := ne_of_gt hMpos
    have hcancel :
        (c / (‖g x0‖ + 1)) * ‖x - x0‖ * (‖g x0‖ + 1) = c * ‖x - x0‖ := by
      -- Cancel the local bound without `field_simp`.
      simp [div_eq_mul_inv, mul_left_comm, mul_comm, hne]
    have hstep' : ‖f x * g x‖ ≤ c * ‖x - x0‖ := by
      -- Rewrite the RHS of `hstep` using `hcancel` (without rewriting the LHS).
      exact hcancel ▸ hstep
    have hx0 : f x0 * g x0 = 0 := by simp [hf0]
    -- Rewrite the subtraction term to `‖f x * g x‖`.
    rw [hx0, sub_zero]
    exact hstep'
  simpa [sub_eq_add_neg, add_assoc] using this

lemma continuousAt_integral_Ioi_one_Φ₅' (u0 : ℝ) (hu0 : 4 < u0) :
    ContinuousAt (fun u : ℝ => ∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)) u0 := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  -- Use dominated convergence on a neighborhood where `u ≥ uL > 4`.
  set uL : ℝ := (u0 + 4) / 2
  have huL : 4 < uL := by
    dsimp [uL]
    linarith
  have huL_lt : uL < u0 := by
    dsimp [uL]
    linarith
  let F : ℝ → ℝ → ℂ := fun u t => Φ₅' u ((t : ℂ) * Complex.I)
  have hF_meas : ∀ᶠ u in 𝓝 u0, AEStronglyMeasurable (F u) μ := by
    filter_upwards [isOpen_Ioi.mem_nhds hu0] with u hu
    have hInt :
        Integrable (fun t : ℝ => Φ₅' u ((t : ℂ) * Complex.I)) (volume.restrict (Set.Ioi (1 : ℝ))) :=
      LaplaceZerosTail.TailDeform.integrable_imag_axis_Φ₅' (u := u) hu
    simpa [F, μ] using hInt.aestronglyMeasurable
  have h_bound : ∀ᶠ u in 𝓝 u0, ∀ᵐ t ∂μ, ‖F u t‖ ≤ ‖F uL t‖ := by
    filter_upwards [isOpen_Ioi.mem_nhds huL_lt] with u hu
    have hu_ge : uL ≤ u := le_of_lt hu
    refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_of_lt ht)
    set z : ℂ := (t : ℂ) * Complex.I
    have hzIm : z.im = t := by simp [z]
    have hnorm_u :
        ‖Φ₅' u z‖ =
          ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ * Real.exp (-Real.pi * u * z.im) := by
      -- Only the `cexp` factor depends on `u`.
      have :
          Φ₅' u z =
            (varphi' (-1 / z) * z ^ (10 : ℕ)) * cexp (Real.pi * Complex.I * (u : ℂ) * z) := by
        simp [Φ₅', mul_assoc]
      calc
        ‖Φ₅' u z‖ =
            ‖(varphi' (-1 / z) * z ^ (10 : ℕ)) *
                cexp (Real.pi * Complex.I * (u : ℂ) * z)‖ := by
            simp [this]
        _ =
            ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ *
              ‖cexp (Real.pi * Complex.I * (u : ℂ) * z)‖ := by
            simp [mul_assoc]
        _ =
            ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ *
              Real.exp (-Real.pi * u * z.im) := by
            simp [LaplaceZerosTail.TailDeform.norm_cexp_pi_I_mul_u_mul (u := u) (z := z)]
    have hnorm_uL :
        ‖Φ₅' uL z‖ =
          ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ * Real.exp (-Real.pi * uL * z.im) := by
      have :
          Φ₅' uL z =
            (varphi' (-1 / z) * z ^ (10 : ℕ)) * cexp (Real.pi * Complex.I * (uL : ℂ) * z) := by
        simp [Φ₅', mul_assoc]
      calc
        ‖Φ₅' uL z‖ =
            ‖(varphi' (-1 / z) * z ^ (10 : ℕ)) *
                cexp (Real.pi * Complex.I * (uL : ℂ) * z)‖ := by
            simp [this]
        _ =
            ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ *
              ‖cexp (Real.pi * Complex.I * (uL : ℂ) * z)‖ := by
            simp [mul_assoc]
        _ =
            ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ *
              Real.exp (-Real.pi * uL * z.im) := by
            simp [LaplaceZerosTail.TailDeform.norm_cexp_pi_I_mul_u_mul (u := uL) (z := z)]
    have hexp :
        Real.exp (-Real.pi * u * t) ≤ Real.exp (-Real.pi * uL * t) := by
      have ht0 : 0 ≤ t := le_of_lt htpos
      have hmul : Real.pi * (uL * t) ≤ Real.pi * (u * t) := by
        have h := mul_le_mul_of_nonneg_right hu_ge ht0
        exact mul_le_mul_of_nonneg_left h Real.pi_pos.le
      have hneg : -(Real.pi * (u * t)) ≤ -(Real.pi * (uL * t)) := neg_le_neg hmul
      have hexp' : (-Real.pi * u * t : ℝ) ≤ -Real.pi * uL * t := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hneg
      exact (Real.exp_le_exp.2 hexp')
    have hmul :
        ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ * Real.exp (-Real.pi * u * z.im) ≤
          ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ * Real.exp (-Real.pi * uL * z.im) := by
      have hnonneg : 0 ≤ ‖varphi' (-1 / z) * z ^ (10 : ℕ)‖ := norm_nonneg _
      simpa [hzIm] using (mul_le_mul_of_nonneg_left (by simpa [hzIm] using hexp) hnonneg)
    -- Rewrite back to `F`.
    simpa [F, z, hnorm_u, hnorm_uL] using hmul
  have hIntBound :
      Integrable (fun t : ℝ => ‖F uL t‖) μ := by
    have hInt :
        Integrable (fun t : ℝ => Φ₅' uL ((t : ℂ) * Complex.I))
          (volume.restrict (Set.Ioi (1 : ℝ))) :=
      LaplaceZerosTail.TailDeform.integrable_imag_axis_Φ₅' (u := uL) huL
    simpa [F, μ] using hInt.norm
  have h_cont : ∀ᵐ t ∂μ, ContinuousAt (fun u : ℝ => F u t) u0 := by
    refine Filter.Eventually.of_forall ?_
    intro t
    -- Only the exponential depends on `u`.
    have hexp :
        ContinuousAt
          (fun u : ℝ => cexp (Real.pi * Complex.I * (u : ℂ) * ((t : ℂ) * Complex.I))) u0 := by
      fun_prop
    have hconst :
        ContinuousAt
          (fun _u : ℝ =>
            varphi' (-1 / ((t : ℂ) * Complex.I)) * ((t : ℂ) * Complex.I) ^ (10 : ℕ)) u0 :=
      continuousAt_const
    simpa [F, Φ₅', mul_assoc] using (continuousAt_const.mul (continuousAt_const.mul hexp))
  -- Apply dominated convergence.
  exact continuousAt_of_dominated hF_meas h_bound hIntBound h_cont

lemma aProfile_hasDerivAt_zero_two_mul_nat_of_two_lt (k : ℕ) (hk : 2 < k) :
    HasDerivAt aProfile 0 ((2 : ℝ) * k) := by
  set u0 : ℝ := (2 : ℝ) * k
  have hu0 : expU u0 1 = 1 := by simpa [u0] using expU_two_mul_nat_one (k := k)
  have hu0_4 : 4 < u0 := by
    have hk' : (2 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have : (4 : ℝ) < (2 : ℝ) * (k : ℝ) := by linarith
    simpa [u0] using this
  let Vseg : ℝ → ℂ := fun u : ℝ => ∫ t in (0 : ℝ)..1, Φ₅' u ((t : ℂ) * Complex.I)
  let Vtail : ℝ → ℂ := fun u : ℝ => ∫ t in Set.Ioi (1 : ℝ), Φ₅' u ((t : ℂ) * Complex.I)
  let W : ℝ → ℂ := fun u : ℝ => Vseg u + Vtail u
  let coeff : ℝ → ℂ := fun u : ℝ => (expU u 1)⁻¹ + expU u 1 - 2
  have hcoeffDeriv : HasDerivAt coeff 0 u0 := by
    simpa [coeff] using (hasDerivAt_factor_even (u0 := u0) hu0)
  have hcoeff0 : coeff u0 = 0 := by simpa [coeff] using (coeff_two_mul_nat (k := k))
  have hVsegCont : ContinuousAt Vseg u0 := by
    -- `Vseg` is a constant multiple of `I₅'`, hence smooth.
    have hI5 :
        ∀ u : ℝ, RealIntegrals.I₅' u = (-2 : ℂ) * (Complex.I : ℂ) * Vseg u := by
      intro u
      -- Expand `I₅'` and rewrite `z₅' t = i t` on `[0,1]`.
      have hparam :
          (∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₅' u (z₅' t)) =
              ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₅' u ((t : ℂ) * Complex.I) := by
        refine intervalIntegral.integral_congr ?_
        intro t ht
        have h01 : (0 : ℝ) ≤ 1 := by norm_num
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le h01] using ht
        simp [z₅'_eq_of_mem (t := t) ht', mul_comm]
      -- Use `intervalIntegral.integral_const_mul` to pull out `I`.
      have hmain :
          ∫ t in (0 : ℝ)..1, RealIntegrands.Φ₅ u t =
              (Complex.I : ℂ) * Vseg u := by
        -- Rewrite the parametrization.
        have :
            (∫ t in (0 : ℝ)..1, RealIntegrands.Φ₅ u t) =
                ∫ t in (0 : ℝ)..1, (Complex.I : ℂ) * Φ₅' u ((t : ℂ) * Complex.I) := by
          simp [RealIntegrands.Φ₅, hparam]
        -- Pull out the constant factor.
        simpa [Vseg, intervalIntegral.integral_const_mul, mul_assoc] using this
      -- Finish by unfolding `I₅'`.
      simp [RealIntegrals.I₅', hmain, mul_assoc]
    set c : ℂ := ((-2 : ℂ) * (Complex.I : ℂ))⁻¹
    have hVsegEq : Vseg = fun u : ℝ => c * RealIntegrals.I₅' u := by
      funext u
      have hci : ((-2 : ℂ) * (Complex.I : ℂ)) ≠ 0 := by
        simp
      have hI5u : RealIntegrals.I₅' u = (-2 : ℂ) * (Complex.I : ℂ) * Vseg u := hI5 u
      -- Multiply by the inverse coefficient.
      exact (eq_inv_mul_iff_mul_eq₀ hci).mpr (id (Eq.symm hI5u))
    have hI5cont : ContinuousAt (fun u : ℝ => RealIntegrals.I₅' u) u0 :=
      Schwartz.I5Smooth.contDiff_I₅'.continuous.continuousAt
    -- Conclude by rewriting and using continuity of scalar multiplication.
    simpa [hVsegEq] using (continuousAt_const.mul hI5cont)
  have hVtailCont : ContinuousAt Vtail u0 :=
    (continuousAt_integral_Ioi_one_Φ₅' (u0 := u0) hu0_4)
  have hWCont : ContinuousAt W u0 := by
    simpa [W] using (hVsegCont.add hVtailCont)
  have hMul : HasDerivAt (fun u : ℝ => coeff u * W u) 0 u0 :=
    hasDerivAt_mul_of_hasDerivAt_zero_of_continuousAt hcoeffDeriv hcoeff0 hWCont
  have hMulI : HasDerivAt (fun u : ℝ => (Complex.I : ℂ) * (coeff u * W u)) 0 u0 := by
    simpa using (hMul.const_mul (Complex.I : ℂ))
  -- Identify `aProfile` with the Laplace factorization in a neighborhood of `u0` (where `u > 4`).
  have hEq :
      (fun u : ℝ => aProfile u) =ᶠ[𝓝 u0] fun u : ℝ =>
        (Complex.I : ℂ) *
          (((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
                Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ))) *
            (Vseg u + Vtail u)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu0_4] with u hu
    have h135 := LaplaceZeros.I₁'_add_I₃'_add_I₅'_eq_imag_axis (u := u)
    have h246 := LaplaceZerosTail.TailDeform.I₂'_add_I₄'_add_I₆'_eq_imag_axis (u := u) hu
    -- Expand `aProfile` and group into the two blocks.
    dsimp [aProfile, RealIntegrals.a']
    calc
      RealIntegrals.I₁' u + RealIntegrals.I₂' u + RealIntegrals.I₃' u + RealIntegrals.I₄' u +
            RealIntegrals.I₅' u + RealIntegrals.I₆' u =
          (RealIntegrals.I₁' u + RealIntegrals.I₃' u + RealIntegrals.I₅' u) +
            (RealIntegrals.I₂' u + RealIntegrals.I₄' u + RealIntegrals.I₆' u) := by
            ac_rfl
      _ =
          (Complex.I : ℂ) *
              ((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
                    Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
                Vseg u) +
            (Complex.I : ℂ) *
              ((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
                    Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
                Vtail u) := by
            simp [h135, h246, Vseg, Vtail, mul_assoc]
      _ =
          (Complex.I : ℂ) *
            ((Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
                  Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) *
              (Vseg u + Vtail u)) := by
            ring
  -- Replace the `Complex.exp` coefficient by `coeff`.
  have hCoeffEq :
      (fun u : ℝ =>
          (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
                Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ))) = fun u : ℝ =>
          coeff u := by
    funext u
    -- Rewrite the `Complex.exp` terms in the coefficient as `expU`.
    have hExpU : expU u (1 : ℂ) = Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) := by
      unfold expU
      simp [mul_left_comm, mul_comm]
    -- `exp(-x) = (exp x)⁻¹`.
    unfold coeff
    -- The only difference is commutativity of addition between `exp` and its inverse.
    simp [hExpU, Complex.exp_neg, sub_eq_add_neg, add_assoc, add_comm]
  have hEq' :
      (fun u : ℝ => aProfile u) =ᶠ[𝓝 u0] fun u : ℝ =>
        (Complex.I : ℂ) * (coeff u * W u) := by
    have := hEq
    -- Rewrite coefficient and `W`.
    refine this.trans ?_
    filter_upwards with u
    have hCoeffU :
        (Complex.exp (((Real.pi * u : ℝ) : ℂ) * Complex.I) +
              Complex.exp (-(((Real.pi * u : ℝ) : ℂ) * Complex.I)) - (2 : ℂ)) = coeff u := by
      -- Evaluate the function identity `hCoeffEq` at `u`.
      simpa using congrArg (fun f : ℝ → ℂ => f u) hCoeffEq
    lia
  exact hMulI.congr_of_eventuallyEq hEq'
/-- The zero set of `a` on the Leech radii `‖x‖ = √(2k)` for integers `k ≥ 2`.

Faithfulness note:
In `dim_24.tex` (around (2.16)-(2.17)), for `k > 2` the `sin(π r^2/2)^2` factor forces a *double*
zero (in the one-variable profile) at `r = √(2k)` because the remaining Laplace term is analytic.
At `k = 2` (i.e. `r = 2`) there is a pole/zero cancellation, and the root is only *simple* in `r`
(the paper gives `a(2)=0` and `a'(2) ≠ 0`).
-/
public theorem a_zero_of_norm_sq_eq_two_mul (k : ℕ) (hk : 2 ≤ k) :
    ∀ x : ℝ²⁴, ‖x‖ ^ 2 = (2 : ℝ) * k → a x = 0 := by
  /- Proof sketch:
  - For `k > 2`, use the analytic continuation formula (paper (2.16)): the integral term is analytic
    at `r = √(2k)` and the `sin(π r^2/2)^2` factor vanishes.
  - For `k = 2`, use the established special value `aRadial 2 = 0` (pole/zero cancellation). -/
  intro x hx
  have ha : a x = aProfile (‖x‖ ^ 2) := ZerosAux.a_apply (x := x)
  rw [ha, hx]
  by_cases hk2 : k = 2
  · subst hk2
    -- `aProfile 4 = 0` from the special value `aRadial_two`.
    have h : (2 : ℝ) * 2 = (4 : ℝ) := by norm_num
    simpa [h] using (ZerosAux.aProfile_four : aProfile (4 : ℝ) = 0)
  · have hk' : 2 < k := lt_of_le_of_ne hk (Ne.symm hk2)
    simpa using (ZerosAux.aProfile_two_mul_nat_of_two_lt (k := k) hk')

/-- For `k > 2`, the one-variable profile has at least a double root at `r = √(2k)`. -/
public theorem aRadial_hasDerivAt_zero_of_two_lt (k : ℕ) (hk : 2 < k) :
    HasDerivAt aRadial 0 (Real.sqrt ((2 : ℝ) * k)) := by
  /- Proof sketch:
  From the analytic continuation formula for `a(r)` (paper (2.16)), for `k>2` the non-sine factor is
  analytic at `r=√(2k)`. The `sin(π r^2/2)^2` factor then enforces vanishing to second order in `r`.
  -/
  -- Reduce to the profile in the variable `u = r^2`.
  have haEq : aRadial = fun r : ℝ => aProfile (r ^ 2) := by
    funext r
    simp [aRadial, ZerosAux.a_apply, axisVec, pow_two]
  set r0 : ℝ := Real.sqrt ((2 : ℝ) * k)
  have hr0sq : r0 ^ 2 = (2 : ℝ) * k := by
    have : 0 ≤ ((2 : ℝ) * k) := by positivity
    simpa [r0] using (Real.sq_sqrt this)
  have haProf : HasDerivAt aProfile 0 ((2 : ℝ) * k) :=
    ZerosAux.aProfile_hasDerivAt_zero_two_mul_nat_of_two_lt (k := k) hk
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r0) r0 := by
    simpa [pow_two, two_mul, mul_assoc] using (hasDerivAt_pow 2 r0)
  have haProf' : HasDerivAt aProfile 0 (r0 ^ 2) := by simpa [hr0sq] using haProf
  have hcomp : HasDerivAt (fun r : ℝ => aProfile (r ^ 2)) 0 r0 := by
    simpa using (haProf'.scomp (x := r0) (h := fun r : ℝ => r ^ 2) hsq)
  simpa [haEq] using hcomp

end ZerosAux


end

end SpherePacking.Dim24
