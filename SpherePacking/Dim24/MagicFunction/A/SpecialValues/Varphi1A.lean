module
public import SpherePacking.Dim24.MagicFunction.A.SpecialValues.Aux04
public import SpherePacking.ForMathlib.SigmaBounds
public import SpherePacking.ForMathlib.SigmaSummability
public import SpherePacking.ForMathlib.SpecificLimits
import SpherePacking.ModularForms.QExpansion
import SpherePacking.ModularForms.DimensionFormulas
import SpherePacking.ModularForms.Lv1Lv2Identities
import SpherePacking.ForMathlib.ExpPiIMulMulI


/-!
# `q`-asymptotics for `varphi₁` at `i∞`

To evaluate the even special values of `aProfile` in `dim_24.tex`, we move a period integral to
height `m → ∞` and use `atImInfty` limits for modular forms and for `varphi₁`.

## Main definitions
* `q`

## Main statements
* `tendsto_Delta_div_q`, `tendsto_q_div_Delta`
* `tendsto_B_div_q`
* `tendsto_varphi₁_mul_q`
-/


namespace SpherePacking.Dim24

noncomputable section


/-!
## Asymptotics for `varphi₁` needed for the even special values

We evaluate the even special values `aProfile 2` and `aProfile 4` by moving the period integral
to height `m → ∞` and using the `atImInfty` limit of `varphi₁ z * exp(2π i z)`.

The key inputs are:
- the modular identity `E₄^3 - E₆^2 = 1728 * Δ`, and
- the `q`-series asymptotics of `E₂ * E₆ - E₄^2`, obtained via Ramanujan's formula for `E₆`.
-/

namespace SpecialValuesVarphi₁Limits

open scoped Interval Real Topology BigOperators Nat ArithmeticFunction.sigma
open Filter Complex UpperHalfPlane intervalIntegral MeasureTheory Set Function
open SlashInvariantFormClass ModularFormClass

/-- The nome `q(z) = exp(2π i z)`. -/
@[expose] public def q (z : ℂ) : ℂ := cexp (2 * π * Complex.I * z)

/-- The nome `q` is never zero. -/
public lemma q_ne_zero (z : ℂ) : q z ≠ 0 := by
  simp [q]

/-- Rewrite `Δ / q` as a (bounded) Euler product, used for `atImInfty` limits. -/
public lemma Delta_div_q_eq_boundedfactor :
    (fun z : ℍ => (Δ z) / q (z : ℂ)) =
      fun z : ℍ => ∏' n : ℕ, (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24 := by
  funext z
  simp [q, Δ, div_eq_mul_inv, mul_left_comm, mul_comm]

/-- `Δ / q → 1` as `z → i∞`. -/
public lemma tendsto_Delta_div_q :
    Tendsto (fun z : ℍ => (Δ z) / q (z : ℂ)) atImInfty (𝓝 (1 : ℂ)) := by
  simpa [Delta_div_q_eq_boundedfactor] using (Delta_boundedfactor : Tendsto _ atImInfty (𝓝 (1 : ℂ)))

/-- `q / Δ → 1` as `z → i∞`. -/
public lemma tendsto_q_div_Delta :
    Tendsto (fun z : ℍ => q (z : ℂ) / (Δ z)) atImInfty (𝓝 (1 : ℂ)) := by
  have h : Tendsto (fun z : ℍ => (Δ z) / q (z : ℂ)) atImInfty (𝓝 (1 : ℂ)) := tendsto_Delta_div_q
  -- Use inversion: `q/Δ = ((Δ/q)⁻¹)`.
  have hinv :
      Tendsto (fun z : ℍ => ((Δ z) / q (z : ℂ))⁻¹) atImInfty (𝓝 ((1 : ℂ)⁻¹)) :=
    (Filter.Tendsto.inv₀ h (by norm_num : (1 : ℂ) ≠ 0))
  simp_all

/-!
### Relating `Δ` to `E₄` and `E₆`
-/

lemma E4_pow_three_eq_E6_sq_add_1728_mul_Delta (z : ℍ) :
    (E₄ z) ^ (3 : ℕ) = (E₆ z) ^ (2 : ℕ) + (1728 : ℂ) * (Δ z) := by
  have h : (Δ z : ℂ) = (1 / 1728 : ℂ) * ((E₄ z) ^ (3 : ℕ) - (E₆ z) ^ (2 : ℕ)) := by
    simpa [Delta_apply] using
      (Delta_apply_eq_one_div_1728_mul_E4_pow_three_sub_E6_sq (z := z))
  simp_all

/-!
### `q`-asymptotics of `E₂ * E₆ - E₄^2`
-/

/-- Divisor sum bound used to dominate `q`-series coefficients: `σ₅ n ≤ n^6`. -/
public lemma sigma_five_le_pow_six (n : ℕ) : σ 5 n ≤ n ^ 6 := by
  simpa using (SpherePacking.ForMathlib.sigma_five_le_pow_six n)

/-- Summability of the coefficients in the shifted `B/q` `q`-series. -/
public lemma summable_coeff_B_over_q :
    Summable (fun n : ℕ =>
      ‖(((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ))‖ * Real.exp (-2 * Real.pi * n)) := by
  refine
    (SpherePacking.ForMathlib.summable_norm_mul_sigma_shift_mul_exp (k := 5) (m := 6) (s := 1) ?_)
  intro n
  norm_cast
  simpa using (sigma_five_le_pow_six (n + 1))

lemma D_E₆_qexp (z : ℍ) :
    D E₆.toFun z =
      (-(504 : ℂ)) * ∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
  -- Coefficients in the q-expansion of `E₆`.
  let c : ℕ → ℂ := fun n => if n = 0 then 1 else -(504 : ℂ) * (σ 5 n : ℂ)
  -- The corresponding q-series as a function of `z ∈ ℍ`.
  let F : ℍ → ℂ := fun w => ∑' n : ℕ, c n * cexp (2 * π * Complex.I * n * w)
  have hper :
      (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma 1 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
    simp [CongruenceSubgroup.strictPeriods_Gamma]
  -- `F` sums to `E₆` (pointwise).
  have hF : ∀ w : ℍ, HasSum (fun n : ℕ => c n * cexp (2 * π * Complex.I * n * w)) (E₆ w) := by
    intro w
    have hsum := ModularFormClass.hasSum_qExpansion (f := E₆) (h := (1 : ℝ)) (by positivity) hper w
    refine HasSum.congr_fun hsum (fun n => ?_)
    have hcoeff : (qExpansion (1 : ℝ) E₆).coeff n = c n := by
      simpa [c] using congr_fun E6_q_exp n
    have hqpow :
        (Function.Periodic.qParam (1 : ℝ) (w : ℂ)) ^ n = cexp (2 * π * Complex.I * n * w) := by
      have hq : Function.Periodic.qParam (1 : ℝ) (w : ℂ) = cexp (2 * π * Complex.I * w) := by
        simp [Function.Periodic.qParam]
      rw [hq]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.exp_nat_mul (2 * π * Complex.I * w) n).symm
    simp [smul_eq_mul, hcoeff, hqpow, mul_left_comm, mul_comm]
  have hFfun : F = E₆.toFun := by
    funext w
    simpa [F] using (hF w).tsum_eq
  have hsum : Summable (fun n : ℕ => c n * cexp (2 * π * Complex.I * n * z)) :=
    (hF z).summable
  have hsum_deriv :
      ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
          ‖c n * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * k.1)‖ ≤ u n := by
    intro K hK hKc
    have him_cont : ContinuousOn (fun w : ℂ => w.im) K := Complex.continuous_im.continuousOn
    have him_pos : ∀ z ∈ K, (0 : ℝ) < z.im := fun z hz => hK hz
    obtain ⟨δ, hδ_pos, hδ_le⟩ :=
      IsCompact.exists_forall_le' (s := K) hKc him_cont (a := (0 : ℝ)) him_pos
    let r : ℝ := Real.exp (-2 * Real.pi * δ)
    have hr_nonneg : 0 ≤ r := (Real.exp_pos _).le
    have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hδ_pos])
    have hr_norm : ‖(r : ℝ)‖ < 1 := by simpa [Real.norm_of_nonneg hr_nonneg] using hr_lt_one
    let u : ℕ → ℝ := fun n => (1008 * Real.pi) * (((n : ℝ) ^ 7 : ℝ) * r ^ n)
    have hu : Summable u := by
      have hs : Summable (fun n : ℕ => ((n : ℝ) ^ 7 : ℝ) * r ^ n) :=
        summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 7 hr_norm
      exact hs.mul_left (1008 * Real.pi)
    refine ⟨u, hu, ?_⟩
    intro n k
    by_cases hn0 : n = 0
    · subst hn0
      simp [c, u]
    have hk_im : δ ≤ k.1.im := hδ_le k.1 k.2
    have hnorm_exp :
        ‖cexp (2 * π * Complex.I * (n : ℂ) * k.1)‖ ≤ r ^ n :=
      ForMathlib.norm_cexp_two_pi_I_mul_nat_mul_le_pow_of_le_im n hk_im
    have hcnorm : ‖c n‖ ≤ (504 : ℝ) * (n : ℝ) ^ 6 := by
      have hnpos : n ≠ 0 := hn0
      -- Use the divisor-sum bound `σ 5 n ≤ n^6`.
      have hsigma : (σ 5 n : ℝ) ≤ (n : ℝ) ^ (6 : ℕ) := by
        norm_cast
        simpa using (sigma_five_le_pow_six n)
      have hnormc :
          ‖c n‖ = 504 * (σ 5 n : ℝ) := by
        have : c n = -(504 : ℂ) * (σ 5 n : ℂ) := by
          simp [c, hnpos]
        simp [this]
      linarith
    have hnorm_2pin : ‖(2 : ℂ) * π * Complex.I * n‖ = 2 * Real.pi * n := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, mul_one, Complex.norm_natCast, Real.norm_of_nonneg Real.pi_pos.le]
    have hmain :
        ‖c n * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * k.1)‖ ≤ u n := by
      -- Bound each factor.
      have hn_ge : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn0)
      calc
        ‖c n * (2 * π * Complex.I * n) * cexp (2 * π * Complex.I * n * k.1)‖
            = ‖c n‖ * ‖(2 * π * Complex.I * n : ℂ)‖ * ‖cexp (2 * π * Complex.I * n * k.1)‖ := by
                simp [mul_assoc]
        _ ≤ ((504 : ℝ) * (n : ℝ) ^ 6) * (2 * Real.pi * n) * (r ^ n) := by
              have h2 :
                  ‖(2 * π * Complex.I * n : ℂ)‖ ≤ 2 * Real.pi * n :=
                ge_of_eq (id (Eq.symm hnorm_2pin))
              have hCA :
                  ‖c n‖ * ‖(2 * π * Complex.I * n : ℂ)‖ ≤
                    ((504 : ℝ) * (n : ℝ) ^ 6) * (2 * Real.pi * n) := by
                refine mul_le_mul hcnorm h2 (by positivity) (by positivity)
              have hCAB :
                  (‖c n‖ * ‖(2 * π * Complex.I * n : ℂ)‖) * ‖cexp (2 * π * Complex.I * n * k.1)‖ ≤
                    (((504 : ℝ) * (n : ℝ) ^ 6) * (2 * Real.pi * n)) *
                      ‖cexp (2 * π * Complex.I * n * k.1)‖ :=
                mul_le_mul_of_nonneg_right hCA (by positivity)
              have hB :
                  (((504 : ℝ) * (n : ℝ) ^ 6) * (2 * Real.pi * n)) *
                        ‖cexp (2 * π * Complex.I * n * k.1)‖ ≤
                      (((504 : ℝ) * (n : ℝ) ^ 6) * (2 * Real.pi * n)) * (r ^ n) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                exact hnorm_exp
              -- Reassociate and combine.
              exact
                Std.IsPreorder.le_trans
                  (‖c n‖ * ‖2 * ↑π * Complex.I * ↑n‖ *
                    ‖cexp (2 * ↑π * Complex.I * ↑n * ↑k)‖)
                  (504 * ↑n ^ 6 * (2 * π * ↑n) *
                    ‖cexp (2 * ↑π * Complex.I * ↑n * ↑k)‖)
                  (504 * ↑n ^ 6 * (2 * π * ↑n) * r ^ n) hCAB hB
        _ = (1008 * Real.pi) * ((n : ℝ) ^ 7 * r ^ n) := by
              -- arithmetic
              ring_nf
        _ = u n := by
              simp [u, mul_assoc, mul_left_comm, mul_comm]
    simpa [mul_assoc] using hmain
  have hDF :
      D F z = ∑' n : ℕ, (n : ℂ) * c n * cexp (2 * π * Complex.I * n * z) := by
    exact D_qexp_tsum c z hsum_deriv
  -- Rewrite the nat sum as an `ℕ+` sum and simplify coefficients.
  have htail :
      (∑' n : ℕ, (n : ℂ) * c n * cexp (2 * π * Complex.I * n * z)) =
        (-(504 : ℂ)) * ∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
    let f : ℕ → ℂ := fun n => (n : ℂ) * c n * cexp (2 * π * Complex.I * n * z)
    have hf0 : f 0 = 0 := by simp [f, c]
    have htsum : (∑' n : ℕ, f n) = ∑' n : ℕ+, f n := by
      simpa using (tsum_pNat (f := f) hf0).symm
    have hf_pos : ∀ n : ℕ+, f n =
        (-(504 : ℂ)) * ((n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z)) := by
      intro n
      have : c (n : ℕ) = -(504 : ℂ) * (σ 5 n : ℂ) := by
        simp [c, n.pos.ne']
      simp [f, this, mul_assoc, mul_left_comm, mul_comm]
    calc
      (∑' n : ℕ, (n : ℂ) * c n * cexp (2 * π * Complex.I * n * z)) =
          ∑' n : ℕ+, f n := by
            simpa [f] using htsum
      _ = ∑' n : ℕ+, (-(504 : ℂ)) * ((n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z)) := by
            exact tsum_congr hf_pos
      _ = (-(504 : ℂ)) * ∑' n : ℕ+, (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
            -- Pull the constant outside the `tsum`.
            exact tsum_mul_left
  -- Use the computed `D F` formula and rewrite the series, then replace `F` by `E₆`.
  simpa [hFfun] using (hDF.trans htail)

/-- `q`-series expression for `E₂ * E₆ - E₄^2` (Ramanujan's derivative formula for `E₆`). -/
public lemma E₂_mul_E₆_sub_E₄_sq (z : ℍ) :
    (E₂ z) * (E₆ z) - (E₄ z) * (E₄ z) =
      (-(1008 : ℂ)) * ∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
  -- Ramanujan formula: `D E₆ = 1/2 * (E₂E₆ - E₄²)`.
  have hRam := congrArg (fun f : ℍ → ℂ => f z) ramanujan_E₆
  -- Solve for `E₂E₆ - E₄² = 2 * D E₆`, then substitute the q-series for `D E₆`.
  have h1 :
      (E₂ z) * (E₆ z) - (E₄ z) * (E₄ z) = (2 : ℂ) * D E₆.toFun z := by
    -- `hRam` gives `D E₆ z = 2⁻¹ * (...)`.
    simp_all
  -- Insert the q-series for `D E₆`.
  have hD := D_E₆_qexp (z := z)
  -- `2 * (-(504)) = -(1008)`.
  have hcoef : (2 : ℂ) * (-(504 : ℂ)) = (-(1008 : ℂ)) := by norm_num
  calc
    (E₂ z) * (E₆ z) - (E₄ z) * (E₄ z) = (2 : ℂ) * D E₆.toFun z := h1
    _ = (2 : ℂ) * (-(504 : ℂ)) *
          ∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
          -- Reassociate `2 * (-(504) * S)` into `2 * (-(504)) * S`.
          simpa [mul_assoc] using congrArg (fun t : ℂ => (2 : ℂ) * t) hD
    _ = (-(1008 : ℂ)) * ∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * n * z) := by
          simp [hcoef, mul_assoc]

/-- Leading coefficient of `((E₂*E₆ - E₄^2) / q)` at `i∞`: tends to `-1008`. -/
public lemma tendsto_B_div_q :
    Tendsto (fun z : ℍ => ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ)) atImInfty
      (𝓝 (-(1008 : ℂ))) := by
  -- Write `B / q` as a `q`-series with constant term `-1008`.
  let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ))
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    simpa [a] using summable_coeff_B_over_q
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n)) atImInfty (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have ha0 : a 0 = (1 : ℂ) := by simp [a]
  have hseries' :
      Tendsto (fun z : ℍ => (-(1008 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 ((-(1008 : ℂ)) * (a 0))) :=
    tendsto_const_nhds.mul hseries
  have hconst : (-(1008 : ℂ)) * a 0 = (-(1008 : ℂ)) := by simp [ha0]
  have hseries'' :
      Tendsto (fun z : ℍ => (-(1008 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (-(1008 : ℂ))) := by
    simpa [hconst] using hseries'
  have hB_eq (z : ℍ) :
      ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ) =
        (-(1008 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n) := by
    have hz : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hB :
        (E₂ z) * (E₆ z) - (E₄ z) * (E₄ z) =
          (-(1008 : ℂ)) *
            ∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (E₂_mul_E₆_sub_E₄_sq z)
    have hshift :
        (∑' (n : ℕ+),
            ((n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)) =
          ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      have hpnat :
          (∑' (n : ℕ+),
              ((n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)) =
            ∑' n : ℕ,
              (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ) *
                    cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ) := by
        simpa using
          (tsum_pnat_eq_tsum_succ
            (f := fun n : ℕ =>
              ((n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)))
      rw [hpnat]
      refine tsum_congr fun n => ?_
      have hexp :
          cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) =
            q (z : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
        have harg :
            (2 * π * Complex.I * (z : ℂ) * ((n : ℂ) + 1)) =
              (2 * π * Complex.I * (z : ℂ)) + (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
          ring_nf
        calc
          cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) =
              cexp (2 * π * Complex.I * (z : ℂ) * ((n : ℂ) + 1)) := by
                simp [Nat.cast_add, Nat.cast_one]
          _ = cexp ((2 * π * Complex.I * (z : ℂ)) + (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) := by
                simp [harg]
          _ = cexp (2 * π * Complex.I * (z : ℂ)) *
                cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
                simp [Complex.exp_add, mul_left_comm, mul_comm]
          _ = q (z : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
                simp [q, mul_left_comm, mul_comm]
      dsimp [a]
      have hdiv :
          cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ) =
            cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
        rw [hexp]
        field_simp [hz]
      have hmul :
          ((((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) *
                cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ) =
            (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) *
              (cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ)) := by
        ring
      calc
        ((((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) *
              cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ) =
            (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) *
              (cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ)) := hmul
        _ = (((n + 1 : ℕ) : ℂ) * (σ 5 (n + 1) : ℂ)) *
              cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by rw [hdiv]
    calc
      ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ)
          = (-(1008 : ℂ)) *
              ((∑' (n : ℕ+), (n : ℂ) * (σ 5 n : ℂ) *
                    cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)) := by
              -- Pull the scalar factor out of the division.
              grind only
      _ = (-(1008 : ℂ)) *
            ∑' (n : ℕ+),
              ((n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) /
                q (z : ℂ) := by
            simpa using
              congrArg (fun t : ℂ => (-(1008 : ℂ)) * t)
                (tsum_div_const (f := fun n : ℕ+ =>
                      (n : ℂ) * (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)))
                    (a := q (z : ℂ))).symm
      _ = (-(1008 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
            simp [hshift]
  exact (tendsto_congr hB_eq).mpr hseries''

/-- Rewrite `varphi₁` in terms of `E₂`, `E₄`, `E₆`, and `Δ`. -/
public lemma varphi₁_rewrite (z : ℍ) :
    Dim24.varphi₁ z =
      (288 * Complex.I) / (π : ℂ) * (E₆ z) * ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / (Δ z) ^ (2 : ℕ) +
      (1016064 * Complex.I) / (π : ℂ) * (E₂ z) / (Δ z) := by
  -- Expand and rewrite `(-49)*E₄^3 + 25*E₆^2` using `E₄^3 = E₆^2 + 1728*Δ`.
  have hE4 : (E₄ z) ^ (3 : ℕ) = (E₆ z) ^ (2 : ℕ) + (1728 : ℂ) * (Δ z) :=
    E4_pow_three_eq_E6_sq_add_1728_mul_Delta (z := z)
  have hC :
      ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) =
        (-24 : ℂ) * (E₆ z) ^ (2 : ℕ) + (-(84672 : ℂ)) * (Δ z) := by
    calc
      ((-49 : ℂ) * (E₄ z) ^ (3 : ℕ) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ)) =
          (-49 : ℂ) * ((E₆ z) ^ (2 : ℕ) + (1728 : ℂ) * (Δ z)) + (25 : ℂ) * (E₆ z) ^ (2 : ℕ) := by
            rw [hE4]
      _ = (-24 : ℂ) * (E₆ z) ^ (2 : ℕ) + (-(84672 : ℂ)) * (Δ z) := by
            ring_nf
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
  have hΔ2 : (Δ z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hΔ
  -- Now unfold `varphi₁` and simplify.
  unfold Dim24.varphi₁
  -- Rewrite the `(-49)*E₄^3 + 25*E₆^2` combination before clearing denominators.
  rw [hC]
  -- Clear denominators (`π` and powers of `Δ`) and finish by normalization.
  field_simp [hπ, hΔ, hΔ2]
  ring_nf

/-- `varphi₁ z * q(z)` tends to the explicit constant `725760 * i / π` at `i∞`. -/
public lemma tendsto_varphi₁_mul_q :
    Tendsto (fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ)) atImInfty
      (𝓝 ((725760 : ℂ) * Complex.I / (π : ℂ))) := by
  -- Use the rewritten formula and take limits termwise.
  have hE2 : Tendsto E₂ atImInfty (𝓝 (1 : ℂ)) := tendsto_E₂_atImInfty
  have hE6 : Tendsto (fun z : ℍ => E₆ z) atImInfty (𝓝 (1 : ℂ)) :=
    SpherePacking.ModularForms.tendsto_E₆_atImInfty
  have hBq :
      Tendsto (fun z : ℍ => ((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ)) atImInfty
        (𝓝 (-(1008 : ℂ))) := tendsto_B_div_q
  have hqΔ : Tendsto (fun z : ℍ => q (z : ℂ) / (Δ z)) atImInfty (𝓝 (1 : ℂ)) :=
    tendsto_q_div_Delta
  have hqΔ2 : Tendsto (fun z : ℍ => (q (z : ℂ) / (Δ z)) ^ (2 : ℕ)) atImInfty (𝓝 (1 : ℂ)) := by
    simpa using (hqΔ.pow 2)
  -- Assemble the limit.
  have hrew :
      (fun z : ℍ => Dim24.varphi₁ z * q (z : ℂ)) =
        fun z : ℍ =>
          (288 * Complex.I) / (π : ℂ) * (E₆ z) * (((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ)) *
              (q (z : ℂ) / (Δ z)) ^ (2 : ℕ)
            + (1016064 * Complex.I) / (π : ℂ) * (E₂ z) * (q (z : ℂ) / (Δ z)) := by
    funext z
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hzq : q (z : ℂ) ≠ 0 := q_ne_zero (z : ℂ)
    have hzΔ : (Δ z : ℂ) ≠ 0 := Δ_ne_zero z
    -- A purely algebraic identity; clear denominators and normalize.
    -- (We use `varphi₁_rewrite` to express `varphi₁` in terms of `Δ`.)
    have : Dim24.varphi₁ z * q (z : ℂ) =
        (288 * Complex.I) / (π : ℂ) * (E₆ z) *
            (((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ)) * (q (z : ℂ) / (Δ z)) ^ (2 : ℕ) +
          (1016064 * Complex.I) / (π : ℂ) * (E₂ z) * (q (z : ℂ) / (Δ z)) := by
      -- Clear denominators in the goal itself.
      -- (This avoids fragile intermediate rewrites between `(/)` and `(^)`.)
      have hΔ2 : (Δ z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hzΔ
      -- First rewrite away `varphi₁`.
      simp [varphi₁_rewrite (z := z), mul_add, mul_assoc, mul_left_comm, mul_comm,
        sub_eq_add_neg]
      field_simp [hπ, hzq, hzΔ, hΔ2]
    simpa using this
  have hterm1 :
      Tendsto
          (fun z : ℍ =>
            (288 * Complex.I) / (π : ℂ) * (E₆ z) *
                (((E₂ z) * (E₆ z) - (E₄ z) * (E₄ z)) / q (z : ℂ)) *
              (q (z : ℂ) / (Δ z)) ^ (2 : ℕ))
          atImInfty
          (𝓝 ((288 * Complex.I) / (π : ℂ) * (1 : ℂ) * (-(1008 : ℂ)) * (1 : ℂ))) := by
    have hconst : Tendsto (fun _z : ℍ => (288 * Complex.I) / (π : ℂ)) atImInfty
        (𝓝 ((288 * Complex.I) / (π : ℂ))) := tendsto_const_nhds
    have hprod := (hconst.mul hE6).mul (hBq) |>.mul hqΔ2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
  have hterm2 :
      Tendsto (fun z : ℍ => (1016064 * Complex.I) / (π : ℂ) * (E₂ z) * (q (z : ℂ) / (Δ z)))
        atImInfty (𝓝 ((1016064 * Complex.I) / (π : ℂ) * (1 : ℂ) * (1 : ℂ))) := by
    have hconst : Tendsto (fun _z : ℍ => (1016064 * Complex.I) / (π : ℂ)) atImInfty
        (𝓝 ((1016064 * Complex.I) / (π : ℂ))) := tendsto_const_nhds
    have hprod := (hconst.mul hE2).mul hqΔ
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
  have hsum := hterm1.add hterm2
  -- Evaluate constants.
  grind only

/-!
### First-order `q`-asymptotics

We will need first-order expansions to extract the constant term of `varphi₁` (for `aProfile 0`)
and to compute the coefficient of `q` in `varphi₁ * q`.
-/

/-- Simplify `exp(2π i z (n+1)) / q(z)` to `exp(2π i z n)`. -/
public lemma cexp_mul_succ_div_q (z : ℂ) (n : ℕ) :
    cexp (2 * π * Complex.I * z * ((n + 1 : ℕ) : ℂ)) / q z =
      cexp (2 * π * Complex.I * z * (n : ℂ)) := by
  unfold q
  have hn1 : (((n + 1 : ℕ) : ℂ)) = (n : ℂ) + 1 := by
    simp [Nat.cast_add, Nat.cast_one]
  have harg :
      (2 * π * Complex.I * z * ((n + 1 : ℕ) : ℂ)) =
        (2 * π * Complex.I * z * (n : ℂ)) + (2 * π * Complex.I * z) := by
    calc
      2 * π * Complex.I * z * ((n + 1 : ℕ) : ℂ) =
          (2 * π * Complex.I * z) * ((n : ℂ) + 1) := by
            simp [hn1, mul_assoc]
      _ = (2 * π * Complex.I * z) * (n : ℂ) + (2 * π * Complex.I * z) := by
            simp [mul_add, mul_assoc]
      _ = (2 * π * Complex.I * z * (n : ℂ)) + (2 * π * Complex.I * z) := by
            simp [mul_assoc]
  have hcast :
      (2 * π * Complex.I * z * ((n + 1 : ℕ) : ℂ)) = (2 * π * Complex.I * z * ((n : ℂ) + 1)) := by
    simp [hn1, mul_assoc]
  have hExp₁ :
      cexp (2 * π * Complex.I * z * ((n + 1 : ℕ) : ℂ)) =
        cexp (2 * π * Complex.I * z * ((n : ℂ) + 1)) := by
    exact congrArg cexp hcast
  have harg' :
      (2 * π * Complex.I * z * ((n : ℂ) + 1)) =
        (2 * π * Complex.I * z * (n : ℂ)) + (2 * π * Complex.I * z) := by
    simpa [hn1] using harg
  have hExp₂ :
      cexp (2 * π * Complex.I * z * ((n : ℂ) + 1)) =
        cexp ((2 * π * Complex.I * z * (n : ℂ)) + (2 * π * Complex.I * z)) := by
    simpa using congrArg cexp harg'
  calc
    cexp (2 * π * Complex.I * z * ((n + 1 : ℕ) : ℂ)) / cexp (2 * π * Complex.I * z) =
        cexp ((2 * π * Complex.I * z * (n : ℂ)) + (2 * π * Complex.I * z)) /
          cexp (2 * π * Complex.I * z) := by
          -- Rewrite the numerator via `hExp₁` and `hExp₂`.
          rw [hExp₁, hExp₂]
    _ = (cexp (2 * π * Complex.I * z * (n : ℂ)) * cexp (2 * π * Complex.I * z)) /
          cexp (2 * π * Complex.I * z) := by
          simp [Complex.exp_add]
    _ = cexp (2 * π * Complex.I * z * (n : ℂ)) := by
          field_simp [Complex.exp_ne_zero (2 * π * Complex.I * z)]

lemma cexp_mul_two_add_div_q_sq (z : ℂ) (n : ℕ) :
    cexp (2 * π * Complex.I * z * ((n + 2 : ℕ) : ℂ)) / (q z) ^ (2 : ℕ) =
      cexp (2 * π * Complex.I * z * (n : ℂ)) := by
  unfold q
  have hne : cexp (2 * π * Complex.I * z) ≠ 0 := Complex.exp_ne_zero _
  have hn2 : (((n + 2 : ℕ) : ℂ)) = (n : ℂ) + (2 : ℂ) := by
    simp [Nat.cast_add]
  have harg₀ :
      2 * π * Complex.I * z * ((n + 2 : ℕ) : ℂ) =
        (2 * π * Complex.I * z * (n : ℂ)) + (2 * π * Complex.I * z) + (2 * π * Complex.I * z) := by
    grind only
  have harg :
      2 * π * Complex.I * z * ((n + 2 : ℕ) : ℂ) =
        (2 * π * Complex.I * z * (n : ℂ)) + (2 * π * Complex.I * z + (2 * π * Complex.I * z)) := by
    -- Reassociate the right-hand side.
    simpa [add_assoc] using harg₀
  have hExp :
      cexp (2 * π * Complex.I * z * ((n + 2 : ℕ) : ℂ)) =
        cexp
          ((2 * π * Complex.I * z * (n : ℂ)) +
            (2 * π * Complex.I * z + (2 * π * Complex.I * z))) := by
    simpa using congrArg cexp harg
  calc
    cexp (2 * π * Complex.I * z * ((n + 2 : ℕ) : ℂ)) / (cexp (2 * π * Complex.I * z)) ^ (2 : ℕ) =
        cexp
            ((2 * π * Complex.I * z * (n : ℂ)) +
              (2 * π * Complex.I * z + (2 * π * Complex.I * z))) /
          (cexp (2 * π * Complex.I * z)) ^ (2 : ℕ) := by
          have := congrArg (fun w : ℂ => w / (cexp (2 * π * Complex.I * z)) ^ (2 : ℕ)) hExp
          simpa using this
    _ =
        (cexp (2 * π * Complex.I * z * (n : ℂ)) * cexp (2 * π * Complex.I * z) *
              cexp (2 * π * Complex.I * z)) /
          (cexp (2 * π * Complex.I * z) * cexp (2 * π * Complex.I * z)) := by
          simp [Complex.exp_add, pow_two, mul_left_comm, mul_comm]
    _ = cexp (2 * π * Complex.I * z * (n : ℂ)) := by
          field_simp [hne]

/-- Leading `q`-coefficient for `E₆`: `(E₆-1)/q → -504` as `z → i∞`. -/
public lemma tendsto_E₆_sub_one_div_q :
    Tendsto (fun z : ℍ => (E₆ z - (1 : ℂ)) / q (z : ℂ)) atImInfty (𝓝 (-(504 : ℂ))) := by
  -- We use the `q`-expansion of `E₆` to identify the leading coefficient.
  let a : ℕ → ℂ := fun n => (σ 5 (n + 1) : ℂ)
  have ha : Summable (fun n : ℕ => ‖a n‖ * Real.exp (-2 * Real.pi * n)) := by
    have hsigma : ∀ n : ℕ, (σ 5 (n + 1) : ℝ) ≤ ((n : ℝ) + (1 : ℕ)) ^ 6 := by
      intro n
      have hsigma0 : (σ 5 (n + 1) : ℝ) ≤ (n + 1 : ℝ) ^ 6 := by
        norm_cast
        simpa using (sigma_five_le_pow_six (n + 1))
      -- Rewrite `(n+1 : ℝ)` as `n + 1`.
      simpa [Nat.cast_add] using hsigma0
    simpa [a] using
      (SpherePacking.ForMathlib.summable_norm_sigma_shift_mul_exp (k := 5) (m := 6) (s := 1) hsigma)
  have hseries :
      Tendsto (fun z : ℍ => ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n)) atImInfty (𝓝 (a 0)) :=
    QExp.tendsto_nat (a := a) (ha := ha)
  have hseries' :
      Tendsto (fun z : ℍ => (-(504 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 ((-(504 : ℂ)) * (a 0))) :=
    tendsto_const_nhds.mul hseries
  have ha0 : a 0 = (1 : ℂ) := by simp [a]
  have hseries'' :
      Tendsto (fun z : ℍ => (-(504 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * z * n))
        atImInfty (𝓝 (-(504 : ℂ))) := by
    simpa [ha0] using hseries'
  -- Identify `(E₆ z - 1) / q` with this `q`-series.
  have hE6_eq (z : ℍ) :
      (E₆ z - (1 : ℂ)) / q (z : ℂ) =
        (-(504 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
    -- Coefficients in the `q`-expansion of `E₆`.
    let c : ℕ → ℂ := fun n => if n = 0 then 1 else -(504 : ℂ) * (σ 5 n : ℂ)
    let f : ℕ → ℂ := fun n => c n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))
    have hper :
        (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma 1 : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
      simp [CongruenceSubgroup.strictPeriods_Gamma]
    have hF : HasSum (fun n : ℕ => f n) (E₆ z) := by
      have hsum :=
        ModularFormClass.hasSum_qExpansion (f := E₆) (h := (1 : ℝ)) (by positivity) hper z
      refine HasSum.congr_fun hsum (fun n => ?_)
      have hcoeff : (qExpansion (1 : ℝ) E₆).coeff n = c n := by
        simpa [c] using congr_fun E6_q_exp n
      have hqpow :
          (Periodic.qParam (1 : ℝ) (z : ℂ)) ^ n =
            cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
        have hq : Periodic.qParam (1 : ℝ) (z : ℂ) = cexp (2 * π * Complex.I * (z : ℂ)) := by
          simp [Periodic.qParam]
        rw [hq]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Complex.exp_nat_mul (2 * π * Complex.I * (z : ℂ)) n).symm
      simp [f, smul_eq_mul, hcoeff, hqpow, mul_left_comm, mul_comm]
    have hsumf : Summable f := hF.summable
    -- Split off the `n = 0` term to rewrite `E₆ z - 1` as a `ℕ+` sum.
    have hsplit :
        f 0 + ∑' n : ℕ+, f (n : ℕ) = E₆ z := by
      have := tsum_zero_pnat_eq_tsum_nat (f := f) hsumf
      simpa [hF.tsum_eq] using this
    have hf0 : f 0 = (1 : ℂ) := by
      simp [f, c]
    have htail :
        E₆ z - (1 : ℂ) = ∑' n : ℕ+, f (n : ℕ) := by
      have hpnat : (∑' n : ℕ+, f (n : ℕ)) = E₆ z - f 0 :=
        eq_sub_of_add_eq' hsplit
      simpa [hf0] using hpnat.symm
    -- Rewrite the `ℕ+` series using the explicit formula for `c n` when `n ≠ 0`.
    let g : ℕ+ → ℂ :=
      fun n => (σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))
    have hfg : (∑' n : ℕ+, f (n : ℕ)) = (-(504 : ℂ)) * ∑' n : ℕ+, g n := by
      have h1 :
          (∑' n : ℕ+, f (n : ℕ)) =
            ∑' n : ℕ+, (-(504 : ℂ)) * g n := by
        refine tsum_congr fun n => ?_
        have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
        grind only
      calc
        (∑' n : ℕ+, f (n : ℕ)) = ∑' n : ℕ+, (-(504 : ℂ)) * g n := h1
        _ = (-(504 : ℂ)) * ∑' n : ℕ+, g n := by
              simpa using
                (tsum_mul_left (a := (-(504 : ℂ))) (f := g))
    have hE6sub :
        E₆ z - (1 : ℂ) = (-(504 : ℂ)) * ∑' n : ℕ+, g n := by
      exact htail.trans (by simpa using hfg)
    -- Now divide by `q` and shift from `ℕ+` to `ℕ`.
    have hshift :
        (∑' n : ℕ+, (g n) / q (z : ℂ)) =
          ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
      have hpnat' :
          (∑' n : ℕ+, (g n) / q (z : ℂ)) =
            ∑' n : ℕ,
              ((σ 5 (n + 1) : ℂ) *
                    cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ) := by
        -- Convert the `ℕ+` sum to an `ℕ` sum via `n ↦ n+1`.
        simpa [g, Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc, mul_assoc,
          mul_left_comm, mul_comm] using
          (tsum_pnat_eq_tsum_succ
            (f := fun n : ℕ =>
              ((σ 5 n : ℂ) * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ))) / q (z : ℂ)))
      rw [hpnat']
      refine tsum_congr fun n => ?_
      dsimp [a]
      have hmul :
          ((σ 5 (n + 1) : ℂ) *
                cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ) =
            (σ 5 (n + 1) : ℂ) *
              (cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ)) := by
        ring
      calc
        ((σ 5 (n + 1) : ℂ) *
                cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ))) / q (z : ℂ)
            = (σ 5 (n + 1) : ℂ) *
                (cexp (2 * π * Complex.I * (z : ℂ) * ((n + 1 : ℕ) : ℂ)) / q (z : ℂ)) := hmul
        _ = (σ 5 (n + 1) : ℂ) *
              cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
              -- Rewrite `((n+1 : ℕ) : ℂ)` as `(n : ℂ) + 1` to match `cexp_mul_succ_div_q`.
              have :=
                cexp_mul_succ_div_q (z := (z : ℂ)) (n := n)
              -- `simp` does the remaining coercion/algebra work.
              simpa [Nat.cast_add, Nat.cast_one] using this
    calc
      (E₆ z - (1 : ℂ)) / q (z : ℂ)
          = ((-(504 : ℂ)) * (∑' n : ℕ+, g n)) / q (z : ℂ) := by
                rw [hE6sub]
      _ = (-(504 : ℂ)) * ((∑' n : ℕ+, g n) / q (z : ℂ)) := by
            simpa [mul_assoc] using
              (mul_div_assoc (-(504 : ℂ)) (∑' n : ℕ+, g n) (q (z : ℂ)))
      _ = (-(504 : ℂ)) * ∑' n : ℕ+, (g n) / q (z : ℂ) := by
            simpa using
              congrArg (fun t : ℂ => (-(504 : ℂ)) * t)
                (tsum_div_const (f := g) (a := q (z : ℂ))).symm
      _ = (-(504 : ℂ)) * ∑' n : ℕ, a n * cexp (2 * π * Complex.I * (z : ℂ) * (n : ℂ)) := by
            simp [hshift]
  exact (tendsto_congr hE6_eq).mpr hseries''


end SpecialValuesVarphi₁Limits

end

end SpherePacking.Dim24
