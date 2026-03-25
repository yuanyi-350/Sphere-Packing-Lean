module
public import SpherePacking.ModularForms.SummableLemmas.Cotangent

/-!
# Summability lemmas for `G_2` with correction term

This file adds the correction term `δ` to the alternative `G_2` series and records summability
and rearrangement lemmas for the resulting expressions.

## Main statements
* `G_2_alt_summable_δ`
* `G2_alt_indexing_δ`, `G2_alt_indexing2_δ`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open ArithmeticFunction

/-- Summability of the alternative `G_2` series with the correction term `δ`. -/
public lemma G_2_alt_summable_δ (z : ℍ) : Summable fun (m : Fin 2 → ℤ) =>
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1)) := by
  refine (G_2_alt_summable z).add ?_
  refine summable_of_hasFiniteSupport ?_
  refine ((Set.finite_singleton (![0, 0] : Fin 2 → ℤ)).insert (![0, -1])).subset ?_
  intro m hm
  by_cases h00 : m 0 = 0 ∧ m 1 = 0
  · have : m = ![0, 0] := by
      ext i; fin_cases i <;> simp [h00.1, h00.2]
    simp [this]
  · by_cases h01 : m 0 = 0 ∧ m 1 = -1
    · have : m = ![0, -1] := by
        ext i; fin_cases i <;> simp [h01.1, h01.2]
      simp [this]
    · exfalso
      exact hm (by simp [δ, h00, h01])

/-- For fixed `b`, summability of the `c`-slice of the alternative `G_2` series. -/
public theorem G2_prod_summable1 (z : ℍ) (b : ℤ) :
    Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹ := by
  have hs := (by simpa [Fin.isValue, one_div, mul_inv_rev] using G_2_alt_summable z)
  exact (((finTwoArrowEquiv _).symm.summable_iff).2 hs).prod_factor b

/-- A `δ`-corrected version of `G2_prod_summable1`. -/
public theorem G2_prod_summable1_δ (z : ℍ) (b : ℤ) :
    Summable fun c : ℤ ↦ ((b : ℂ) * ↑z + ↑c + 1)⁻¹ * (((b : ℂ) * ↑z + ↑c) ^ 2)⁻¹ + δ b c := by
  have hs := (by simpa [Fin.isValue, one_div, mul_inv_rev] using G_2_alt_summable_δ z)
  exact (((finTwoArrowEquiv _).symm.summable_iff).2 hs).prod_factor b

/-- Reindex the `δ`-corrected `G_2` series as an iterated sum over `ℤ × ℤ`. -/
public lemma G2_alt_indexing_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1)) =
    ∑' m : ℤ, ∑' n : ℤ, (1 / (((m : ℂ)* z + n)^2 * (m * z + n +1)) + (δ m n)) := by
  rw [← (finTwoArrowEquiv _).symm.tsum_eq]
  simp only [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_div, mul_inv_rev]
  have hs := (((finTwoArrowEquiv _).symm.summable_iff).2 <|
    by simpa [Fin.isValue, one_div, mul_inv_rev] using G_2_alt_summable_δ z)
  refine Summable.tsum_prod' hs ?_
  intro b
  simpa using hs.prod_factor b

/-- A commuted version of `G2_alt_indexing_δ`, swapping the `ℤ` sums. -/
public lemma G2_alt_indexing2_δ (z : ℍ) : ∑' (m : Fin 2 → ℤ),
    (1 / (((m 0 : ℂ) * z + m 1)^2 * (m 0 * z + m 1 + 1)) + δ (m 0) (m 1)) =
    ∑' n : ℤ, ∑' m : ℤ, (1 / (((m : ℂ)* z +n)^2 * (m * z + n +1)) + δ m n) := by
  rw [Summable.tsum_comm', G2_alt_indexing_δ (z := z)]
  · have h := G_2_alt_summable_δ z
    rw [← (finTwoArrowEquiv _).symm.summable_iff] at h
    simpa [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using h
  · intro b
    simpa [one_div, mul_inv_rev] using G2_prod_summable1_δ z b
  · have h := G_2_alt_summable_δ z
    rw [← ((finTwoArrowEquiv _).trans (.prodComm ..)).symm.summable_iff] at h
    simpa [Fin.isValue, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] using h.prod_factor

/-- If `g n` grows linearly at infinity, then `∑ 1/(g n)^(k+1)` is summable for `k ≥ 1`. -/
public theorem summable_pow_inv_of_linear_bigO (k : ℕ) (hk : 1 ≤ k) {g : ℕ → ℂ}
    (hlin : (fun n : ℕ => (g n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)|⁻¹)) :
    Summable fun n : ℕ => ((g n) ^ (k + 1))⁻¹ := by
  have hab : (1 : ℝ) < (k + 1 : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : (1 : ℕ) < 2) (Nat.succ_le_succ hk)
  refine
    summable_hammerTime_nat (f := fun n : ℕ => (g n) ^ (k + 1)) (a := (k + 1)) hab ?_
  norm_cast
  simp_rw [← inv_pow]
  have hpow :
      (fun n : ℕ ↦ (↑(n ^ (k + 1)) : ℝ)⁻¹) =
        fun n : ℕ ↦ (↑(n : ℝ)⁻¹) ^ (k + 1) := by simp
  simp_rw [hpow]
  apply Asymptotics.IsBigO.pow
  apply Asymptotics.IsBigO.of_abs_right
  -- Turn `| (n : ℝ)⁻¹ |` into `|(n : ℝ)|⁻¹`.
  simpa [abs_inv, Nat.abs_cast, Asymptotics.isBigO_abs_right] using hlin
