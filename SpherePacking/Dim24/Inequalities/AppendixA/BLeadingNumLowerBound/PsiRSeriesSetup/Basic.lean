module
public import SpherePacking.Dim24.Inequalities.AppendixA.GeometricTailBounds
public import SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.Defs


/-!
### `ψI` numerator as an `r`-series

Appendix A (and `appendix.txt`) treats the theta contribution using the parameter
`r(t) = exp(-π t)` and `r`-series with integer coefficients.
We set up the minimal Cauchy-product API for `rseries` used to expand the `ψI`-numerator.
-/

noncomputable section

namespace SpherePacking.Dim24.AppendixA


open scoped BigOperators

/-- Additivity of `rseries`, assuming summability of the two norm series. -/
public lemma rseries_add_of_summable (t : ℝ) (a b : ℕ → ℤ)
    (ha : Summable (fun n : ℕ => ‖((a n : ℂ) * (rC t) ^ n)‖))
    (hb : Summable (fun n : ℕ => ‖((b n : ℂ) * (rC t) ^ n)‖)) :
    rseries (fun n : ℕ => a n + b n) t = rseries a t + rseries b t := by
  have ha' : Summable (fun n : ℕ => (a n : ℂ) * (rC t) ^ n) := Summable.of_norm ha
  have hb' : Summable (fun n : ℕ => (b n : ℂ) * (rC t) ^ n) := Summable.of_norm hb
  simp [rseries, Int.cast_add, add_mul, ha'.tsum_add hb']

/-- Pull an integer scalar out of `rseries`, assuming summability of the norm series. -/
public lemma rseries_smul_int_of_summable (t : ℝ) (c : ℤ) (a : ℕ → ℤ)
    (ha : Summable (fun n : ℕ => ‖((a n : ℂ) * (rC t) ^ n)‖)) :
    rseries (fun n : ℕ => c * a n) t = (c : ℂ) * rseries a t := by
  have ha' : Summable (fun n : ℕ => (a n : ℂ) * (rC t) ^ n) := Summable.of_norm ha
  simpa [rseries, Int.cast_mul, mul_assoc] using (ha'.tsum_mul_left (a := (c : ℂ)))

/-- Cauchy product on integer coefficient functions `ℕ → ℤ`, written as an antidiagonal sum. -/
@[expose] public def convZ (a b : ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ p ∈ Finset.antidiagonal n, a p.1 * b p.2

/-- Polynomial growth bound for `convZ a b`, assuming polynomial bounds on `a` and `b`. -/
public lemma abs_convZ_le (a b : ℕ → ℤ) (Ca Cb : ℝ) (ka kb : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ Ca * (((n + 1 : ℕ) : ℝ) ^ ka))
    (hb : ∀ n : ℕ, |(b n : ℝ)| ≤ Cb * (((n + 1 : ℕ) : ℝ) ^ kb)) :
    ∀ n : ℕ, |(convZ a b n : ℝ)| ≤ (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb + 1)) := by
  intro n
  have hcast :
      (convZ a b n : ℝ) =
        ∑ p ∈ Finset.antidiagonal n, (a p.1 : ℝ) * (b p.2 : ℝ) := by
    -- Push the casts inside the sum.
    simp [convZ]
  have hterm :
      ∀ p ∈ Finset.antidiagonal n,
        |(a p.1 : ℝ) * (b p.2 : ℝ)| ≤ (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb)) := by
    intro p hp
    have hm : p.1 + p.2 = n := by simpa [Finset.mem_antidiagonal] using hp
    have hp1_le : p.1 ≤ n := by
      have : p.1 ≤ p.1 + p.2 := Nat.le_add_right _ _
      simpa [hm] using this
    have hp2_le : p.2 ≤ n := by
      have : p.2 ≤ p.1 + p.2 := Nat.le_add_left _ _
      simpa [hm] using this
    have hp1 : ((p.1 + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hp1_le
    have hp2 : ((p.2 + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hp2_le
    have hpow1 : (((p.1 + 1 : ℕ) : ℝ) ^ ka) ≤ (((n + 1 : ℕ) : ℝ) ^ ka) :=
      pow_le_pow_left₀ (by positivity) hp1 _
    have hpow2 : (((p.2 + 1 : ℕ) : ℝ) ^ kb) ≤ (((n + 1 : ℕ) : ℝ) ^ kb) :=
      pow_le_pow_left₀ (by positivity) hp2 _
    have ha' : |(a p.1 : ℝ)| ≤ Ca * (((p.1 + 1 : ℕ) : ℝ) ^ ka) := ha p.1
    have hb' : |(b p.2 : ℝ)| ≤ Cb * (((p.2 + 1 : ℕ) : ℝ) ^ kb) := hb p.2
    have hCa : 0 ≤ Ca := le_trans (abs_nonneg (a 0 : ℝ)) (by simpa using ha 0)
    have hCb : 0 ≤ Cb := le_trans (abs_nonneg (b 0 : ℝ)) (by simpa using hb 0)
    calc
      |(a p.1 : ℝ) * (b p.2 : ℝ)| = |(a p.1 : ℝ)| * |(b p.2 : ℝ)| := by simp [abs_mul]
      _ ≤ (Ca * (((p.1 + 1 : ℕ) : ℝ) ^ ka)) * (Cb * (((p.2 + 1 : ℕ) : ℝ) ^ kb)) :=
            mul_le_mul ha' hb' (abs_nonneg _) (mul_nonneg hCa (by positivity))
      _ ≤ (Ca * (((n + 1 : ℕ) : ℝ) ^ ka)) * (Cb * (((n + 1 : ℕ) : ℝ) ^ kb)) := by
            gcongr
      _ = (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb)) := by
            simp [mul_assoc, mul_left_comm, pow_add]
  have hsum_abs :
      |∑ p ∈ Finset.antidiagonal n, (a p.1 : ℝ) * (b p.2 : ℝ)| ≤
        ∑ p ∈ Finset.antidiagonal n, |(a p.1 : ℝ) * (b p.2 : ℝ)| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (f := fun p => (a p.1 : ℝ) * (b p.2 : ℝ))
        (s := Finset.antidiagonal n))
  have hsum_le :
      (∑ p ∈ Finset.antidiagonal n, |(a p.1 : ℝ) * (b p.2 : ℝ)|) ≤
        (∑ _p ∈ Finset.antidiagonal n, (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb))) :=
    Finset.sum_le_sum hterm
  have hcard : (Finset.antidiagonal n).card = n + 1 := by
    simp
  have hconst :
      (∑ _p ∈ Finset.antidiagonal n, (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb))) =
        ((n + 1 : ℕ) : ℝ) * ((Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb))) := by
    simp [hcard, mul_assoc]
  calc
    |(convZ a b n : ℝ)| =
        |∑ p ∈ Finset.antidiagonal n, (a p.1 : ℝ) * (b p.2 : ℝ)| := by
      simp [hcast]
    _ ≤ ∑ p ∈ Finset.antidiagonal n, |(a p.1 : ℝ) * (b p.2 : ℝ)| := hsum_abs
    _ ≤
          ∑ _p ∈ Finset.antidiagonal n,
            (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb)) := hsum_le
    _ =
        ((n + 1 : ℕ) : ℝ) * ((Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb))) := hconst
    _ = (Ca * Cb) * (((n + 1 : ℕ) : ℝ) ^ (ka + kb + 1)) := by
          -- Rewrite `pow_succ` and reassociate.
          ring_nf

/-- Cauchy product for `rseries`: the product of two `rseries` is the `rseries` of their `convZ`. -/
public lemma rseries_mul_cast (t : ℝ) (a b : ℕ → ℤ)
    (ha : Summable (fun n : ℕ => ‖((a n : ℂ) * (rC t) ^ n)‖))
    (hb : Summable (fun n : ℕ => ‖((b n : ℂ) * (rC t) ^ n)‖)) :
    (rseries a t) * (rseries b t) = rseries (convZ a b) t := by
  let f : ℕ → ℂ := fun n => (a n : ℂ) * (rC t) ^ n
  let g : ℕ → ℂ := fun n => (b n : ℂ) * (rC t) ^ n
  have hf : Summable (fun n : ℕ => ‖f n‖) := by simpa [f] using ha
  have hg : Summable (fun n : ℕ => ‖g n‖) := by simpa [g] using hb
  have hprod :
      (∑' n : ℕ, f n) * (∑' n : ℕ, g n) =
        ∑' m : ℕ, ∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2 := by
    simpa using (tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg)
  have hanti (m : ℕ) :
      (∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2) =
        (convZ a b m : ℂ) * (rC t) ^ m := by
    have hmul (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal m) :
        f p.1 * g p.2 = ((a p.1 : ℂ) * (b p.2 : ℂ)) * (rC t) ^ m := by
      have hm : p.1 + p.2 = m := by
        simpa [Finset.mem_antidiagonal] using hp
      grind only
    calc
      (∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2)
          = ∑ p ∈ Finset.antidiagonal m, ((a p.1 : ℂ) * (b p.2 : ℂ)) * (rC t) ^ m := by
              exact Finset.sum_congr rfl hmul
      _ = (∑ p ∈ Finset.antidiagonal m, (a p.1 : ℂ) * (b p.2 : ℂ)) * (rC t) ^ m := by
            simp [Finset.sum_mul, mul_assoc]
        _ = (convZ a b m : ℂ) * (rC t) ^ m := by
            simp [convZ]
  have hanti' :
      (fun m : ℕ => ∑ p ∈ Finset.antidiagonal m, f p.1 * g p.2) =
        fun m : ℕ => (convZ a b m : ℂ) * (rC t) ^ m := by
    funext m
    simp [hanti m]
  have hf_tsum : (∑' n : ℕ, f n) = rseries a t := by
    simp [rseries, f, rC]
  have hg_tsum : (∑' n : ℕ, g n) = rseries b t := by
    simp [rseries, g, rC]
  have hconv_tsum :
      (∑' m : ℕ, (convZ a b m : ℂ) * (rC t) ^ m) = rseries (convZ a b) t := by
    simp [rseries, rC]
  simpa [hf_tsum, hg_tsum, hconv_tsum, hanti'] using hprod

/-- The coefficient function of the constant series `1`: `oneCoeffFun 0 = 1`, otherwise `0`. -/
@[expose] public def oneCoeffFun (n : ℕ) : ℤ := if n = 0 then 1 else 0

/--
Iterated Cauchy product powers: `powConvZ a k` is the coefficient function of
`(rseries a)^k`. -/
@[expose] public def powConvZ (a : ℕ → ℤ) : ℕ → (ℕ → ℤ)
  | 0 => oneCoeffFun
  | Nat.succ k => convZ a (powConvZ a k)

/-!
#### Summability/tail bounds for `rseries` with polynomially bounded coefficients

We reuse the same `powGeomTerm` majorants as for `q`-series, but with base `r(t) = exp(-π t)`.
-/

/-- Summability of the geometric-polynomial majorant `powGeomTerm (r t) k`. -/
public lemma summable_powGeomTerm_r (t : ℝ) (ht0 : 0 < t) (k : ℕ) :
    Summable (fun n : ℕ => powGeomTerm (r t) k n) := by
  -- Reduce to summability of `n^k * r^n` for `‖r‖ < 1`.
  set r0 : ℝ := r t
  have hr0_pos : 0 < r0 := by
    simp [r0, r, Real.exp_pos]
  have hr0_nonneg : 0 ≤ r0 := hr0_pos.le
  have hr0_lt_one : r0 < 1 := by
    have hneg : (-Real.pi * t) < 0 := by nlinarith [Real.pi_pos, ht0]
    simpa [r0, r] using (Real.exp_lt_one_iff.2 hneg)
  have hr0_norm : ‖r0‖ < 1 := by
    simpa [Real.norm_of_nonneg hr0_nonneg] using hr0_lt_one
  have hs_pow : Summable (fun n : ℕ => ((n : ℝ) ^ k : ℝ) * r0 ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k hr0_norm
  have hs_shift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r0 ^ (n + 1)) := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1 (f := fun n : ℕ => ((n : ℝ) ^ k : ℝ) * r0 ^ n)).2 hs_pow
  have hs_shift' :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * r0 ^ n) := by
    have hs1 :
        Summable (fun n : ℕ => (1 / r0) * (((n + 1 : ℕ) : ℝ) ^ k * r0 ^ (n + 1))) :=
      hs_shift.mul_left (1 / r0)
    refine hs1.congr ?_
    intro n
    field_simp [hr0_pos.ne']
    simp [pow_succ, mul_comm]
  simpa [powGeomTerm, r0] using hs_shift'

private lemma norm_rseries_term_le_of_coeffBound (t : ℝ) (a : ℕ → ℤ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) (n : ℕ) :
    ‖((a n : ℂ) * (rC t) ^ n)‖ ≤ C * powGeomTerm (r t) k n := by
  have hr0 : 0 ≤ r t := (Real.exp_pos _).le
  have hrC : ‖rC t‖ = r t := by
    simp [rC, Real.norm_of_nonneg hr0]
  have hnorm_r : ‖(rC t) ^ n‖ = (r t) ^ n := by
    simp [norm_pow, hrC]
  calc
    ‖((a n : ℂ) * (rC t) ^ n)‖ = ‖(a n : ℂ)‖ * ‖(rC t) ^ n‖ := by simp
    _ = |(a n : ℝ)| * (r t) ^ n := by simp [hnorm_r]
    _ ≤ (C * (((n + 1 : ℕ) : ℝ) ^ k)) * (r t) ^ n := by
          exact mul_le_mul_of_nonneg_right (ha n) (pow_nonneg hr0 _)
    _ = C * powGeomTerm (r t) k n := by
          simp [powGeomTerm, mul_assoc, Nat.cast_add_one]

/-- Summability of the norm series defining `rseries`, assuming a polynomial coefficient bound. -/
public lemma summable_norm_rseries_of_coeffBound (t : ℝ) (ht0 : 0 < t)
    (a : ℕ → ℤ) (C : ℝ) (k : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    Summable (fun n : ℕ => ‖((a n : ℂ) * (rC t) ^ n)‖) := by
  have hle : ∀ n : ℕ, ‖((a n : ℂ) * (rC t) ^ n)‖ ≤ C * powGeomTerm (r t) k n :=
    norm_rseries_term_le_of_coeffBound (t := t) (a := a) (C := C) (k := k) ha
  -- Summability of the majorant.
  have hs_majorant : Summable (fun n : ℕ => C * powGeomTerm (r t) k n) := by
    have hs0 : Summable (fun n : ℕ => powGeomTerm (r t) k n) :=
      summable_powGeomTerm_r (t := t) (ht0 := ht0) (k := k)
    exact hs0.mul_left C
  exact Summable.of_norm_bounded (g := fun n : ℕ => C * powGeomTerm (r t) k n)
    hs_majorant (by intro n; simpa using hle n)

/-- Tail bound for `rseries`: bound the norm of the tail by a sum of `powGeomTerm` majorants. -/
public lemma norm_rseries_tail_le_of_coeffBound (t : ℝ) (ht0 : 0 < t)
    (a : ℕ → ℤ) (C : ℝ) (k N : ℕ)
    (ha : ∀ n : ℕ, |(a n : ℝ)| ≤ C * (((n + 1 : ℕ) : ℝ) ^ k)) :
    ‖∑' m : ℕ, (a (N + m) : ℂ) * (rC t) ^ (N + m)‖ ≤
      C * (∑' m : ℕ, powGeomTerm (r t) k (N + m)) := by
  let f : ℕ → ℂ := fun m => (a (N + m) : ℂ) * (rC t) ^ (N + m)
  have hf_tail_summable : Summable (fun m : ℕ => ‖f m‖) := by
    have hs :
        Summable (fun n : ℕ => ‖((a n : ℂ) * (rC t) ^ n)‖) :=
      summable_norm_rseries_of_coeffBound (t := t) (ht0 := ht0)
        (a := a) (C := C) (k := k) ha
    have hs' : Summable (fun m : ℕ => ‖((a (m + N) : ℂ) * (rC t) ^ (m + N))‖) :=
      (summable_nat_add_iff N (f := fun n => ‖((a n : ℂ) * (rC t) ^ n)‖)).2 hs
    simpa [f, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs'
  have hnorm_tsum :
      ‖∑' m : ℕ, f m‖ ≤ ∑' m : ℕ, ‖f m‖ :=
    (norm_tsum_le_tsum_norm hf_tail_summable)
  -- Termwise bound by the majorant `C * powGeomTerm`.
  have hterm_le : ∀ m : ℕ, ‖f m‖ ≤ C * powGeomTerm (r t) k (N + m) :=
    fun m => norm_rseries_term_le_of_coeffBound t a C k ha (N + m)
  have hs_majorant : Summable (fun m : ℕ => C * powGeomTerm (r t) k (N + m)) := by
    have hs0 : Summable (fun m : ℕ => powGeomTerm (r t) k (N + m)) := by
      have hs := summable_powGeomTerm_r (t := t) (ht0 := ht0) (k := k)
      have hs' : Summable (fun m : ℕ => powGeomTerm (r t) k (m + N)) :=
        (summable_nat_add_iff N (f := fun n => powGeomTerm (r t) k n)).2 hs
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hs'
    exact hs0.mul_left C
  have hsum_le :
      (∑' m : ℕ, ‖f m‖) ≤ ∑' m : ℕ, C * powGeomTerm (r t) k (N + m) := by
    refine hasSum_le (fun m => hterm_le m) ?_ hs_majorant.hasSum
    · exact hf_tail_summable.hasSum
  have hCmul :
      (∑' m : ℕ, C * powGeomTerm (r t) k (N + m)) =
        C * (∑' m : ℕ, powGeomTerm (r t) k (N + m)) := by
    simpa [mul_assoc] using
      (tsum_mul_left (a := C) (f := fun m => powGeomTerm (r t) k (N + m)))
  calc
    ‖∑' m : ℕ, (a (N + m) : ℂ) * (rC t) ^ (N + m)‖
        = ‖∑' m : ℕ, f m‖ := by simp [f]
    _ ≤ ∑' m : ℕ, ‖f m‖ := hnorm_tsum
    _ ≤ ∑' m : ℕ, C * powGeomTerm (r t) k (N + m) := hsum_le
    _ = C * (∑' m : ℕ, powGeomTerm (r t) k (N + m)) := hCmul


end SpherePacking.Dim24.AppendixA
