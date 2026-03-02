module
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


/-!
# Iterated derivatives

This file proves results such as `upper_ne_int`, `aut_iter_deriv`, `aut_contDiffOn`,
`iter_div_aut_add`, and `exp_iter_deriv_within`.
-/

open scoped Real Nat
open UpperHalfPlane Set Filter Function Complex

/-- For `x ∈ ℍ` and `d ∈ ℤ`, the complex number `x + d` is nonzero. -/
public theorem upper_ne_int (x : ℍ) (d : ℤ) : (x : ℂ) + d ≠ 0 := by
  simpa [eq_neg_iff_add_eq_zero] using UpperHalfPlane.ne_intCast x (-d)


/-- A closed form for iterated derivatives of `z ↦ 1 / (z + d)` on the upper half-plane. -/
public theorem aut_iter_deriv (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z + d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  set s : Set ℂ := {z : ℂ | 0 < z.im}
  have hs : IsOpen s := by
    refine isOpen_lt ?_ ?_ <;> fun_prop
  -- Reduce `iteratedDerivWithin` to the iterated `deriv` on the open set `s`.
  refine (iteratedDerivWithin_of_isOpen_eq_iterate (s := s) (n := k)
      (f := fun z : ℂ => 1 / (z + d)) hs).trans ?_
  intro t _
  have hneg : (-1 - k : ℤ) = Int.negSucc k := by
    -- both sides are `-(k+1)`; `Int.negSucc_eq` rewrites the RHS
    simp [Int.negSucc_eq, sub_eq_add_neg, add_comm]
  have hzpow : (t + (d : ℂ)) ^ (-1 - k : ℤ) = 1 / (t + (d : ℂ)) ^ (k + 1) := by
    simp [one_div, hneg]
  -- Use the closed form for iterated derivatives of an inverse affine function.
  have hiter :
      deriv^[k] (fun x : ℂ => 1 / (x + d)) t =
        (-1) ^ k * k ! * (t + (d : ℂ)) ^ (-1 - k : ℤ) := by
    simpa [one_div] using
      congrArg (fun g : ℂ → ℂ => g t) (iter_deriv_inv_linear (k := k) (c := (1 : ℂ)) (d := d))
  simpa [one_div, s, hzpow] using hiter

theorem aut_iter_deriv' (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d)) {z : ℂ | 0 < z.im})
      (fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  simpa [sub_eq_add_neg] using (aut_iter_deriv (-d : ℤ) k)

/-- Smoothness of `z ↦ 1 / (z - d)` on the upper half-plane. -/
public theorem aut_contDiffOn (d : ℤ) (k : ℕ) : ContDiffOn ℂ k (fun z : ℂ => 1 / (z - d))
    {z : ℂ | 0 < z.im} := by
  simpa [one_div] using
    (ContDiffOn.inv (contDiffOn_id.sub contDiffOn_const) fun x hx =>
      by simpa [sub_eq_add_neg] using (upper_ne_int (x := ⟨x, hx⟩) (d := (-d : ℤ))))


/-- A closed form for iterated derivatives of `z ↦ 1 / (z - d) + 1 / (z + d)`.

This holds on the upper half-plane `{z : ℂ | 0 < z.im}`.
-/
public theorem iter_div_aut_add (d : ℤ) (k : ℕ) :
    EqOn (iteratedDerivWithin k (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) {z : ℂ | 0 < z.im})
      ((fun t : ℂ => (-1) ^ k * k ! * (1 / (t - d) ^ (k + 1))) + fun t : ℂ =>
        (-1) ^ k * k ! * (1 / (t + d) ^ (k + 1))) {z : ℂ | 0 < z.im} := by
  intro x hx
  have hfg :
      (fun z : ℂ => 1 / (z - d) + 1 / (z + d)) =
        (fun z : ℂ => 1 / (z - d)) + fun z : ℂ => 1 / (z + d) := by
    funext z
    simp [Pi.add_apply]
  -- Put the sum into the canonical `f + g` form used by `iteratedDerivWithin_add`.
  rw [hfg]
  have hs : IsOpen ({z : ℂ | 0 < z.im} : Set ℂ) := by
    refine isOpen_lt ?_ ?_ <;> fun_prop
  have hsub :
      ContDiffWithinAt ℂ k (fun z : ℂ => (z - d)⁻¹) {z : ℂ | 0 < z.im} x := by
    simpa [one_div] using (aut_contDiffOn d k).contDiffWithinAt hx
  have hadd :
      ContDiffWithinAt ℂ k (fun z : ℂ => (z + d)⁻¹) {z : ℂ | 0 < z.im} x := by
    simpa [one_div, sub_eq_add_neg, Int.cast_neg, neg_neg] using
      (aut_contDiffOn (-d) k).contDiffWithinAt hx
  have hsum := iteratedDerivWithin_add (hx := hx) (h := hs.uniqueDiffOn) hsub hadd
  have h₁' :
      iteratedDerivWithin k (fun z : ℂ => (z - d)⁻¹) {z : ℂ | 0 < z.im} x =
        (-1) ^ k * k ! * ((x - d) ^ (k + 1))⁻¹ := by
    simpa [one_div] using (aut_iter_deriv' d k hx)
  have h₂' :
      iteratedDerivWithin k (fun z : ℂ => (z + d)⁻¹) {z : ℂ | 0 < z.im} x =
        (-1) ^ k * k ! * ((x + d) ^ (k + 1))⁻¹ := by
    simpa [one_div] using (aut_iter_deriv d k hx)
  -- split the iterated derivative over the sum, then rewrite each term using the closed form
  simpa [Pi.add_apply, one_div, h₁', h₂'] using hsum

/-- Iterated derivatives of an exponential `s ↦ exp(2π i m s)` on the upper half-plane. -/
public theorem exp_iter_deriv_within (n m : ℕ) :
    EqOn (iteratedDerivWithin n (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * m * s))
           {z : ℂ | 0 < z.im})
      (fun t => (2 * ↑π * Complex.I * m) ^ n * Complex.exp (2 * ↑π * Complex.I * m * t))
      {z : ℂ | 0 < z.im} := by
  refine (iteratedDerivWithin_of_isOpen (s := {z : ℂ | 0 < z.im}) ?_).trans ?_
  · refine isOpen_lt (by fun_prop) (by fun_prop)
  intro x _
  exact congr_fun (iteratedDeriv_cexp_const_mul ..) x
