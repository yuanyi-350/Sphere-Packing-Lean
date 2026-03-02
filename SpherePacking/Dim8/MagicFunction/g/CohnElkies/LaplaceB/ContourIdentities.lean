module
public import SpherePacking.Dim8.MagicFunction.g.CohnElkies.LaplaceB.Basic


/-!
# Contour integrands for `b'`

This file packages the exponential weight `exp(π i u z)` together with the functions `ψI'`,
`ψT'`, and `ψS'` into contour integrands used in the rectangle deformation argument for the
Laplace representation of `b'`.

## Main definitions
* `MagicFunction.g.CohnElkies.IntegralReps.bContourWeight`
* `MagicFunction.g.CohnElkies.IntegralReps.bContourIntegrandI`
* `MagicFunction.g.CohnElkies.IntegralReps.bContourIntegrandT`
* `MagicFunction.g.CohnElkies.IntegralReps.bContourIntegrandS`

## Main statements
* `MagicFunction.g.CohnElkies.IntegralReps.bContourIntegrandI_mul_I_eq_bLaplaceIntegrand`
* `MagicFunction.g.CohnElkies.IntegralReps.differentiableOn_bContourIntegrandT`
-/

namespace MagicFunction.g.CohnElkies.IntegralReps

noncomputable section

open scoped BigOperators Topology UpperHalfPlane
open MeasureTheory Real Complex Filter


/-- Exponential weight `exp(π i u z)` used in the contour integrands for `b'`. -/
@[expose] public def bContourWeight (u : ℝ) (z : ℂ) : ℂ :=
  cexp (π * (Complex.I : ℂ) * (u : ℂ) * z)

/-- Multiplicativity of `bContourWeight` with respect to addition. -/
public lemma bContourWeight_add (u : ℝ) (z w : ℂ) :
    bContourWeight u (z + w) = bContourWeight u z * bContourWeight u w := by
  simp [bContourWeight, mul_add, Complex.exp_add, mul_assoc]

/-- Contour integrand for the `ψI'` term (with a minus sign). -/
@[expose] public def bContourIntegrandI (u : ℝ) (z : ℂ) : ℂ :=
  -(ψI' z * bContourWeight u z)

/-- Contour integrand for the `ψT'` term. -/
@[expose] public def bContourIntegrandT (u : ℝ) (z : ℂ) : ℂ :=
  ψT' z * bContourWeight u z

/-- Contour integrand for the `ψS'` term. -/
@[expose] public def bContourIntegrandS (u : ℝ) (z : ℂ) : ℂ :=
  ψS' z * bContourWeight u z

/-- Evaluate `bContourWeight` on the imaginary axis: `bContourWeight u (I * t) = exp(-π u t)`. -/
public lemma bContourWeight_mul_I (u t : ℝ) :
    bContourWeight u ((Complex.I : ℂ) * (t : ℂ)) = (Real.exp (-π * u * t) : ℂ) := by
  have hI :
      (π : ℂ) * (Complex.I : ℂ) * (u : ℂ) * ((Complex.I : ℂ) * (t : ℂ)) =
        (-(π : ℂ) * (u : ℂ) * (t : ℂ)) := by ring_nf; simp [pow_two, Complex.I_mul_I]
  simp [bContourWeight, hI]

private lemma bContourIntegrandI_mul_I (u t : ℝ) :
    bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) =
      -(ψI' ((Complex.I : ℂ) * (t : ℂ)) * (Real.exp (-π * u * t) : ℂ)) := by
  simp [bContourIntegrandI, bContourWeight_mul_I, mul_assoc]

/-- On the imaginary axis, `bContourIntegrandI` agrees with `-bLaplaceIntegrand`. -/
public lemma bContourIntegrandI_mul_I_eq_bLaplaceIntegrand (u t : ℝ) :
    bContourIntegrandI u ((Complex.I : ℂ) * (t : ℂ)) = -bLaplaceIntegrand u t := by
  simp [bLaplaceIntegrand, bContourIntegrandI_mul_I]

/-- Imaginary-axis specialization of `bContourIntegrandT`. -/
public lemma bContourIntegrandT_mul_I (u t : ℝ) :
    bContourIntegrandT u ((Complex.I : ℂ) * (t : ℂ)) =
      ψT' ((Complex.I : ℂ) * (t : ℂ)) * (Real.exp (-π * u * t) : ℂ) := by
  simp [bContourIntegrandT, bContourWeight_mul_I, mul_assoc]

/-- Translate `ψT'` into `ψI'` by adding `1` in the upper half-plane. -/
public lemma ψT'_eq_ψI'_add_one (z : ℂ) (hz : 0 < z.im) :
    ψT' z = ψI' (z + (1 : ℂ)) := by
  have hz' : 0 < (z + (1 : ℂ)).im := by simpa using hz
  have htrans : ((1 : ℝ) +ᵥ ⟨z, hz⟩ : ℍ) = ⟨z + (1 : ℂ), hz'⟩ := by
    ext1; simp; ring_nf
  simp [ψT', ψI', hz, ψT, modular_slash_T_apply, htrans]

/-- Specialize `ψT'_eq_ψI'_add_one` at `z = -1 + I * t`. -/
public lemma ψT'_neg_one_add_I_mul (t : ℝ) (ht : 0 < t) :
    ψT' ((-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) = ψI' ((Complex.I : ℂ) * (t : ℂ)) := by
  simpa [add_assoc, mul_assoc] using
    (ψT'_eq_ψI'_add_one (z := (-1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) (by simpa [mul_assoc] using ht))

/-- Specialize `ψT'_eq_ψI'_add_one` at `z = 1 + I * t`. -/
public lemma ψT'_one_add_I_mul (t : ℝ) (ht : 0 < t) :
    ψT' ((1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) = ψI' ((Complex.I : ℂ) * (t : ℂ)) := by
  have hz0 : 0 < (((Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by simpa using ht
  have hz1 : 0 < (((1 : ℂ) + (Complex.I : ℂ) * (t : ℂ)) : ℂ).im := by
    simpa [mul_assoc] using ht
  have htrans :
      ((1 : ℝ) +ᵥ ⟨(Complex.I : ℂ) * (t : ℂ), hz0⟩ : ℍ) =
        ⟨(1 : ℂ) + (Complex.I : ℂ) * (t : ℂ), hz1⟩ := by
    ext1; simp
  have hrel :=
    congrArg (fun F : ℍ → ℂ => F ⟨(Complex.I : ℂ) * (t : ℂ), hz0⟩) ψT_slash_T
  have hEq :
      ψT ⟨(1 : ℂ) + (Complex.I : ℂ) * (t : ℂ), hz1⟩ =
        ψI ⟨(Complex.I : ℂ) * (t : ℂ), hz0⟩ := by
    simpa [modular_slash_T_apply, htrans] using hrel
  simpa [ψT', ψI', ht] using hEq

/-- Specialize `ψT'_eq_ψI'_add_one` at `z = I * t`. -/
public lemma ψT'_I_mul (t : ℝ) (ht : 0 < t) :
    ψT' ((Complex.I : ℂ) * (t : ℂ)) = ψI' (((Complex.I : ℂ) * (t : ℂ)) + (1 : ℂ)) := by
  simpa [add_assoc] using
    (ψT'_eq_ψI'_add_one (z := (Complex.I : ℂ) * (t : ℂ)) (by simpa using ht))

private lemma differentiableOn_ψT_ofComplex :
    DifferentiableOn ℂ (fun z : ℂ => ψT (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} := by
  -- Transfer the `MDifferentiable` statements for the `H`-functions on `ℍ` to `ℂ`.
  have hH2 :
      DifferentiableOn ℂ (fun z : ℂ => H₂ (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := H₂)).1 mdifferentiable_H₂
  have hH3 :
      DifferentiableOn ℂ (fun z : ℂ => H₃ (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := H₃)).1 mdifferentiable_H₃
  have hH4 :
      DifferentiableOn ℂ (fun z : ℂ => H₄ (UpperHalfPlane.ofComplex z)) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff (f := H₄)).1 mdifferentiable_H₄
  have hden2 :
      ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
        (H₂ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ) ≠ 0 := by
    intro z hz
    exact pow_ne_zero 2 (H₂_ne_zero (UpperHalfPlane.ofComplex z))
  have hden4 :
      ∀ z : ℂ, z ∈ {z : ℂ | 0 < z.im} →
        (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ) ≠ 0 := by
    intro z hz
    exact pow_ne_zero 2 (H₄_ne_zero (UpperHalfPlane.ofComplex z))
  have hleft :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (H₃ (UpperHalfPlane.ofComplex z) + H₄ (UpperHalfPlane.ofComplex z)) /
            (H₂ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))
        {z : ℂ | 0 < z.im} :=
    (hH3.add hH4).div (hH2.pow 2) hden2
  have hright :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (H₂ (UpperHalfPlane.ofComplex z) + H₃ (UpperHalfPlane.ofComplex z)) /
            (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))
        {z : ℂ | 0 < z.im} :=
    (hH2.add hH3).div (hH4.pow 2) hden4
  have hExpr :
      DifferentiableOn ℂ
        (fun z : ℂ =>
          (128 : ℂ) *
            (((H₃ (UpperHalfPlane.ofComplex z) + H₄ (UpperHalfPlane.ofComplex z)) /
                  (H₂ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ)) +
              ((H₂ (UpperHalfPlane.ofComplex z) + H₃ (UpperHalfPlane.ofComplex z)) /
                  (H₄ (UpperHalfPlane.ofComplex z)) ^ (2 : ℕ))))
        {z : ℂ | 0 < z.im} := by
    simpa [mul_assoc] using (DifferentiableOn.const_mul (hleft.add hright) (128 : ℂ))
  -- Rewrite the expression using `ψT_eq`.
  refine hExpr.congr ?_
  intro z hz
  have hh2 : (H₂_MF : ℍ → ℂ) = H₂ := rfl
  have hh3 : (H₃_MF : ℍ → ℂ) = H₃ := rfl
  have hh4 : (H₄_MF : ℍ → ℂ) = H₄ := rfl
  have h := congrArg (fun f : ℍ → ℂ => f (UpperHalfPlane.ofComplex z)) ψT_eq
  simpa [hh2, hh3, hh4] using h

/-- Holomorphy of `bContourIntegrandT` on the open upper half-plane. -/
public lemma differentiableOn_bContourIntegrandT (u : ℝ) :
    DifferentiableOn ℂ (bContourIntegrandT u) {z : ℂ | 0 < z.im} := by
  have hExp : DifferentiableOn ℂ (bContourWeight u) {z : ℂ | 0 < z.im} := by
    simpa [bContourWeight] using (by fun_prop :
      Differentiable ℂ fun z : ℂ => cexp (π * (Complex.I : ℂ) * (u : ℂ) * z)).differentiableOn
  have hg :
      DifferentiableOn ℂ (fun z : ℂ => ψT (UpperHalfPlane.ofComplex z) * bContourWeight u z)
        {z : ℂ | 0 < z.im} := differentiableOn_ψT_ofComplex.mul hExp
  refine hg.congr ?_
  intro z hz
  have hz' : 0 < z.im := hz
  simp [bContourIntegrandT, ψT', hz', UpperHalfPlane.ofComplex_apply_of_im_pos hz']

/-- Continuity of `bContourIntegrandT` on the open upper half-plane. -/
public lemma continuousOn_bContourIntegrandT (u : ℝ) :
    ContinuousOn (bContourIntegrandT u) {z : ℂ | 0 < z.im} := by
  simpa using (differentiableOn_bContourIntegrandT (u := u)).continuousOn

end

end MagicFunction.g.CohnElkies.IntegralReps
