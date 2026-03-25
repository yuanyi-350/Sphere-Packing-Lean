module
public import SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Harmonic
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite dimensionality of the homogeneous pieces `Pk k`

This file shows that the degree-`k` homogeneous component `Pk k` of `MvPolynomial (Fin 24) ℝ` is
finite dimensional. This is used later to deduce completeness of the Fischer inner product spaces.

## Main statements
* `finiteDimensional_Pk`
-/
namespace SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
noncomputable section

open scoped BigOperators

open Finsupp MvPolynomial

/-- The homogeneous piece `Pk k` is finite dimensional. -/
public noncomputable instance finiteDimensional_Pk (k : ℕ) : FiniteDimensional ℝ (Pk k) := by
  -- Unfold to the concrete `homogeneousSubmodule`.
  change FiniteDimensional ℝ ↥(MvPolynomial.homogeneousSubmodule Var ℝ k)
  -- Let `S` be the (finite) set of exponent vectors of degree `k`.
  let S : Set (Var →₀ ℕ) := expSet k
  have hEq :
      MvPolynomial.homogeneousSubmodule Var ℝ k =
        Finsupp.supported (α := Var →₀ ℕ) (M := ℝ) ℝ S := by
    simpa [S] using (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := Var) (R := ℝ) k)
  haveI : Finite S :=
    (Set.finite_coe_iff.mpr (expSet_finite k))
  haveI : FiniteDimensional ℝ (S →₀ ℝ) := by infer_instance
  -- Map `homogeneousSubmodule` into `S →₀ ℝ` using the equality `hEq` and `supportedEquivFinsupp`.
  let eST :=
    LinearEquiv.ofEq (MvPolynomial.homogeneousSubmodule Var ℝ k)
      (Finsupp.supported (α := Var →₀ ℕ) (M := ℝ) ℝ S) hEq
  let eSup := (Finsupp.supportedEquivFinsupp (M := ℝ) (R := ℝ) (s := S))
  let f : ↥(MvPolynomial.homogeneousSubmodule Var ℝ k) →ₗ[ℝ] (S →₀ ℝ) :=
    eSup.toLinearMap.comp eST.toLinearMap
  have hf : Function.Injective f := eSup.injective.comp eST.injective
  exact FiniteDimensional.of_injective f hf

end

end SpherePacking.Dim24.Uniqueness.BS81.LP.Gegenbauer24.PSD.Fischer
