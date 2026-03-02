module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.IsZLatticeOfUnimodular
public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# A lattice inside its real span

Given a `ℤ`-submodule `L ⊆ ℝ²⁴`, we view `L` as a `ℤ`-submodule of its real span `spanR L`.
This is a convenient construction for the implication `Unimodular → IsZLattice`.

## Main definitions
* `IsZLatticeOfUnimodular.latticeInSpanR`

## Main statements
* `IsZLatticeOfUnimodular.instIsZLattice_latticeInSpanR`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

namespace IsZLatticeOfUnimodular

variable (L : Submodule ℤ ℝ²⁴)

/-- View `L` as a `ℤ`-submodule of its real span `spanR L`. -/
@[expose]
public def latticeInSpanR : Submodule ℤ (spanR (L := L)) :=
  Submodule.comap
    (((spanR (L := L)).subtype : spanR (L := L) →ₗ[ℝ] ℝ²⁴).restrictScalars ℤ) L

/-- Membership in `latticeInSpanR L` is definitional membership in `L` after coercion to `ℝ²⁴`. -/
@[simp] public lemma mem_latticeInSpanR_iff (x : spanR (L := L)) :
    x ∈ latticeInSpanR (L := L) ↔ (x : ℝ²⁴) ∈ L := by
  rfl

/-- If `L` is discrete, then `latticeInSpanR L` has the discrete topology. -/
public instance instDiscreteTopology_latticeInSpanR [DiscreteTopology L] :
    DiscreteTopology (latticeInSpanR (L := L)) := by
  -- Use a continuous injective map into the discrete space `L`.
  let f : latticeInSpanR (L := L) → L :=
    fun x => ⟨((x : spanR (L := L)) : ℝ²⁴), x.property⟩
  have hf : Continuous f := by
    -- `fun_prop` handles continuity between subtypes of `ℝ²⁴`.
    dsimp [f]
    fun_prop
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hxy' :
        ((x : spanR (L := L)) : ℝ²⁴) = ((y : spanR (L := L)) : ℝ²⁴) :=
      congrArg (fun z : L => (z : ℝ²⁴)) hxy
    -- `spanR (L := L)` is a subtype of `ℝ²⁴`.
    exact Subtype.ext hxy'
  exact DiscreteTopology.of_continuous_injective (hc := hf) (hinj := hinj)

/-- If `L` is discrete, then `latticeInSpanR L` is a `ℤ`-lattice in `spanR L`. -/
public instance instIsZLattice_latticeInSpanR [DiscreteTopology L] :
    IsZLattice ℝ (latticeInSpanR (L := L)) := by
  -- Show `span ℝ (latticeInSpanR : Set (spanR L)) = ⊤` by comparing its image in `ℝ²⁴`.
  refine ⟨?_⟩
  -- Let `W := spanR L` and `LW := latticeInSpanR L`.
  let W : Submodule ℝ ℝ²⁴ := spanR (L := L)
  let LW : Submodule ℤ W := latticeInSpanR (L := L)
  have hinj : Function.Injective (W.subtype : W →ₗ[ℝ] ℝ²⁴) := fun _ _ h => by
    apply Subtype.ext
    exact h
  have himg :
      (fun w : W => (w : ℝ²⁴)) '' (LW : Set W) = (L : Set ℝ²⁴) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [LW, W, latticeInSpanR] using hw
    · intro hx
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · -- `x ∈ spanR L`
        exact Submodule.subset_span hx
      · -- membership in `LW`
        simpa [LW, W, latticeInSpanR] using hx
  have hmap :
      Submodule.map (W.subtype : W →ₗ[ℝ] ℝ²⁴)
          (Submodule.span ℝ (LW : Set W))
        =
        W := by
    -- Use `map_span` and the definition of `W`.
    rw [Submodule.map_span]
    simp [W, IsZLatticeOfUnimodular.spanR, himg]
  -- Pull back along the injective map `W.subtype`.
  have :
      Submodule.span ℝ (LW : Set W) = ⊤ := by
    have := congrArg (Submodule.comap (W.subtype : W →ₗ[ℝ] ℝ²⁴)) hmap
    -- simplify `comap (subtype) W = ⊤` and `comap_map = _` for injective maps
    simpa [Submodule.comap_map_eq_of_injective hinj] using this
  simpa [LW] using this

end IsZLatticeOfUnimodular

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
