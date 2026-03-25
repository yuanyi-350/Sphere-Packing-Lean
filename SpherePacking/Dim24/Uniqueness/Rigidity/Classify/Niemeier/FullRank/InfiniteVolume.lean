module
public import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.FullRank.OrthogonalDecomp
import SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Niemeier.LatticeInSpan
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Infinite-volume fundamental domains

If `spanR L ≠ ⊤`, then any additive fundamental domain for the translation action of `L` on `ℝ²⁴`
has infinite volume. This is the geometric input behind the implication
`Unimodular L → IsZLattice ℝ L`.

## Main statements
* `IsZLatticeOfUnimodular.volume_eq_top_of_isAddFundamentalDomain_of_spanR_ne_top`
-/


namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

open MeasureTheory

namespace IsZLatticeOfUnimodular

variable (L : Submodule ℤ ℝ²⁴)

local notation "W" => W (L := L)
local notation "K" => K (L := L)

lemma volume_univ_K_eq_top (hW : spanR (L := L) ≠ ⊤) :
    (volume : Measure K) (Set.univ : Set K) = ⊤ := by
  -- `K` is defined as the orthogonal complement of `spanR L`.
  simpa [IsZLatticeOfUnimodular.K, IsZLatticeOfUnimodular.W] using
    (volume_univ_orthogonal_eq_top (L := L) hW)

namespace InfiniteVolume

open scoped Topology

-- A convenient abbreviation for the lattice inside its span.
local notation "LW" => latticeInSpanR (L := L)

-- Transport an element of `LW` back to an element of `L`.
noncomputable def toL : LW → L := fun x => ⟨((x : W) : ℝ²⁴), x.property⟩

-- View an element of `L` as an element of `LW`.
noncomputable def toLW : L → LW :=
  fun x => ⟨⟨(x : ℝ²⁴), mem_W_of_mem_L (L := L) x.property⟩, x.property⟩

-- For the translation action of `L` on `ℝ²⁴`, `v +ᵥ x` is definitionaly `v + x`.
@[simp] lemma vadd_eq_add_coe (v : L) (x : ℝ²⁴) : v +ᵥ x = (v : ℝ²⁴) + x := rfl

@[simp] lemma toL_toLW (x : L) : toL (L := L) (toLW (L := L) x) = x := by
  apply Subtype.ext
  rfl

@[simp] lemma toLW_toL (x : LW) : toLW (L := L) (toL (L := L) x) = x := by
  rfl

-- The `W`-component of `decomp.symm` is additive.
@[simp] private lemma decomp_symm_fst_add (x y : ℝ²⁴) :
    ((decomp (L := L)).symm (x + y)).1 =
      ((decomp (L := L)).symm x).1 + ((decomp (L := L)).symm y).1 :=
  congrArg Prod.fst ((decomp (L := L)).symm.map_add x y)

-- Elements of `W` are sent by `decomp.symm` to `(w, 0)`.
@[simp] lemma decomp_symm_coe_W (w : W) :
    (decomp (L := L)).symm (w : ℝ²⁴) = (w, (0 : K)) := by
  simp [IsZLatticeOfUnimodular.decomp]

-- Hence, elements of `L` have trivial `K`-component.
@[simp] lemma decomp_symm_coe_L_snd (x : L) :
    ((decomp (L := L)).symm (x : ℝ²⁴)).2 = (0 : K) := by
  have hx : (x : ℝ²⁴) ∈ W := mem_W_of_mem_L (L := L) x.property
  simpa [toLW, IsZLatticeOfUnimodular.W] using
    congrArg Prod.snd (decomp_symm_coe_W (L := L) (w := ⟨(x : ℝ²⁴), hx⟩))

-- And the `W`-component is just `x` viewed in `W`.
@[simp] lemma decomp_symm_coe_L_fst (x : L) :
    ((decomp (L := L)).symm (x : ℝ²⁴)).1 = (toLW (L := L) x : W) := by
  have hx : (x : ℝ²⁴) ∈ W := mem_W_of_mem_L (L := L) x.property
  simpa [toLW, IsZLatticeOfUnimodular.W] using
    congrArg Prod.fst (decomp_symm_coe_W (L := L) (w := ⟨(x : ℝ²⁴), hx⟩))

/-!
### A canonical fundamental domain in `ℝ²⁴`

We use the orthogonal decomposition `ℝ²⁴ ≃ₗ W × K` for `W = spanR L` and its orthogonal complement
`K = Wᗮ`, together with the standard `ZSpan.fundamentalDomain` in `W` for the induced lattice
`latticeInSpanR L`.
-/

noncomputable local instance instModuleFiniteLW [DiscreteTopology L] : Module.Finite ℤ LW :=
  @ZLattice.module_finite ℝ _ _ _ _ _ _ _ _ _ _ LW
    (instDiscreteTopology_latticeInSpanR (L := L)) (instIsZLattice_latticeInSpanR (L := L))

noncomputable local instance instModuleFreeLW [DiscreteTopology L] : Module.Free ℤ LW :=
  @ZLattice.module_free ℝ _ _ _ _ _ _ _ _ _ _ LW
    (instDiscreteTopology_latticeInSpanR (L := L)) (instIsZLattice_latticeInSpanR (L := L))

noncomputable def bZ [DiscreteTopology L] :
    Module.Basis (Fin (Module.finrank ℝ W)) ℤ LW :=
  (Module.Free.chooseBasis ℤ LW).reindex (Fintype.equivOfCardEq
    (by rw [← Module.finrank_eq_card_chooseBasisIndex, @ZLattice.rank ℝ _ _ _ _ _ _ _ _ _ _ LW
      (instDiscreteTopology_latticeInSpanR (L := L)) (instIsZLattice_latticeInSpanR (L := L)), Fintype.card_fin]))

noncomputable def bR [DiscreteTopology L] :
    Module.Basis (Fin (Module.finrank ℝ W)) ℝ W :=
  @Module.Basis.ofZLatticeBasis ℝ _ _ _ _ _ _ _ _ _ _ LW
    (instDiscreteTopology_latticeInSpanR (L := L)) _ (instIsZLattice_latticeInSpanR (L := L)) (bZ (L := L))

noncomputable def A [DiscreteTopology L] : Set W :=
  ZSpan.fundamentalDomain (bR (L := L))

noncomputable def F0 [DiscreteTopology L] : Set ℝ²⁴ :=
  (decomp (L := L)) '' (A (L := L) ×ˢ (Set.univ : Set K))

local instance instBorelSpaceW : BorelSpace W := Subtype.borelSpace fun x => x ∈ W
local instance instOpensMeasurableSpaceW : OpensMeasurableSpace W := Subtype.opensMeasurableSpace fun x => x ∈ W
local instance instMeasureSpaceW : MeasureSpace W :=
  @measureSpaceOfInnerProductSpace W _ _ _ Subtype.instMeasurableSpace (instBorelSpaceW (L := L))
local instance instBorelSpaceK : BorelSpace K := Subtype.borelSpace fun x => x ∈ K
local instance instMeasureSpaceK : MeasureSpace K :=
  @measureSpaceOfInnerProductSpace K _ _ _ Subtype.instMeasurableSpace (instBorelSpaceK (L := L))
local instance instBorelSpaceWK : BorelSpace (W × K) := Prod.borelSpace

lemma measurableSet_A [DiscreteTopology L] : MeasurableSet (A (L := L)) := by
  simpa [A, bR] using
    (@ZSpan.fundamentalDomain_measurableSet W (Fin (Module.finrank ℝ W)) _ _ (bR (L := L))
      Subtype.instMeasurableSpace (instOpensMeasurableSpaceW (L := L)) inferInstance)

lemma measure_A_ne_zero [DiscreteTopology L] : (volume : Measure W) (A (L := L)) ≠ 0 := by
  simpa [A, bR] using
    (@ZSpan.measure_fundamentalDomain_ne_zero W (Fin (Module.finrank ℝ W)) _ _ (bR (L := L))
      inferInstance Subtype.instMeasurableSpace (instBorelSpaceW (L := L)) (volume : Measure W) inferInstance)

lemma isAddFundamentalDomain_F0 [DiscreteTopology L] [Countable L] :
    IsAddFundamentalDomain L (F0 (L := L)) (volume : Measure ℝ²⁴) := by
  have hA_meas : MeasurableSet (A (L := L)) := measurableSet_A (L := L)
  have hprodmeas : MeasurableSet (A (L := L) ×ˢ (Set.univ : Set K)) :=
    hA_meas.prod MeasurableSet.univ
  have hemb : MeasurableEmbedding (decomp (L := L)) := by
    have hemeas : Measurable (decomp (L := L)) :=
      (LinearMap.continuous_of_finiteDimensional _).measurable
    exact hemeas.measurableEmbedding (decomp (L := L)).injective
  have hF0_meas : MeasurableSet (F0 (L := L)) := by
    simpa [F0] using
      (hemb.measurableSet_image (s := (A (L := L) ×ˢ (Set.univ : Set K)))).2 hprodmeas
  refine IsAddFundamentalDomain.mk' hF0_meas.nullMeasurableSet ?_
  intro x
  let wk : W × K := (decomp (L := L)).symm x
  let G : Submodule ℤ W := Submodule.span ℤ (Set.range (bR (L := L)))
  have hspan : G = LW := by
    have hspan' : Submodule.span ℤ (Set.range (bR (L := L))) = LW := by
      simpa [bR] using
        (@Module.Basis.ofZLatticeBasis_span ℝ _ _ _ _ _ _ _ _ _ _ LW
          (instDiscreteTopology_latticeInSpanR (L := L)) _ (instIsZLattice_latticeInSpanR (L := L)) (bZ (L := L)))
    simpa [G, bR] using hspan'
  have hexuG : ∃! v : G, v +ᵥ wk.1 ∈ A (L := L) := by
    simpa [G, A] using
      (ZSpan.exist_unique_vadd_mem_fundamentalDomain (b := bR (L := L)) (x := wk.1))
  rcases hexuG with ⟨v0, hv0, hv0uniq⟩
  let ofG : G → L := fun v =>
    ⟨((v : W) : ℝ²⁴),
      (mem_latticeInSpanR_iff (L := L) (x := (v : W))).1 (by
        have : (v : W) ∈ LW := by
          simpa [hspan] using v.property
        simpa using this)⟩
  let toG : L → G := fun y =>
    ⟨(toLW (L := L) y : W), by
      have : ((toLW (L := L) y : LW) : W) ∈ LW := (toLW (L := L) y).property
      exact (hspan.symm ▸ this)⟩
  have hof_to : ∀ y : L, ofG (toG y) = y := by
    intro y
    apply Subtype.ext
    rfl
  have hF0_pre :
      F0 (L := L) =
        ((decomp (L := L)).symm : ℝ²⁴ → W × K) ⁻¹' (A (L := L) ×ˢ (Set.univ : Set K)) := by
    simpa [F0] using
      ((decomp (L := L)).toEquiv.image_eq_preimage_symm (A (L := L) ×ˢ (Set.univ : Set K)))
  refine ⟨ofG v0, ?_, ?_⟩
  · rw [hF0_pre]
    change (decomp (L := L)).symm (((ofG v0 : L) : ℝ²⁴) + x) ∈ (A (L := L) ×ˢ (Set.univ : Set K))
    refine ⟨?_, trivial⟩
    have hfst :
        ((decomp (L := L)).symm (((ofG v0 : L) : ℝ²⁴) + x)).1 = (v0 : W) + wk.1 := by
      have hfst_add :
          ((decomp (L := L)).symm (((ofG v0 : L) : ℝ²⁴) + x)).1 =
            ((decomp (L := L)).symm (((ofG v0 : L) : ℝ²⁴))).1 + ((decomp (L := L)).symm x).1 :=
        decomp_symm_fst_add (L := L) (((ofG v0 : L) : ℝ²⁴)) x
      have hfst0 : ((decomp (L := L)).symm (((ofG v0 : L) : ℝ²⁴))).1 = (v0 : W) := by
        simp [ofG]
      have hwk : ((decomp (L := L)).symm x).1 = wk.1 := rfl
      calc
        ((decomp (L := L)).symm (((ofG v0 : L) : ℝ²⁴) + x)).1
            = ((decomp (L := L)).symm (((ofG v0 : L) : ℝ²⁴))).1 + ((decomp (L := L)).symm x).1 :=
              hfst_add
        _ = (v0 : W) + wk.1 := by simp [hfst0, hwk]
    have hA0 : (v0 : W) + wk.1 ∈ A (L := L) := by simpa using hv0
    exact hfst ▸ hA0
  · intro y hy
    have hyA : ((decomp (L := L)).symm (((y : L) : ℝ²⁴) + x)).1 ∈ A (L := L) := by
      have hy0 : ((decomp (L := L)).symm (y +ᵥ x)).1 ∈ A (L := L) := by
        rw [hF0_pre] at hy
        exact hy.1
      simpa [vadd_eq_add_coe (L := L) (v := y) (x := x)] using hy0
    have hyA' : (toG y : W) + wk.1 ∈ A (L := L) := by
      have hfst_add :
          ((decomp (L := L)).symm (((y : L) : ℝ²⁴) + x)).1 =
            ((decomp (L := L)).symm ((y : L) : ℝ²⁴)).1 + ((decomp (L := L)).symm x).1 :=
        decomp_symm_fst_add (L := L) ((y : L) : ℝ²⁴) x
      have hfst : ((decomp (L := L)).symm ((y : L) : ℝ²⁴)).1 = (toG y : W) := by
        change ((decomp (L := L)).symm ((y : L) : ℝ²⁴)).1 = (toLW (L := L) y : W)
        exact decomp_symm_coe_L_fst (L := L) (x := y)
      have : ((decomp (L := L)).symm (((y : L) : ℝ²⁴) + x)).1 = (toG y : W) + wk.1 := by
        calc
          ((decomp (L := L)).symm (((y : L) : ℝ²⁴) + x)).1 =
              ((decomp (L := L)).symm ((y : L) : ℝ²⁴)).1 + ((decomp (L := L)).symm x).1 := hfst_add
          _ = (toG y : W) + ((decomp (L := L)).symm x).1 := by simp [hfst]
          _ = (toG y : W) + wk.1 := by simp [wk]
      exact this ▸ hyA
    have htoG : toG y = v0 := by
      apply hv0uniq
      change ((toG y : W) + wk.1 ∈ A (L := L))
      exact hyA'
    calc
      y = ofG (toG y) := (hof_to y).symm
      _ = ofG v0 := congrArg ofG htoG

lemma volume_F0_eq_top [DiscreteTopology L] [Countable L] (hW : spanR (L := L) ≠ ⊤) :
    (volume : Measure ℝ²⁴) (F0 (L := L)) = ⊤ := by
  letI : BorelSpace K := Subtype.borelSpace fun x => x ∈ K
  letI : MeasureSpace K :=
    @measureSpaceOfInnerProductSpace K _ _ _ Subtype.instMeasurableSpace (Subtype.borelSpace fun x => x ∈ K)
  haveI : Measure.IsAddHaarMeasure (volume : Measure W) := by
    simpa [measureSpaceOfInnerProductSpace] using
      (@isAddHaarMeasure_basis_addHaar _ W _ _ _ Subtype.instMeasurableSpace (instBorelSpaceW (L := L)) ((stdOrthonormalBasis ℝ W).toBasis))
  haveI : Measure.IsAddHaarMeasure (volume : Measure K) := by
    simpa [measureSpaceOfInnerProductSpace] using
      (@isAddHaarMeasure_basis_addHaar _ K _ _ _ Subtype.instMeasurableSpace (inferInstance : BorelSpace K) ((stdOrthonormalBasis ℝ K).toBasis))
  -- Use the product Haar measure on `W × K` to avoid relying on an `IsAddHaarMeasure` instance
  -- for `volume : Measure (W × K)` (which can be fragile w.r.t. instance diamonds).
  let ν : Measure (W × K) := (volume : Measure W).prod (volume : Measure K)
  haveI : Measure.IsAddHaarMeasure ν := by infer_instance
  have hKuniv : (volume : Measure K) (Set.univ : Set K) = ⊤ := volume_univ_K_eq_top (L := L) hW
  have hA_ne0 : (volume : Measure W) (A (L := L)) ≠ 0 := measure_A_ne_zero (L := L)
  have hAprod : ν (A (L := L) ×ˢ (Set.univ : Set K)) = ⊤ := by
    have hprod :
        ν (A (L := L) ×ˢ (Set.univ : Set K)) =
          (volume : Measure W) (A (L := L)) * (volume : Measure K) (Set.univ : Set K) := by
      have hprod' :=
        (MeasureTheory.Measure.prod_prod (μ := (volume : Measure W)) (ν := (volume : Measure K))
          (A (L := L)) (Set.univ : Set K))
      dsimp [ν]
      exact hprod'
    simp [hprod, hKuniv, hA_ne0]
  have hmeasProd : MeasurableSet (A (L := L) ×ˢ (Set.univ : Set K)) :=
    (measurableSet_A (L := L)).prod MeasurableSet.univ
  have hemeas_symm : Measurable (decomp (L := L)).symm :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hF0_preim :
      (decomp (L := L)).symm ⁻¹' (A (L := L) ×ˢ (Set.univ : Set K)) = F0 (L := L) := by
    simpa [F0] using
      ((decomp (L := L)).toEquiv.image_eq_preimage_symm (A (L := L) ×ˢ (Set.univ : Set K))).symm
  have hmap :
      (volume : Measure ℝ²⁴) (F0 (L := L)) =
        (volume : Measure ℝ²⁴).map ((decomp (L := L)).symm : ℝ²⁴ →ₗ[ℝ] (W × K))
          (A (L := L) ×ˢ (Set.univ : Set K)) := by
    simp [Measure.map_apply, hemeas_symm, hmeasProd, hF0_preim]
  have hsurj : Function.Surjective ((decomp (L := L)).symm : ℝ²⁴ →ₗ[ℝ] (W × K)) :=
    (decomp (L := L)).symm.surjective
  rcases (@LinearMap.exists_map_addHaar_eq_smul_addHaar ℝ ℝ²⁴ (W × K)
      _ _ _ (inferInstance : MeasurableSpace ℝ²⁴) (inferInstance : BorelSpace ℝ²⁴) _ _
      Prod.instMeasurableSpace (instBorelSpaceWK (L := L)) _ ((decomp (L := L)).symm : ℝ²⁴ →ₗ[ℝ] (W × K))
      (volume : Measure ℝ²⁴) ν _ _ _ hsurj) with
    ⟨c, hcpos, hc⟩
  rw [hmap, hc]
  simp [hAprod, hcpos.ne']

end InfiniteVolume

/-- If `spanR L ≠ ⊤`, then any additive fundamental domain for `L` in `ℝ²⁴` has infinite volume. -/
public theorem volume_eq_top_of_isAddFundamentalDomain_of_spanR_ne_top
    [DiscreteTopology L] [Countable L] {F : Set ℝ²⁴}
    (hF : IsAddFundamentalDomain L F (volume : Measure ℝ²⁴))
    (hW : spanR (L := L) ≠ ⊤) :
    (volume : Measure ℝ²⁴) F = ⊤ := by
  haveI : MeasurableVAdd ↥L ℝ²⁴ :=
    show MeasurableVAdd ↥L ℝ²⁴ from (inferInstance : MeasurableVAdd L.toAddSubgroup ℝ²⁴)
  haveI : MeasurableConstVAdd ↥L ℝ²⁴ :=
    show MeasurableConstVAdd ↥L ℝ²⁴ from (inferInstance : MeasurableConstVAdd L.toAddSubgroup ℝ²⁴)
  haveI : VAddInvariantMeasure ↥L ℝ²⁴ (volume : Measure ℝ²⁴) := by infer_instance
  have hF0 :
      IsAddFundamentalDomain L (InfiniteVolume.F0 (L := L)) (volume : Measure ℝ²⁴) :=
    InfiniteVolume.isAddFundamentalDomain_F0 (L := L)
  have hEq :
      (volume : Measure ℝ²⁴) F = (volume : Measure ℝ²⁴) (InfiniteVolume.F0 (L := L)) :=
    (show IsAddFundamentalDomain L.toAddSubgroup F (volume : Measure ℝ²⁴) from hF).measure_eq
      (μ := (volume : Measure ℝ²⁴))
      (show IsAddFundamentalDomain L.toAddSubgroup (InfiniteVolume.F0 (L := L)) (volume : Measure ℝ²⁴) from hF0)
  have hVolF0 : (volume : Measure ℝ²⁴) (InfiniteVolume.F0 (L := L)) = ⊤ :=
    InfiniteVolume.volume_F0_eq_top (L := L) hW
  simpa [hEq] using hVolF0

end IsZLatticeOfUnimodular

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
