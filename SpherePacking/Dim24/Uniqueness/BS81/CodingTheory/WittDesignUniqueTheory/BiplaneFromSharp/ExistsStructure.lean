module
public import
  SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.WittDesignUniqueTheory.SharpGolayAux.Extraction

/-!
# Existence of a biplane structure from a sharp Golay input

This is the "existence only" statement corresponding to the construction carried out in
`SharpGolayAux.Extraction.extract`, which chooses all data deterministically.

Keeping this as a derived lemma avoids duplicating the full construction.
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory

namespace GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneFromSharp

noncomputable section

/-- From a sharp BS81 Golay input code, one can extract a biplane structure. -/
public theorem exists_biplaneStructure_of_sharp
    (C : Code 24) (hC : IsSharpBS81GolayInput C) :
    ∃ _D : Biplane.Structure, True :=
  ⟨(SharpGolayUniqueFromBiplaneAux.extract C hC).D, trivial⟩

end

end GolayUniquenessSteps.WittDesignUniqueTheory.BiplaneFromSharp
end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory
