import FregeanECA.V2.Axioms
import FregeanECA.Theorems
import FregeanECA.Part2.Theorems

/-! Actual derivability equivalences for the v2 axioms, using the existing
soundness/completeness bridge. Standalone equivalences assume no ECA laws. -/
namespace FregeanECA.V2
open FFL FFL.FirstOrder Guarded Axioms Encoded

abbrev pcAlgebraTheory := theory PCAxiom
abbrev positiveComprehensionTheory := theory PCComprehensionAxiom
abbrev fcAlgebraTheory := theory FCAxiom
abbrev fullComprehensionTheory := theory FCComprehensionAxiom
abbrev combinedPositiveTheory := theory (WithECA PCAxiom)
abbrev combinedFullTheory := theory (WithECA FCAxiom)

/-- Standalone PC-algebra = PC, for every sentence of the ambient language. -/
theorem pc_algebra_comprehension_provability (σ : Sentence language) :
    (pcAlgebraTheory ⊢ σ) ↔ (positiveComprehensionTheory ⊢ σ) :=
  same_validity_same_proofs _ _ (fun M =>
    (pc_axioms_iff_conditions M).trans
      ((pcAlgebra_iff_positiveComprehension M.applicative).trans
        (pc_comprehension_axioms_iff M).symm)) σ

/-- Standalone FC-algebra = FC, with C and predicate projection included. -/
theorem fc_algebra_comprehension_provability (σ : Sentence language) :
    (fcAlgebraTheory ⊢ σ) ↔ (fullComprehensionTheory ⊢ σ) :=
  same_validity_same_proofs _ _ (fun M =>
    (fc_axioms_iff_conditions M).trans
      ((fcAlgebra_iff_fullComprehension M.applicative).trans
        (fc_comprehension_axioms_iff M).symm)) σ

/-- Adding ECA makes the new positive presentation equivalent to the old one. -/
theorem combined_positive_original_provability (σ : Sentence language) :
    (combinedPositiveTheory ⊢ σ) ↔ (specificationTheory ⊢ σ) :=
  same_validity_same_proofs _ _ (fun M =>
    (combined_pc_axioms_iff M).trans (specification_axioms_iff_conditions M).symm) σ

/-- Adding ECA makes the new full presentation equivalent to the old one. -/
theorem combined_full_original_provability (σ : Sentence language) :
    (combinedFullTheory ⊢ σ) ↔ (Part2.fullAlgebraTheory ⊢ σ) :=
  same_validity_same_proofs _ _ (fun M =>
    (combined_fc_axioms_iff M).trans (Part2.algebra_axioms_iff_conditions M).symm) σ

/-- The original functional Part I theory and the new algebra share proofs. -/
theorem functional_combined_positive_provability (p : Applicative.Formula) :
    (functionalTheory ⊢ sentence p.functional) ↔
      (combinedPositiveTheory ⊢ sentence p.functional) :=
  (functional_specification_provability p).trans
    (combined_positive_original_provability _).symm

/-- The original functional Part II theory and the new algebra share proofs. -/
theorem functional_combined_full_provability (p : Applicative.Formula) :
    (Part2.fullFunctionalTheory ⊢ sentence p.functional) ↔
      (combinedFullTheory ⊢ sentence p.functional) :=
  (Part2.full_functional_algebra_provability p).trans
    (combined_full_original_provability _).symm

/-- Consistency is transferred through the proved equivalence, not assumed. -/
theorem combined_neither_proves_false :
    (combinedPositiveTheory ⊬ (⊥ : Sentence language)) ∧
    (combinedFullTheory ⊬ (⊥ : Sentence language)) := by
  constructor
  · intro proof
    exact Encoded.neither_theory_proves_false.2
      ((combined_positive_original_provability _).mp proof)
  · intro proof
    exact Part2.full_neither_theory_proves_false.1
      ((combined_full_original_provability _).mp proof)

end FregeanECA.V2
