import FregeanECA.Part2.Theorems
import Foundation.FirstOrder.SetTheory.Basic.Axioms

namespace FregeanECA.Part2
open FFL FFL.FirstOrder Guarded Axioms Encoded

/-- Strengthening comprehension preserves every Part I Fregean theorem,
in the complete ambient language and the actual Foundation proof calculus. -/
theorem preserves_part_one_functional (sentence : Sentence language)
    (proof : functionalTheory ⊢ sentence) : fullFunctionalTheory ⊢ sentence := by
  apply LogicBridge.provable_of_eq_model_lift (proof := proof)
  intro M _ _ _ h
  haveI := sorts_of_model h
  have full : FullTFConditions (extracted M) :=
    (full_functional_axioms_iff_conditions _).mp
      ((model_iff_valid (extractedRealization M) FullFunctionalAxiom).mp h)
  refine ⟨M↓[language], ?_, Iff.rfl⟩
  exact (model_iff_valid (extractedRealization M) FunctionalAxiom).mpr
    (functional_axioms_of_conditions _ full.toTFConditions)

/-- The strengthened relational theory retains every Part I specification
theorem; the computational axioms have not been weakened. -/
theorem preserves_part_one_algebraic (sentence : Sentence language)
    (proof : specificationTheory ⊢ sentence) : fullAlgebraTheory ⊢ sentence := by
  apply LogicBridge.provable_of_eq_model_lift (proof := proof)
  intro M _ _ _ h
  haveI := sorts_of_model h
  have full : FullTSConditions (extracted M).applicative :=
    (algebra_axioms_iff_conditions _).mp
      ((model_iff_valid (extractedRealization M) AlgebraAxiom).mp h)
  refine ⟨M↓[language], ?_, Iff.rfl⟩
  exact (model_iff_valid (extractedRealization M) SpecificationAxiom).mpr
    (specification_axioms_of_conditions _ full.toTSConditions)

/-- The displayed external consistency implication, using the library's
actual ZFC theory. The concrete Lean model already establishes the conclusion;
this does not assert an internal ZFC derivation of model existence. -/
theorem full_relative_consistency :
    Entailment.Consistent FirstOrder.SetTheory.ZermeloFraenkelChoice →
      Entailment.Consistent fullAlgebraTheory ∧
      Entailment.Consistent fullFunctionalTheory :=
  fun _ => ⟨full_algebra_consistent, full_functional_consistent⟩

end FregeanECA.Part2
