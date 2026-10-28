import FregeanECA.Part2.AlgebraAxioms
import FregeanECA.Part2.Correspondence
import FregeanECA.Theorems
import FregeanECA.Interpretability

namespace FregeanECA.Part2
open FFL FFL.FirstOrder Guarded Axioms Encoded

abbrev fullFunctionalTheory := theory FullFunctionalAxiom
abbrev fullRelationalTheory := theory FullRelationalAxiom
abbrev fullAlgebraTheory := theory AlgebraAxiom

/-- Actual deductive equivalence of the two added closure schemas and full
comprehension, for every sentence of the encoded ambient language. -/
theorem algebra_comprehension_provability (σ : Sentence language) :
    (fullAlgebraTheory ⊢ σ) ↔ (fullRelationalTheory ⊢ σ) :=
  same_validity_same_proofs _ _ (fun M =>
    (algebra_axioms_iff_conditions M).trans (full_relational_axioms_iff_conditions M).symm) σ

/-- The strengthened Fregean and algebraic presentations have the same actual
shared-language proofs, including negation and relation identity. -/
theorem full_functional_algebra_provability (p : Applicative.Formula) :
    (fullFunctionalTheory ⊢ sentence p.functional) ↔
      (fullAlgebraTheory ⊢ sentence p.functional) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    haveI := sorts_of_model h
    let native := extracted M
    have ts : FullTSConditions native.applicative :=
      (algebra_axioms_iff_conditions native).mp
        ((model_iff_valid (extractedRealization M) AlgebraAxiom).mp h)
    let expanded := copyExpansion native.applicative
    refine ⟨taggedModel expanded, taggedModel_valid expanded _
      (full_functional_axioms_of_conditions _ (full_ts_expansion_satisfies_full_tf ts)), ?_⟩
    exact (taggedModel_truth expanded p.functional).trans
      ((shared_validity expanded p).trans
        ((shared_validity native p).symm.trans
          (sentence_truth (extractedRealization M) inferInstance
            (fun _ => inferInstance) p.functional).symm))
  · intro M _ _ _ h
    haveI := sorts_of_model h
    let native := extracted M
    have tf : FullTFConditions native :=
      (full_functional_axioms_iff_conditions native).mp
        ((model_iff_valid (extractedRealization M) FullFunctionalAxiom).mp h)
    exact ⟨M↓[language], (model_iff_valid (extractedRealization M) AlgebraAxiom).mpr
      (algebra_axioms_of_conditions native (full_tf_reduct_satisfies_full_ts tf)), Iff.rfl⟩

theorem full_consistency_equivalence :
    Entailment.Consistent fullFunctionalTheory ↔ Entailment.Consistent fullAlgebraTheory := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr ((encoded_falsum_provability FullFunctionalAxiom).symm.trans
    ((full_functional_algebra_provability .falsum).trans
      (encoded_falsum_provability AlgebraAxiom)))

/-- Full-language proof transport for the copy-function interpretation. -/
theorem full_functional_proof_interprets (p : Functional.Formula)
    (proof : fullFunctionalTheory ⊢ sentence p) :
    fullAlgebraTheory ⊢ sentence (Interpretability.translate p).functional := by
  apply LogicBridge.provable_of_eq_model_lift (proof := proof)
  intro M _ _ _ h
  haveI := sorts_of_model h
  let native := extracted M
  have ts : FullTSConditions native.applicative :=
    (algebra_axioms_iff_conditions native).mp
      ((model_iff_valid (extractedRealization M) AlgebraAxiom).mp h)
  let expanded := copyExpansion native.applicative
  refine ⟨taggedModel expanded, taggedModel_valid expanded _
    (full_functional_axioms_of_conditions _ (full_ts_expansion_satisfies_full_tf ts)), ?_⟩
  exact (taggedModel_truth expanded p).trans
    ((Interpretability.translation_validity native p).trans
      (sentence_truth (extractedRealization M) inferInstance (fun _ => inferInstance)
        (Interpretability.translate p).functional).symm)

/-- One concrete algebraic model verifies all literal B, C, Q axiom instances. -/
theorem full_algebra_model : taggedModel openFunctional ⊧* fullAlgebraTheory :=
  taggedModel_valid _ _ (algebra_axioms_of_conditions _ openSpecification_satisfies_full_TS)

theorem full_algebra_consistent : Entailment.Consistent fullAlgebraTheory :=
  LogicBridge.consistent_of_structure _ full_algebra_model

/-- Functional consistency follows through equivalence, not a second model proof. -/
theorem full_functional_consistent : Entailment.Consistent fullFunctionalTheory :=
  full_consistency_equivalence.mpr full_algebra_consistent

theorem full_neither_theory_proves_false :
    (fullAlgebraTheory ⊬ (⊥ : Sentence language)) ∧
      (fullFunctionalTheory ⊬ (⊥ : Sentence language)) :=
  ⟨Entailment.consistent_iff_unprovable_bot.mp full_algebra_consistent,
    Entailment.consistent_iff_unprovable_bot.mp full_functional_consistent⟩

end FregeanECA.Part2
