import FregeanECA.TheoryEncoding
import FregeanECA.AxiomsRelational
import FregeanECA.Concrete

/-! Instantiated proof-calculus consequences of the model constructions. -/
namespace FregeanECA.Encoded
open FFL FFL.FirstOrder Guarded Axioms

abbrev functionalTheory := theory FunctionalAxiom
abbrev specificationTheory := theory SpecificationAxiom
abbrev comprehensionTheory := theory RelationalAxiom

theorem shared_validity {D : Type u} {F : Type v} {R : Nat → Type w}
    [Nonempty F] (M : Functional.Interpretation D F R) (p : Applicative.Formula) :
    Valid M p.functional ↔ ∀ o r, p.truth M.applicative o r := by
  constructor
  · intro h o r
    exact (shared_formula_preserves_truth M p o (fun _ => Classical.choice inferInstance) r).mp
      (h o (fun _ => Classical.choice inferInstance) r)
  · intro h o f r
    exact (shared_formula_preserves_truth M p o f r).mpr (h o r)

/-- Companion result, not printed in the paper: equality of actual first-order
provability, not a
definition of proof as semantic validity. -/
theorem specification_comprehension_provability (σ : Sentence language) :
    (specificationTheory ⊢ σ) ↔ (comprehensionTheory ⊢ σ) :=
  same_validity_same_proofs _ _
    (fun M => specification_and_relational_axioms_same_models M) σ

/-- Companion to `thm:correspondence` for every classical sentence of the shared
language, including
relation identity and quantification. Free variables are universally closed. -/
theorem functional_specification_provability (p : Applicative.Formula) :
    (functionalTheory ⊢ sentence p.functional) ↔
    (specificationTheory ⊢ sentence p.functional) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    letI := sorts_of_model h
    let native := extracted M
    have ts : TSConditions native.applicative :=
      (specification_axioms_iff_conditions native).mp
        ((model_iff_valid (extractedRealization M) SpecificationAxiom).mp h)
    let expanded := copyExpansion native.applicative
    refine ⟨taggedModel expanded,
      taggedModel_valid expanded _ (functional_axioms_of_conditions _ (ts_expansion_satisfies_tf ts)), ?_⟩
    exact (taggedModel_truth expanded p.functional).trans
      ((shared_validity expanded p).trans
      ((shared_validity native p).symm.trans
        (sentence_truth (extractedRealization M) inferInstance (fun _ => inferInstance) p.functional).symm))
  · intro M _ _ _ h
    letI := sorts_of_model h
    let native := extracted M
    have tf : TFConditions native := (functional_axioms_iff_conditions native).mp
      ((model_iff_valid (extractedRealization M) FunctionalAxiom).mp h)
    refine ⟨M↓[language], ?_, Iff.rfl⟩
    exact (model_iff_valid (extractedRealization M) SpecificationAxiom).mpr
      (specification_axioms_of_conditions native (tf_reduct_satisfies_ts tf))

instance open_object_nonempty : Nonempty OpenObject := ⟨openSpecification.constantK⟩

/-- The explicit open beta-eta model satisfies every concrete functional axiom. -/
theorem open_model_functional : taggedModel openFunctional ⊧* functionalTheory :=
  taggedModel_valid _ _ (functional_axioms_of_conditions _ openFunctional_satisfies_TF)

theorem open_model_specification : taggedModel openFunctional ⊧* specificationTheory :=
  taggedModel_valid _ _ (specification_axioms_of_conditions _ openSpecification_satisfies_TS)

/-- Universal closure and sort guards preserve the contradiction sentence. -/
theorem encoded_falsum_truth {M : Type} [Nonempty M] [Structure language M]
    [Structure.Eq language M] [SortCorrect M] :
    (M↓[language] ⊧ sentence .falsum) ↔ (M↓[language] ⊧ (⊥ : Sentence language)) := by
  have truth := sentence_truth (extractedRealization M) inferInstance
    (fun _ => inferInstance) .falsum
  constructor
  · intro h
    exact truth.mp h
      (fun _ => (extracted M).applicative.constantK)
      (fun _ => Classical.choice inferInstance)
      (fun _ _ => Classical.choice inferInstance)
  · intro h
    exact False.elim h

theorem encoded_falsum_provability (axioms : Functional.Formula → Prop) :
    (theory axioms ⊢ sentence .falsum) ↔
      (theory axioms ⊢ (⊥ : Sentence language)) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    letI := sorts_of_model h
    exact ⟨M↓[language], h, encoded_falsum_truth⟩
  · intro M _ _ _ h
    letI := sorts_of_model h
    exact ⟨M↓[language], h, encoded_falsum_truth.symm⟩

/-- Consistency equivalence is just the shared-language theorem at false. -/
theorem consistency_equivalence :
    Entailment.Consistent functionalTheory ↔ Entailment.Consistent specificationTheory := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr ((encoded_falsum_provability FunctionalAxiom).symm.trans
    ((functional_specification_provability .falsum).trans
      (encoded_falsum_provability SpecificationAxiom)))

/-- The single model-existence consistency proof, on the simpler side. -/
theorem specification_consistent : Entailment.Consistent specificationTheory :=
  LogicBridge.consistent_of_structure _ open_model_specification

/-- Functional consistency is transferred; it has no second model proof. -/
theorem functional_consistent : Entailment.Consistent functionalTheory :=
  consistency_equivalence.mpr specification_consistent

theorem both_theories_consistent :
    Entailment.Consistent functionalTheory ∧ Entailment.Consistent specificationTheory :=
  ⟨functional_consistent, specification_consistent⟩

theorem neither_theory_proves_false :
    (functionalTheory ⊬ (⊥ : Sentence language)) ∧
    (specificationTheory ⊬ (⊥ : Sentence language)) :=
  ⟨Entailment.consistent_iff_unprovable_bot.mp functional_consistent,
    Entailment.consistent_iff_unprovable_bot.mp specification_consistent⟩

end FregeanECA.Encoded
