import FregeanECA.ActualFE
import FregeanECA.V2.Theorems
import FregeanECA.Part2.Conservativity

/-!
The optional FE extension of Part II.

This file does not change the original Part II axiom set. It defines its FE
extension separately and checks both proof interpretations. In particular,
FE does not raise interpretability strength. The separate completed
`Part2.MutualInterpretability` module also interprets this extension in Z2.
-/

namespace FregeanECA.Part2.FunctionExtensionality

open FFL FFL.FirstOrder Guarded Axioms Encoded

universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

def FullFEAxiom (p : Functional.Formula) : Prop :=
  FullFunctionalAxiom p ∨ p = functionExtensionality

abbrev fullFETheory := theory FullFEAxiom

theorem axioms_of_conditions (M : Functional.Interpretation D F R)
    (h : FullTFConditions M) (fe : Valid M functionExtensionality) :
    ∀ p, FullFEAxiom p → Valid M p := by
  intro p hp
  rcases hp with hp | rfl
  · exact full_functional_axioms_of_conditions M h p hp
  · exact fe

theorem conditions_of_axioms (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, FullFEAxiom p → Valid M p) :
    FullTFConditions M ∧ Valid M functionExtensionality :=
  ⟨conditions_of_full_functional_axioms M (fun p hp => h p (Or.inl hp)),
    h _ (Or.inr rfl)⟩

/-- A copy of the object sort has no duplicate functions with the same action. -/
theorem copy_valid_FE (M : Positive.Interpretation D R)
    (h : FullTSConditions M) :
    Valid (copyExpansion M) functionExtensionality := by
  intro objects functions predicates
  apply (functionExtensionality_truth _ _ _ _).mpr
  exact h.extensional

theorem copy_satisfies_full_FE (M : Positive.Interpretation D R)
    (h : FullTSConditions M) :
    ∀ p, FullFEAxiom p → Valid (copyExpansion M) p :=
  axioms_of_conditions _ (full_ts_expansion_satisfies_full_tf h) (copy_valid_FE M h)

/-- Adding FE preserves all existing proofs, including sentences with function
identity. The reverse interpretation below does not preserve that identity
vocabulary literally, so this is not a full-language conservativity claim. -/
theorem original_proof_in_extension (σ : Sentence language)
    (proof : fullFunctionalTheory ⊢ σ) : fullFETheory ⊢ σ := by
  apply LogicBridge.provable_of_eq_model_lift (proof := proof)
  intro M _ _ _ h
  have := sorts_of_model h
  have native := (model_iff_valid (extractedRealization M) FullFEAxiom).mp h
  refine ⟨M↓[language], ?_, Iff.rfl⟩
  exact (model_iff_valid (extractedRealization M) FullFunctionalAxiom).mpr
    (fun p hp => native p (Or.inl hp))

/-- The FE extension and full relational algebra agree on all shared formulas. -/
theorem shared_provability (p : Applicative.Formula) :
    (fullFETheory ⊢ sentence p.functional) ↔
      (fullAlgebraTheory ⊢ sentence p.functional) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    have := sorts_of_model h
    let native := extracted M
    have ts : FullTSConditions native.applicative :=
      (algebra_axioms_iff_conditions native).mp
        ((model_iff_valid (extractedRealization M) AlgebraAxiom).mp h)
    let expanded := copyExpansion native.applicative
    refine ⟨taggedModel expanded,
      taggedModel_valid expanded _ (copy_satisfies_full_FE _ ts), ?_⟩
    exact (taggedModel_truth expanded p.functional).trans
      ((shared_validity expanded p).trans
        ((shared_validity native p).symm.trans
          (sentence_truth (extractedRealization M) inferInstance
            (fun _ => inferInstance) p.functional).symm))
  · intro M _ _ _ h
    have := sorts_of_model h
    let native := extracted M
    have tf : FullTFConditions native :=
      (conditions_of_axioms native
        ((model_iff_valid (extractedRealization M) FullFEAxiom).mp h)).1
    exact ⟨M↓[language], (model_iff_valid (extractedRealization M) AlgebraAxiom).mpr
      (algebra_axioms_of_conditions native (full_tf_reduct_satisfies_full_ts tf)), Iff.rfl⟩

/-- The explicit copy-function translation transfers every functional proof
of the FE extension, including full comprehension and primitive identity. -/
theorem proof_interprets_in_algebra (p : Functional.Formula)
    (proof : fullFETheory ⊢ sentence p) :
    fullAlgebraTheory ⊢ sentence (Interpretability.translate p).functional := by
  apply LogicBridge.provable_of_eq_model_lift (proof := proof)
  intro M _ _ _ h
  have := sorts_of_model h
  let native := extracted M
  have ts : FullTSConditions native.applicative :=
    (algebra_axioms_iff_conditions native).mp
      ((model_iff_valid (extractedRealization M) AlgebraAxiom).mp h)
  let expanded := copyExpansion native.applicative
  refine ⟨taggedModel expanded,
    taggedModel_valid expanded _ (copy_satisfies_full_FE _ ts), ?_⟩
  exact (taggedModel_truth expanded p).trans
    ((Interpretability.translation_validity native p).trans
      (sentence_truth (extractedRealization M) inferInstance (fun _ => inferInstance)
        (Interpretability.translate p).functional).symm)

/-- Interpretation of the stronger theory in the original theory by replacing
its function sort with a copy of its object sort. -/
theorem proof_interprets_in_original (p : Functional.Formula)
    (proof : fullFETheory ⊢ sentence p) :
    fullFunctionalTheory ⊢ sentence (Interpretability.translate p).functional :=
  (full_functional_algebra_provability _).mpr (proof_interprets_in_algebra p proof)

theorem mutual_proof_interpretations :
    (∀ p : Functional.Formula, (fullFunctionalTheory ⊢ sentence p) →
      (fullFETheory ⊢ sentence p)) ∧
    (∀ p : Functional.Formula, (fullFETheory ⊢ sentence p) →
      (fullFunctionalTheory ⊢ sentence (Interpretability.translate p).functional)) :=
  ⟨fun p => original_proof_in_extension (sentence p), proof_interprets_in_original⟩

/-- The statement targets the active v2 full algebra, not just its predecessor. -/
theorem shared_v2_provability (p : Applicative.Formula) :
    (fullFETheory ⊢ sentence p.functional) ↔
      (V2.combinedFullTheory ⊢ sentence p.functional) :=
  (shared_provability p).trans (V2.combined_full_original_provability _).symm

theorem proof_interprets_in_v2 (p : Functional.Formula)
    (proof : fullFETheory ⊢ sentence p) :
    V2.combinedFullTheory ⊢ sentence (Interpretability.translate p).functional :=
  (V2.combined_full_original_provability _).mpr (proof_interprets_in_algebra p proof)

/-- FE retains the already proved conservativity over the entire pure
classical ECA language, not just equations between translated lambda terms. -/
theorem pure_conservativity (p : Pure.Formula) :
    (Bare.theory ⊢ Bare.sentence p) ↔
      (fullFETheory ⊢ sentence p.functional) :=
  (bare_eca_full_algebra_provability p).trans (shared_provability p.applicative).symm

theorem consistent : Entailment.Consistent fullFETheory := by
  rw [Entailment.consistent_iff_unprovable_bot]
  intro proof
  have proof' := (encoded_falsum_provability FullFEAxiom).mpr proof
  have falseInAlgebra := (shared_provability .falsum).mp proof'
  exact full_neither_theory_proves_false.1
    ((encoded_falsum_provability AlgebraAxiom).mp falseInAlgebra)

end FregeanECA.Part2.FunctionExtensionality

#print axioms FregeanECA.Part2.FunctionExtensionality.mutual_proof_interpretations
#print axioms FregeanECA.Part2.FunctionExtensionality.shared_v2_provability
#print axioms FregeanECA.Part2.FunctionExtensionality.pure_conservativity
#print axioms FregeanECA.Part2.FunctionExtensionality.consistent

