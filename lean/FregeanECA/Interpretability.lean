import FregeanECA.TheoryEncoding

/-! Actual proof transport for the full functional language. Function variables
are interpreted as object variables in a disjoint part of the variable supply.
Primitive function equality is translated to object equality; the model lift
uses the copy-function expansion, where that interpretation is exact. -/

namespace FregeanECA.Interpretability
open FFL FFL.FirstOrder Guarded Axioms Encoded
universe u v w

def objectVariables (i : Nat) : Nat := 2 * i
def functionVariables (i : Nat) : Nat := 2 * i + 1

theorem objectVariables_injective : Function.Injective objectVariables := by
  intro i j same
  simp only [objectVariables] at same
  omega

theorem functionVariables_injective : Function.Injective functionVariables := by
  intro i j same
  simp only [functionVariables] at same
  omega

theorem variable_ranges_disjoint (i j : Nat) : objectVariables i ≠ functionVariables j := by
  simp only [objectVariables, functionVariables]
  omega

def translate (φ : Functional.Formula) : Applicative.Formula :=
  φ.translate objectVariables functionVariables

/-- Both arbitrary assignments and their interleaved merger are accounted for,
so the result applies to the universal closures of open formulas as well. -/
theorem copy_translation_validity {D : Type u} {R : Nat → Type w}
    (M : Positive.Interpretation D R) (φ : Functional.Formula) :
    Valid (copyExpansion M) φ ↔
      ∀ (objects : Nat → D) (predicates : Positive.PredicateAssignment R),
        (translate φ).truth M objects predicates := by
  constructor
  · intro valid target predicates
    let objects := fun i => target (objectVariables i)
    let functions := fun i => target (functionVariables i)
    have bindings : Functional.Bindings (copyExpansion M)
        objectVariables functionVariables objects functions target := ⟨fun _ => rfl, fun _ => rfl⟩
    exact (copy_expansion_preserves_full_truth M φ _ _ _ _ _ _ bindings).mp
      (valid objects functions predicates)
  · intro valid objects functions predicates
    let target := Functional.mergedParameters (copyExpansion M) objects functions
    have bindings : Functional.Bindings (copyExpansion M)
        objectVariables functionVariables objects functions target := {
      object := fun i => Functional.mergedParameters_even (copyExpansion M) objects functions i
      function := fun i => Functional.mergedParameters_odd (copyExpansion M) objects functions i }
    exact (copy_expansion_preserves_full_truth M φ _ _ _ _ _ _ bindings).mpr
      (valid target predicates)

theorem translation_validity {D : Type u} {F : Type v} {R : Nat → Type w}
    [Nonempty F] (M : Functional.Interpretation D F R) (φ : Functional.Formula) :
    Valid (copyExpansion M.applicative) φ ↔ Valid M (translate φ).functional := by
  constructor
  · intro valid objects functions predicates
    exact (shared_formula_preserves_truth M (translate φ) objects functions predicates).mpr
      ((copy_translation_validity M.applicative φ).mp valid objects predicates)
  · intro valid
    apply (copy_translation_validity M.applicative φ).mpr
    intro objects predicates
    let functions : Nat → F := fun _ => Classical.choice (inferInstance : Nonempty F)
    exact (shared_formula_preserves_truth M (translate φ) objects functions predicates).mp
      (valid objects functions predicates)

/-- Every actual TF theorem, not merely a shared-language theorem, translates
to an actual TS theorem in Foundation's classical first-order calculus. -/
theorem functional_proof_interprets_in_specification (φ : Functional.Formula)
    (proof : theory FunctionalAxiom ⊢ sentence φ) :
    theory SpecificationAxiom ⊢ sentence (translate φ).functional := by
  apply LogicBridge.provable_of_eq_model_lift (proof := proof)
  intro M _ _ _ satisfies
  letI := sorts_of_model satisfies
  let native := extracted M
  have conditions : TSConditions native.applicative :=
    (specification_axioms_iff_conditions native).mp
      ((model_iff_valid (extractedRealization M) SpecificationAxiom).mp satisfies)
  let expanded := copyExpansion native.applicative
  refine ⟨taggedModel expanded,
    taggedModel_valid expanded _
      (functional_axioms_of_conditions expanded (ts_expansion_satisfies_tf conditions)), ?_⟩
  exact (taggedModel_truth expanded φ).trans
    ((translation_validity native φ).trans
      (sentence_truth (extractedRealization M) inferInstance
        (fun _ => inferInstance) (translate φ).functional).symm)

/-- In the other direction, the interpretation keeps the shared sorts and
operations and simply introduces the defined applicative notation in TF. -/
theorem specification_proof_interprets_in_functional (φ : Applicative.Formula)
    (proof : theory SpecificationAxiom ⊢ sentence φ.functional) :
    theory FunctionalAxiom ⊢ sentence φ.functional := by
  apply LogicBridge.provable_of_eq_model_lift (proof := proof)
  intro M _ _ _ satisfies
  letI := sorts_of_model satisfies
  let native := extracted M
  have conditions : TFConditions native :=
    (functional_axioms_iff_conditions native).mp
      ((model_iff_valid (extractedRealization M) FunctionalAxiom).mp satisfies)
  refine ⟨M↓[language], ?_, Iff.rfl⟩
  exact (model_iff_valid (extractedRealization M) SpecificationAxiom).mpr
    (specification_axioms_of_conditions native (tf_reduct_satisfies_ts conditions))

/-- Explicit theorem preservation in both interpretations, for every formula
of each source language and hence every source sentence. -/
theorem mutual_interpretations_preserve_proofs :
    (∀ φ : Functional.Formula, (theory FunctionalAxiom ⊢ sentence φ) →
      (theory SpecificationAxiom ⊢ sentence (translate φ).functional)) ∧
    (∀ φ : Applicative.Formula, (theory SpecificationAxiom ⊢ sentence φ.functional) →
      (theory FunctionalAxiom ⊢ sentence φ.functional)) :=
  ⟨functional_proof_interprets_in_specification,
    specification_proof_interprets_in_functional⟩

end FregeanECA.Interpretability

