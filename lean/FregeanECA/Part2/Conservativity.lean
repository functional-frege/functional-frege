import FregeanECA.Conservativity
import FregeanECA.Part2.Theorems

/-! Part II remains conservative over the genuine single-sorted ECA calculus.
Full relational comprehension changes neither the objects nor their application
in the powerset expansion of an arbitrary ECA. Foundation soundness and
completeness therefore transfer actual proofs of every pure classical formula.
-/

namespace FregeanECA.Part2
open FFL FFL.FirstOrder Guarded Axioms Encoded

/-- Full impredicative relational comprehension adds no consequences in the
pure ECA language, including quantified and negated formulas. There is no
model-existence premise. -/
theorem bare_eca_full_algebra_provability (φ : Pure.Formula) :
    (Bare.theory ⊢ Bare.sentence φ) ↔
      (fullAlgebraTheory ⊢ Guarded.sentence φ.functional) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    haveI := sorts_of_model h
    let native := Guarded.extracted M
    have ts : FullTSConditions native.applicative :=
      (algebra_axioms_iff_conditions native).mp
        ((model_iff_valid (extractedRealization M) AlgebraAxiom).mp h)
    refine ⟨Bare.model native.applicative.pure, Bare.model_valid _ ts.eca, ?_⟩
    exact (Bare.model_truth native.applicative.pure φ).trans
      ((pure_validity native φ).symm.trans
        (Guarded.sentence_truth (extractedRealization M) inferInstance
          (fun _ => inferInstance) φ.functional).symm)
  · intro M _ _ _ h
    have eca := (Bare.models_theory_iff M).mp h
    let algebra := algebraOfPure eca
    let expanded := copyExpansion (fullRelations algebra)
    have ts : FullTSConditions expanded.applicative :=
      fullRelations_satisfies_full_TS algebra eca.extensional eca.nontrivial
    refine ⟨taggedModel expanded,
      taggedModel_valid expanded _ (algebra_axioms_of_conditions expanded ts), ?_⟩
    have same : expanded.applicative.pure = Bare.extracted M := rfl
    have sameTruth : (∀ o, φ.truth expanded.applicative.pure o) ↔
        (∀ o, φ.truth (Bare.extracted M) o) := by rw [same]
    exact (taggedModel_truth expanded φ.functional).trans
      ((pure_validity expanded φ).trans
        (sameTruth.trans (Bare.sentence_truth M φ).symm))

/-- The corresponding conservativity theorem for Part II's functional theory,
obtained from the actual shared-language proof equivalence. -/
theorem bare_eca_full_functional_provability (φ : Pure.Formula) :
    (Bare.theory ⊢ Bare.sentence φ) ↔
      (fullFunctionalTheory ⊢ Guarded.sentence φ.functional) :=
  (bare_eca_full_algebra_provability φ).trans
    (full_functional_algebra_provability φ.applicative).symm

end FregeanECA.Part2
