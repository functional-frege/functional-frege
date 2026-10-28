import FregeanECA.Bare
import FregeanECA.Theorems

/-! Conservativity over the genuine single-sorted ECA calculus. The left-hand
theory below has only K, S, application, equality and the four ECA axioms.
Foundation soundness and completeness transfer actual sequent-calculus proofs.
-/
namespace FregeanECA.Encoded
open FFL FFL.FirstOrder Guarded Axioms
universe u v w

theorem pure_validity {D : Type u} {F : Type v} {R : Nat → Type w}
    [Nonempty F] [∀ n, Nonempty (R n)] (M : Functional.Interpretation D F R)
    (φ : Pure.Formula) : Valid M φ.functional ↔ ∀ o, φ.truth M.applicative.pure o := by
  classical
  constructor
  · intro h o
    let f : Nat → F := fun _ => Classical.choice (inferInstance : Nonempty F)
    let r : Positive.PredicateAssignment R := fun n _ => Classical.choice (inferInstance : Nonempty (R n))
    exact (pure_functional_embedding_preserves_truth M φ o f r).mp (h o f r)
  · intro h o f r
    exact (pure_functional_embedding_preserves_truth M φ o f r).mpr (h o)

def algebraOfPure {D : Type u} {P : Pure.Interpretation D} (h : Pure.ECAConditions P) :
    Frege.CombinatoryAlgebra D where
  apply := P.apply
  constant := P.constantK
  distribute := P.constantS
  constant_returns_first_argument := h.constant
  distribute_applies_the_same_argument := h.distribute

/-- Every classical pure formula is conservative, including quantified and
negated formulas; this is not restricted to equations or positive formulas. -/
theorem bare_eca_specification_provability (φ : Pure.Formula) :
    (Bare.theory ⊢ Bare.sentence φ) ↔
      (specificationTheory ⊢ Guarded.sentence φ.functional) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    haveI := sorts_of_model h
    let native := Guarded.extracted M
    have ts : TSConditions native.applicative :=
      (specification_axioms_iff_conditions native).mp
        ((model_iff_valid (extractedRealization M) SpecificationAxiom).mp h)
    refine ⟨Bare.model native.applicative.pure, Bare.model_valid _ ts.eca, ?_⟩
    exact (Bare.model_truth native.applicative.pure φ).trans
      ((pure_validity native φ).symm.trans
        (Guarded.sentence_truth (extractedRealization M) inferInstance (fun _ => inferInstance) φ.functional).symm)
  · intro M _ _ _ h
    have eca := (Bare.models_theory_iff M).mp h
    let algebra := algebraOfPure eca
    let expanded := copyExpansion (fullRelations algebra)
    have ts : TSConditions expanded.applicative :=
      fullRelations_satisfies_TS algebra eca.extensional eca.nontrivial
    refine ⟨taggedModel expanded,
      taggedModel_valid expanded _ (specification_axioms_of_conditions expanded ts), ?_⟩
    have same : expanded.applicative.pure = Bare.extracted M := rfl
    have sameTruth : (∀ o, φ.truth expanded.applicative.pure o) ↔
        (∀ o, φ.truth (Bare.extracted M) o) := by rw [same]
    exact (taggedModel_truth expanded φ.functional).trans
      ((pure_validity expanded φ).trans
        (sameTruth.trans (Bare.sentence_truth M φ).symm))

/-- The pure-object conservativity claim for the functional presentation,
using the same bare ECA theory and the actual functional theory. -/
theorem bare_eca_functional_provability (φ : Pure.Formula) :
    (Bare.theory ⊢ Bare.sentence φ) ↔
      (functionalTheory ⊢ Guarded.sentence φ.functional) :=
  (bare_eca_specification_provability φ).trans
    (functional_specification_provability φ.applicative).symm

end FregeanECA.Encoded
