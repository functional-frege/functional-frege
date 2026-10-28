import FregeanECA.Theorems
import FregeanECA.ActualFE
import FregeanECA.CounterexampleSyntax

namespace FregeanECA.Encoded
open FFL FFL.FirstOrder Guarded Axioms

/-- A concrete sorted countermodel refutes an actual sequent-calculus proof. -/
theorem unprovable_of_countermodel {D F : Type} {R : Nat → Type}
    [Nonempty D] [Nonempty F] [∀ n, Nonempty (R n)]
    (M : Functional.Interpretation D F R) (axioms : Functional.Formula → Prop)
    (p : Functional.Formula) (holds : ∀ q, axioms q → Valid M q)
    (fails : ¬ Valid M p) : theory axioms ⊬ sentence p := by
  intro proof
  exact fails ((taggedModel_truth M p).mp
    (Theory.Proof.sound_small proof (taggedModel_valid M axioms holds)))

/-- Proposition 4.2: TF cannot prove primitive function extensionality. -/
theorem function_extensionality_not_provable :
    functionalTheory ⊬ sentence functionExtensionality :=
  unprovable_of_countermodel openDuplicate _ _
    actual_functional_axioms_have_an_FE_countermodel.1
    actual_functional_axioms_have_an_FE_countermodel.2

def closureNontrivialAxiom (p : Functional.Formula) : Prop :=
  ClosureAxiom p ∨ p = nontriviality

abbrev closureNontrivialTheory := theory closureNontrivialAxiom

/-- Proposition 6.1: even adding nontriviality to the five closure families
does not prove the parameter-singleton instance of positive comprehension. -/
theorem closure_does_not_prove_positive_comprehension :
    closureNontrivialTheory ⊬ sentence CounterexampleSyntax.singletonComprehension := by
  letI : ∀ n, Nonempty (CounterexampleSyntax.Relations n) :=
    fun n => ⟨Counterexample.universalRelation (n + 1)⟩
  apply unprovable_of_countermodel CounterexampleSyntax.invariantModel
  · intro p hp
    rcases hp with hc | rfl
    · exact CounterexampleSyntax.every_actual_closure_axiom_is_valid p hc
    · exact CounterexampleSyntax.actual_nontriviality_is_valid
  · exact CounterexampleSyntax.actual_singleton_comprehension_is_not_valid

end FregeanECA.Encoded
