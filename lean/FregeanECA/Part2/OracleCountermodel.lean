import FregeanECA.Part2.OracleCountermodelBase
import FregeanECA.Part2.OracleTableBindings
import FregeanECA.Part2.OracleTableMatrix

/-! The actual quantified table formula in the paper's applicative syntax.
It uses available finite relations as witnesses, not external predicates.
-/
namespace FregeanECA.Part2.Oracle

open FFL FFL.FirstOrder Positive OracleTarget

def targetSatisfactionFormula : Applicative.Formula :=
  .existsPredicate 1 (.existsPredicate 2
    (OracleTarget.translate tableSlots (fun _ : Fin 1 => .var 0) satisfactionMatrix))

theorem target_satisfaction_iff (operations : Operations)
    (objects : ObjectAssignment Nat) :
    targetSatisfactionFormula.truth (definableModel (withSyntax operations))
      objects (baseAssignment (withSyntax operations)) ↔
    ∃ truth : Relations (withSyntax operations) 1,
      ∃ values : Relations (withSyntax operations) 2,
        satisfactionMatrix.Evalb
          (s := tabledStructure (withSyntax operations) truth values)
          (fun _ => objects 0) := by
  change (∃ truth : Relations (withSyntax operations) 1,
      ∃ values : Relations (withSyntax operations) 2,
        (OracleTarget.translate tableSlots (fun _ : Fin 1 => .var 0) satisfactionMatrix).truth
          (definableModel (withSyntax operations)) objects
          (tableAssignment (withSyntax operations) truth values)) ↔ _
  apply exists_congr
  intro truth
  apply exists_congr
  intro values
  letI := tabledStructure (withSyntax operations) truth values
  exact translation_truth (definableModel (withSyntax operations))
    (tableAssignment (withSyntax operations) truth values) tableSlots
    (table_bindings (withSyntax operations) truth values) satisfactionMatrix
    (fun _ => .var 0) (fun _ => objects 0) objects (fun _ => rfl)

/-- One fixed applicative formula agrees with the actual truth of every
encoded sentence. Its two predicate quantifiers range over available,
first-order-definable relations. -/
theorem target_satisfaction_on_sentence_codes (operations : Operations)
    (sentence : Sentence language) (objects : ObjectAssignment Nat) :
    targetSatisfactionFormula.truth (definableModel (withSyntax operations))
      (assignTuple 1 (fun _ => Encodable.encode sentence) objects)
      (baseAssignment (withSyntax operations)) ↔
    sentence.Evalb (s := modelStructure (withSyntax operations)) Fin.elim0 := by
  rw [target_satisfaction_iff]
  exact exists_definable_tables_iff operations sentence

/-- The concrete first-order-definable relation model cannot satisfy Q.
There is no model-existence, satisfaction, or nondefinability premise. -/
theorem definable_model_fails_predicate_projection (operations : Operations) :
    ¬ PredicateProjection (definableModel (withSyntax operations)) := by
  apply predicate_projection_fails_of_truth_formula (withSyntax operations)
    targetSatisfactionFormula (fun _ => 0) (baseAssignment (withSyntax operations))
  intro sentence
  exact target_satisfaction_on_sentence_codes operations sentence (fun _ => 0)

theorem definable_model_fails_full_comprehension (operations : Operations) :
    ¬ HasFullComprehension (definableModel (withSyntax operations)) := by
  intro full
  exact definable_model_fails_predicate_projection operations
    (full_comprehension_implies_classical_closure _ full).predicateProjection

/-- The paper's countermodel: ECA, all five positive closure conditions,
and complementation hold, while predicate projection fails. -/
theorem complemented_specification_without_predicate_projection (operations : Operations) :
    TSConditions (definableModel (withSyntax operations)) ∧
    ComplementClosure (definableModel (withSyntax operations)) ∧
    ¬ HasFullComprehension (definableModel (withSyntax operations)) ∧
    ¬ PredicateProjection (definableModel (withSyntax operations)) :=
  ⟨(definable_model_satisfies_B_and_C (withSyntax operations)).1,
   (definable_model_satisfies_B_and_C (withSyntax operations)).2,
   definable_model_fails_full_comprehension operations,
   definable_model_fails_predicate_projection operations⟩

/-- Every literal complemented specification axiom is valid in the same
countermodel. The constructor argument is only membership in the syntactic
axiom family, not a semantic premise. -/
theorem literal_complemented_specification_without_predicate_projection :
    (∀ formula, Generated.ComplementedAxiom formula →
      Axioms.Valid (copyExpansion (definableModel (withSyntax (fun _ _ _ => 0)))) formula) ∧
    ¬ PredicateProjection (definableModel (withSyntax (fun _ _ _ => 0))) :=
  ⟨definable_model_satisfies_literal_complemented_axioms (withSyntax (fun _ _ _ => 0)),
   definable_model_fails_predicate_projection (fun _ _ _ => 0)⟩

end FregeanECA.Part2.Oracle
