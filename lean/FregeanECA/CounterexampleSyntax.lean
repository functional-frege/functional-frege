import FregeanECA.AxiomsSpecification
import FregeanECA.Counterexample

namespace FregeanECA.Axioms
open Functional

/-- Exactly B1--B5, omitting every ECA axiom. -/
inductive ClosureAxiom : Formula → Prop where
  | equality : ClosureAxiom equalityRelation
  | intersection (n : Nat) : ClosureAxiom (intersection n)
  | union (n : Nat) : ClosureAxiom (union n)
  | preimage (m n : Nat) : ClosureAxiom (preimage m n)
  | existsProjection (n : Nat) : ClosureAxiom (existsProjection n)
  | forallProjection (n : Nat) : ClosureAxiom (forallProjection n)

theorem closure_axiom_is_specification_axiom {p : Formula} (h : ClosureAxiom p) :
    SpecificationAxiom p := by
  cases h with
  | equality => exact .equality
  | intersection n => exact .intersection n
  | union n => exact .union n
  | preimage m n => exact .preimage m n
  | existsProjection n => exact .existsProjection n
  | forallProjection n => exact .forallProjection n

theorem closure_axioms_of_closure {D : Type u} {F : Type v} {R : Nat → Type w}
    (M : Interpretation D F R) (h : Positive.PositiveClosure M.applicative) :
    ∀ p, ClosureAxiom p → Valid M p := by
  intro p hp o f r
  cases hp with
  | equality => exact (equalityRelation_truth M o f r).mpr h.equality
  | intersection n =>
      exact (intersection_truth M n o f r).mpr (h.intersection n (r n 0) (r n 1))
  | union n => exact (union_truth M n o f r).mpr (h.union n (r n 0) (r n 1))
  | preimage source target =>
      exact (preimage_truth M source target o f r).mpr
        (h.preimage source target (r source 0) (fun i => o i))
  | existsProjection n =>
      exact (existsProjection_truth M n o f r).mpr (h.existsProjection n (r (n+1) 0))
  | forallProjection n =>
      exact (forallProjection_truth M n o f r).mpr (h.forallProjection n (r (n+1) 0))

end FregeanECA.Axioms

namespace FregeanECA.CounterexampleSyntax
open Axioms

abbrev Relations (arity : Nat) := Counterexample.Relation (arity + 1)

/-- The invariant Bool structure with explicit interpretations of the unused
function sort and K/S symbols. No combinator equations are asserted. -/
def invariantModel : Functional.Interpretation Bool Bool Relations where
  applicative := {
    apply := Counterexample.application
    constantK := false
    constantS := false
    satisfies := fun _ P xs => P.holds xs }
  eval := Counterexample.application
  delta := id

theorem relation_sorts_nonempty (arity : Nat) : Nonempty (Relations arity) :=
  Counterexample.each_relation_sort_is_nonempty arity

theorem append_agrees {n : Nat} (arguments : Fin n → Bool) (value : Bool) :
    Counterexample.append arguments value = Positive.appendLast arguments value := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Counterexample.append]
  · simp [Counterexample.append, j.isLt]

theorem application_returns_last (arity : Nat) (program : Bool) (arguments : Fin (arity + 1) → Bool) :
    Positive.applyArguments invariantModel.applicative program arguments =
      arguments (Fin.last arity) :=
  Positive.applyArguments_append invariantModel.applicative arity program arguments

/-- The earlier invariant-relation construction satisfies the exact current
closure structure, including the actual finite-program B3 convention. -/
theorem invariantModel_positive_closure : Positive.PositiveClosure invariantModel.applicative where
  equality := ⟨Counterexample.diagonal, fun _ => Iff.rfl⟩
  preimage := by
    intro source target relation programs
    refine ⟨Counterexample.substitute relation programs, ?_⟩
    intro arguments
    change relation.holds (fun i => Counterexample.applyTuple (target + 1) (programs i) arguments) ↔ _
    simp only [Counterexample.a_positive_application_returns_the_last_argument,
      application_returns_last]
    rfl
  intersection := fun _ left right => ⟨Counterexample.intersection left right, fun _ => Iff.rfl⟩
  union := fun _ left right => ⟨Counterexample.union left right, fun _ => Iff.rfl⟩
  existsProjection := by
    intro arity relation
    refine ⟨Counterexample.existsProject relation, ?_⟩
    intro arguments
    change (∃ value, relation.holds (Counterexample.append arguments value)) ↔ _
    simp only [append_agrees]
    rfl
  forallProjection := by
    intro arity relation
    refine ⟨Counterexample.forallProject relation, ?_⟩
    intro arguments
    change (∀ value, relation.holds (Counterexample.append arguments value)) ↔ _
    simp only [append_agrees]
    rfl

theorem every_actual_closure_axiom_is_valid :
    ∀ p, ClosureAxiom p → Valid invariantModel p :=
  closure_axioms_of_closure invariantModel invariantModel_positive_closure

theorem actual_nontriviality_is_valid : Valid invariantModel nontriviality := by
  intro objects functions predicates
  exact (nontriviality_truth invariantModel objects functions predicates).mpr
    Counterexample.the_object_domain_is_nontrivial

/-- The literal A1 instance with body x = a; a is the first parameter. -/
def singletonComprehension : Functional.Formula :=
  relationalComprehension 0 (.equal (.var 0) (.var 1))

theorem singletonComprehension_is_a_functional_axiom :
    FunctionalAxiom singletonComprehension := .relational 0 (.equal (.var 0) (.var 1))

theorem actual_singleton_comprehension_fails_at_false
    (functions : Nat → Bool) (predicates : Positive.PredicateAssignment Relations) :
    ¬ singletonComprehension.truth invariantModel (fun _ => false) functions predicates := by
  intro truth
  obtain ⟨P, defines⟩ := (relationalComprehension_truth invariantModel
    0 (.equal (.var 0) (.var 1)) (fun _ => false) functions predicates).mp truth
  apply Counterexample.no_relation_defines_parameter_equality_at_false
  refine ⟨P, ?_⟩
  intro x
  exact defines (fun _ => x)

theorem actual_singleton_comprehension_is_not_valid :
    ¬ Valid invariantModel singletonComprehension := by
  intro valid
  exact actual_singleton_comprehension_fails_at_false (fun _ => false)
    (fun arity _ => Counterexample.universalRelation (arity + 1)) (valid _ _ _)

/-- Actual B1--B5 and nontriviality hold, while an actual positive-comprehension
formula fails. Foundation soundness can now give syntactic nonderivability. -/
theorem actual_closure_axioms_have_a_positive_comprehension_countermodel :
    (∀ p, ClosureAxiom p → Valid invariantModel p) ∧
      Valid invariantModel nontriviality ∧
      ¬ Valid invariantModel singletonComprehension :=
  ⟨every_actual_closure_axiom_is_valid, actual_nontriviality_is_valid,
    actual_singleton_comprehension_is_not_valid⟩

end FregeanECA.CounterexampleSyntax

