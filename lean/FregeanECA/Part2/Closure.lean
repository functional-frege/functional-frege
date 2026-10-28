import FregeanECA.Syntax
import FregeanECA.Comprehension

/-! Part II: semantic classical comprehension in the original object-only
relation sorts. Predicate projection is an explicit impredicative schema;
separately represented sections are never silently collected into a family.
This file does not encode the new schemas as object-language theory axioms. -/

namespace FregeanECA.Part2
open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

/-- Full classical comprehension, including primitive relation identity and
arbitrarily nested object and predicate quantifiers. Index n denotes arity n+1. -/
structure HasFullComprehension (model : Interpretation D R) : Prop where
  relations_nonempty : ∀ arity, Nonempty (R arity)
  comprehend : ∀ (arity : Nat) (formula : Applicative.Formula)
    (parameters : ObjectAssignment D) (predicates : PredicateAssignment R),
    ∃ relation : R arity, ∀ arguments,
      model.satisfies arity relation arguments ↔
        formula.truth model (assignTuple (arity + 1) arguments parameters) predicates

/-- Complementation is relative to all object tuples of the given arity. -/
structure ComplementClosure (model : Interpretation D R) : Prop where
  complement : ∀ arity (relation : R arity), ∃ result : R arity, ∀ arguments,
    model.satisfies arity result arguments ↔ ¬ model.satisfies arity relation arguments

/-- The precise missing projection over an available predicate domain. The
antecedent gives each section separately; no family object or choice function
is a premise. The matrix may itself contain predicate quantifiers. -/
structure PredicateProjection (model : Interpretation D R) : Prop where
  project : ∀ (arity source : Nat) (formula : Applicative.Formula)
    (parameters : ObjectAssignment D) (predicates : PredicateAssignment R),
    (∀ predicate : R source, ∃ slice : R arity, ∀ arguments,
      model.satisfies arity slice arguments ↔
        formula.truth model (assignTuple (arity + 1) arguments parameters)
          (pushPredicate predicates source predicate)) →
    ∃ result : R arity, ∀ arguments,
      model.satisfies arity result arguments ↔
        ∃ predicate : R source,
          formula.truth model (assignTuple (arity + 1) arguments parameters)
            (pushPredicate predicates source predicate)

/-- Exactly B1--B5, Boolean complementation, and predicate projection. -/
structure ClassicalClosure (model : Interpretation D R) : Prop where
  positive : PositiveClosure model
  complemented : ComplementClosure model
  predicateProjection : PredicateProjection model

/-- Constant propositions, including equality of duplicate-capable predicate
representatives, require only top, complement, and a classical case split. -/
theorem ClassicalClosure.represents_constant {model : Interpretation D R}
    (closure : ClassicalClosure model) (arity : Nat) (p : Prop) :
    ∃ result : R arity, ∀ arguments, model.satisfies arity result arguments ↔ p := by
  classical
  obtain ⟨top, topLaw⟩ :=
    equality_and_preimages_supply_top model closure.positive.toEqualityAndPreimages arity
  by_cases holds : p
  · exact ⟨top, fun arguments => ⟨fun _ => holds, fun _ => topLaw arguments⟩⟩
  · obtain ⟨bottom, bottomLaw⟩ := closure.complemented.complement arity top
    exact ⟨bottom, fun arguments =>
      ⟨fun h => False.elim ((bottomLaw arguments).mp h (topLaw arguments)),
       fun h => False.elim (holds h)⟩⟩

/-- Structural induction on the complete existing classical syntax. In the
predicate cases the projection premise is discharged section by section. -/
theorem classical_closure_implies_full_comprehension (model : Interpretation D R)
    (laws : CombinatoryLaws model) (closure : ClassicalClosure model) :
    HasFullComprehension model := by
  classical
  refine ⟨?_, ?_⟩
  · intro arity
    obtain ⟨top, _⟩ :=
      equality_and_preimages_supply_top model closure.positive.toEqualityAndPreimages arity
    exact ⟨top⟩
  · intro arity formula
    induction formula generalizing arity with
    | equal left right =>
        intro parameters predicates
        obtain ⟨equality, equalityLaw⟩ := closure.positive.equality
        let terms : Fin 2 → Term := Fin.cases left (fun _ => right)
        obtain ⟨result, resultLaw⟩ := closure_under_term_preimages model laws
          closure.positive 1 arity equality terms parameters
        exact ⟨result, fun arguments => (resultLaw arguments).trans (equalityLaw _)⟩
    | relation source index terms =>
        intro parameters predicates
        exact closure_under_term_preimages model laws closure.positive source arity
          (predicates source index) terms parameters
    | relationEqual source left right =>
        intro parameters predicates
        exact closure.represents_constant arity (predicates source left = predicates source right)
    | falsum =>
        intro parameters predicates
        exact closure.represents_constant arity False
    | implies left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨notA, notALaw⟩ := closure.complemented.complement arity a
        obtain ⟨result, resultLaw⟩ := closure.positive.union arity notA b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, notALaw, aLaw, bLaw, Applicative.Formula.truth]
        by_cases h : left.truth model (assignTuple (arity + 1) arguments parameters) predicates
        · simp [h]
        · simp [h]
    | conjunction left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨result, resultLaw⟩ := closure.positive.intersection arity a b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, aLaw, bLaw, Applicative.Formula.truth]
    | disjunction left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨result, resultLaw⟩ := closure.positive.union arity a b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, aLaw, bLaw, Applicative.Formula.truth]
    | existsObject body bodyIH =>
        intro parameters predicates
        obtain ⟨bodyRelation, bodyLaw⟩ := bodyIH (arity + 1) parameters predicates
        obtain ⟨result, resultLaw⟩ :=
          closure_projects_first_exists model laws closure.positive arity bodyRelation
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, bodyLaw, assignTuple_cons, Applicative.Formula.truth]
    | forallObject body bodyIH =>
        intro parameters predicates
        obtain ⟨bodyRelation, bodyLaw⟩ := bodyIH (arity + 1) parameters predicates
        obtain ⟨result, resultLaw⟩ :=
          closure_projects_first_forall model laws closure.positive arity bodyRelation
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, bodyLaw, assignTuple_cons, Applicative.Formula.truth]
    | existsPredicate source body bodyIH =>
        intro parameters predicates
        exact closure.predicateProjection.project arity source body parameters predicates
          (fun predicate => bodyIH arity parameters (pushPredicate predicates source predicate))
    | forallPredicate source body bodyIH =>
        intro parameters predicates
        have sections : ∀ predicate : R source, ∃ slice : R arity, ∀ arguments,
            model.satisfies arity slice arguments ↔
              (Applicative.Formula.implies body .falsum).truth model
                (assignTuple (arity + 1) arguments parameters)
                (pushPredicate predicates source predicate) := by
          intro predicate
          obtain ⟨slice, sectionLaw⟩ :=
            bodyIH arity parameters (pushPredicate predicates source predicate)
          obtain ⟨negated, negatedLaw⟩ := closure.complemented.complement arity slice
          exact ⟨negated, fun arguments => (negatedLaw arguments).trans
            (not_congr (sectionLaw arguments))⟩
        obtain ⟨counterexamples, counterexamplesLaw⟩ := closure.predicateProjection.project
          arity source (.implies body .falsum) parameters predicates sections
        obtain ⟨result, resultLaw⟩ := closure.complemented.complement arity counterexamples
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, counterexamplesLaw, Applicative.Formula.truth]
        constructor
        · intro none predicate
          apply Classical.byContradiction
          intro failure
          exact none ⟨predicate, failure⟩
        · rintro all ⟨predicate, failure⟩
          exact failure (all predicate)

/-- The strict positive syntax embeds into the classical syntax without any
translation of object terms, predicate representatives, or variable stacks. -/
def positiveFormula : Positive.Formula → Applicative.Formula
  | .equal left right => .equal left right
  | .relation arity index arguments => .relation arity index arguments
  | .conjunction left right => .conjunction (positiveFormula left) (positiveFormula right)
  | .disjunction left right => .disjunction (positiveFormula left) (positiveFormula right)
  | .existsObject body => .existsObject (positiveFormula body)
  | .forallObject body => .forallObject (positiveFormula body)
  | .existsPredicate arity body => .existsPredicate arity (positiveFormula body)
  | .forallPredicate arity body => .forallPredicate arity (positiveFormula body)

theorem positiveFormula_truth (model : Interpretation D R) (formula : Positive.Formula)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R) :
    (positiveFormula formula).truth model objects predicates ↔
      formula.truth model objects predicates := by
  induction formula generalizing objects predicates <;>
    simp_all only [positiveFormula, Applicative.Formula.truth, Positive.Formula.truth]

theorem full_comprehension_implies_positive_comprehension (model : Interpretation D R)
    (full : HasFullComprehension model) : HasPositiveComprehension model where
  relations_nonempty := full.relations_nonempty
  comprehend := by
    intro arity formula parameters predicates
    obtain ⟨relation, relationLaw⟩ := full.comprehend arity
      (positiveFormula formula) parameters predicates
    exact ⟨relation, fun arguments =>
      (relationLaw arguments).trans (positiveFormula_truth model formula _ predicates)⟩

theorem full_comprehension_implies_complement (model : Interpretation D R)
    (full : HasFullComprehension model) : ComplementClosure model := by
  classical
  refine ⟨?_⟩
  intro arity relation
  let initial : PredicateAssignment R := fun source _ => Classical.choice (full.relations_nonempty source)
  let predicates := pushPredicate initial arity relation
  obtain ⟨result, resultLaw⟩ := full.comprehend arity
    (.implies (.relation arity 0 (fun i => .var i.val)) .falsum)
    (fun _ => model.constantK) predicates
  refine ⟨result, ?_⟩
  intro arguments
  simpa only [Applicative.Formula.truth, Term.value, assignTuple_at,
    predicates, pushPredicate, dite_true] using resultLaw arguments

theorem full_comprehension_implies_predicate_projection (model : Interpretation D R)
    (full : HasFullComprehension model) : PredicateProjection model where
  project := by
    intro arity source formula parameters predicates _sections
    exact full.comprehend arity (.existsPredicate source formula) parameters predicates

/-- Necessity uses actual comprehension instances; predicate projection does
not need to choose or encode the witnesses in its antecedent. -/
theorem full_comprehension_implies_classical_closure (model : Interpretation D R)
    (full : HasFullComprehension model) : ClassicalClosure model where
  positive := positive_comprehension_implies_closure model
    (full_comprehension_implies_positive_comprehension model full)
  complemented := full_comprehension_implies_complement model full
  predicateProjection := full_comprehension_implies_predicate_projection model full

/-- Semantic equivalence over K/S algebras. Extensionality, nontriviality, and
extensional identity of relation representatives are not additional premises. -/
theorem classical_closure_iff_full_comprehension (model : Interpretation D R)
    (laws : CombinatoryLaws model) :
    ClassicalClosure model ↔ HasFullComprehension model :=
  ⟨classical_closure_implies_full_comprehension model laws,
    full_comprehension_implies_classical_closure model⟩

end FregeanECA.Part2
