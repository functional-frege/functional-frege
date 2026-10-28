import FregeanECA.Comprehension

/-!
# Positive relational algebra independent of combinatory laws

Version 2 replaces preimages under represented programs by preimages under
finite applicative terms, with object parameters. The resulting algebra is
equivalent to the entire strict-positive comprehension scheme on arbitrary
applicative interpretations. No K/S laws or nontriviality assumption is used.
-/

namespace FregeanECA.V2

open FregeanECA.Positive

universe u v
variable {D : Type u} {R : Nat → Type v}

/-- Equality, Boolean positive operations, term substitution, and object projection.
The relation sort `R n` has positive arity `n + 1`. -/
structure PCAlgebra (model : Interpretation D R) : Prop where
  equality : ∃ relation : R 1, ∀ arguments,
    model.satisfies 1 relation arguments ↔ arguments 0 = arguments 1
  termPreimage : ∀ (source target : Nat) (relation : R source)
    (terms : Fin (source + 1) → Term) (parameters : ObjectAssignment D),
    ∃ result : R target, ∀ arguments,
      model.satisfies target result arguments ↔
        model.satisfies source relation
          (fun i => (terms i).value model (assignTuple (target + 1) arguments parameters))
  intersection : ∀ arity (left right : R arity), ∃ result : R arity, ∀ arguments,
    model.satisfies arity result arguments ↔
      model.satisfies arity left arguments ∧ model.satisfies arity right arguments
  union : ∀ arity (left right : R arity), ∃ result : R arity, ∀ arguments,
    model.satisfies arity result arguments ↔
      model.satisfies arity left arguments ∨ model.satisfies arity right arguments
  existsProjection : ∀ arity (relation : R (arity + 1)), ∃ result : R arity, ∀ arguments,
    model.satisfies arity result arguments ↔
      ∃ value, model.satisfies (arity + 1) relation (appendLast arguments value)
  forallProjection : ∀ arity (relation : R (arity + 1)), ∃ result : R arity, ∀ arguments,
    model.satisfies arity result arguments ↔
      ∀ value, model.satisfies (arity + 1) relation (appendLast arguments value)

/-- The new substitution clause includes every old program-preimage instance,
without requiring those programs to obey combinatory equations. -/
theorem pcAlgebra_implies_positiveClosure (model : Interpretation D R)
    (algebra : PCAlgebra model) : PositiveClosure model := by
  refine {
    toEqualityAndPreimages := { equality := algebra.equality, preimage := ?_ }
    intersection := algebra.intersection
    union := algebra.union
    existsProjection := algebra.existsProjection
    forallProjection := algebra.forallProjection
  }
  intro source target relation programs
  let coefficients := assignTuple (source + 1) programs (fun _ => model.constantK)
  obtain ⟨result, resultLaw⟩ := algebra.termPreimage source target relation
    (fun i => programTerm (target + 1) i.val) coefficients
  refine ⟨result, ?_⟩
  intro arguments
  simpa only [value_programTerm, coefficients, assignTuple_at] using resultLaw arguments

theorem pcAlgebra_supply_top (model : Interpretation D R)
    (algebra : PCAlgebra model) (arity : Nat) :
    ∃ top : R arity, IsTop model arity top :=
  equality_and_preimages_supply_top model
    (pcAlgebra_implies_positiveClosure model algebra).toEqualityAndPreimages arity

/-- A least available relation need not be empty: in a singleton interpretation
the only available extension may be the full relation. -/
def IsLeast (model : Interpretation D R) (arity : Nat) (least : R arity) : Prop :=
  ∀ relation : R arity, ∀ arguments,
    model.satisfies arity least arguments → model.satisfies arity relation arguments

/-- If some available relation has a false tuple, parameter substitution gives
an empty relation. Otherwise every available relation is full and hence least. -/
theorem pcAlgebra_supply_least (model : Interpretation D R)
    (algebra : PCAlgebra model) (arity : Nat) :
    ∃ least : R arity, IsLeast model arity least := by
  classical
  by_cases allFull : ∀ relation : R arity, IsTop model arity relation
  · obtain ⟨top, _⟩ := pcAlgebra_supply_top model algebra arity
    exact ⟨top, fun relation arguments _ => allFull relation arguments⟩
  · obtain ⟨relation, notFull⟩ := Classical.not_forall.mp allFull
    obtain ⟨arguments, falseTuple⟩ := Classical.not_forall.mp notFull
    let coefficients := assignTuple (arity + 1) arguments (fun _ => model.constantK)
    obtain ⟨least, leastLaw⟩ := algebra.termPreimage arity arity relation
      (fun i => .var ((arity + 1) + i.val)) coefficients
    have empty : IsBottom model arity least := by
      intro tuple holds
      have atFalseTuple := (leastLaw tuple).mp holds
      have same : (fun i : Fin (arity + 1) =>
          (Term.var ((arity + 1) + i.val)).value model
            (assignTuple (arity + 1) tuple coefficients)) = arguments := by
        funext i
        simp only [Term.value, assignTuple_after, coefficients, assignTuple_at]
      rw [same] at atFalseTuple
      exact falseTuple atFalseTuple
    exact ⟨least, fun _ tuple holds => False.elim (empty tuple holds)⟩

/-- Monotonicity needs a least available extension, not necessarily an empty one. -/
theorem forall_predicate_iff_least (model : Interpretation D R)
    (body : Formula) (objects : ObjectAssignment D) (predicates : PredicateAssignment R)
    (arity : Nat) (least : R arity) (minimal : IsLeast model arity least) :
    (Formula.forallPredicate arity body).truth model objects predicates ↔
      body.truth model objects (pushPredicate predicates arity least) := by
  constructor
  · intro holds
    exact holds least
  · intro holds relation
    apply positive_truth_is_monotone model body objects _ _ _ holds
    exact push_predicate_preserves_inclusion model predicates predicates
      (assignment_le_refl model predicates) arity least relation (minimal relation)

theorem pcAlgebra_moves_last_to_front (model : Interpretation D R)
    (algebra : PCAlgebra model) (arity : Nat) (relation : R (arity + 1)) :
    ∃ result : R (arity + 1), ∀ arguments,
      model.satisfies (arity + 1) result arguments ↔
        model.satisfies (arity + 1) relation
          (Fin.cases (arguments (Fin.last (arity + 1))) (fun i => arguments i.castSucc)) := by
  let position : Fin (arity + 2) → Fin (arity + 2) :=
    Fin.cases (Fin.last (arity + 1)) (fun i => i.castSucc)
  obtain ⟨result, resultLaw⟩ := algebra.termPreimage
    (arity + 1) (arity + 1) relation (fun i => .var (position i).val) (fun _ => model.constantK)
  refine ⟨result, ?_⟩
  intro arguments
  rw [resultLaw]
  have same : (fun i => Term.value model
      (assignTuple (arity + 2) arguments (fun _ => model.constantK)) (.var (position i).val)) =
      Fin.cases (arguments (Fin.last (arity + 1))) (fun i => arguments i.castSucc) := by
    funext i
    simp only [Term.value, assignTuple_at]
    exact Fin.cases rfl (fun _ => rfl) i
  rw [same]

theorem pcAlgebra_projects_first_exists (model : Interpretation D R)
    (algebra : PCAlgebra model) (arity : Nat) (relation : R (arity + 1)) :
    ∃ result : R arity, ∀ arguments,
      model.satisfies arity result arguments ↔
        ∃ value, model.satisfies (arity + 1) relation (Fin.cases value arguments) := by
  obtain ⟨reordered, reorderedLaw⟩ := pcAlgebra_moves_last_to_front model algebra arity relation
  obtain ⟨result, resultLaw⟩ := algebra.existsProjection arity reordered
  refine ⟨result, ?_⟩
  intro arguments
  simp only [resultLaw, reorderedLaw, appendLast_last, appendLast_castSucc]

theorem pcAlgebra_projects_first_forall (model : Interpretation D R)
    (algebra : PCAlgebra model) (arity : Nat) (relation : R (arity + 1)) :
    ∃ result : R arity, ∀ arguments,
      model.satisfies arity result arguments ↔
        ∀ value, model.satisfies (arity + 1) relation (Fin.cases value arguments) := by
  obtain ⟨reordered, reorderedLaw⟩ := pcAlgebra_moves_last_to_front model algebra arity relation
  obtain ⟨result, resultLaw⟩ := algebra.forallProjection arity reordered
  refine ⟨result, ?_⟩
  intro arguments
  simp only [resultLaw, reorderedLaw, appendLast_last, appendLast_castSucc]

/-- All strict-positive formulas, including nested quantification over relations,
have available extensions. The argument needs neither K/S nor nontriviality. -/
theorem pcAlgebra_implies_positiveComprehension (model : Interpretation D R)
    (algebra : PCAlgebra model) : HasPositiveComprehension model := by
  refine ⟨?_, ?_⟩
  · intro arity
    obtain ⟨top, _⟩ := pcAlgebra_supply_top model algebra arity
    exact ⟨top⟩
  · intro arity formula
    induction formula generalizing arity with
    | equal left right =>
        intro parameters predicates
        obtain ⟨equality, equalityLaw⟩ := algebra.equality
        let terms : Fin 2 → Term := Fin.cases left (fun _ => right)
        obtain ⟨result, resultLaw⟩ := algebra.termPreimage 1 arity equality terms parameters
        refine ⟨result, ?_⟩
        intro arguments
        exact (resultLaw arguments).trans (equalityLaw _)
    | relation source index terms =>
        intro parameters predicates
        exact algebra.termPreimage source arity (predicates source index) terms parameters
    | conjunction left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨result, resultLaw⟩ := algebra.intersection arity a b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, aLaw, bLaw, Formula.truth]
    | disjunction left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨result, resultLaw⟩ := algebra.union arity a b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, aLaw, bLaw, Formula.truth]
    | existsObject body bodyIH =>
        intro parameters predicates
        obtain ⟨bodyRelation, bodyLaw⟩ := bodyIH (arity + 1) parameters predicates
        obtain ⟨result, resultLaw⟩ := pcAlgebra_projects_first_exists model algebra arity bodyRelation
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, bodyLaw, assignTuple_cons, Formula.truth]
    | forallObject body bodyIH =>
        intro parameters predicates
        obtain ⟨bodyRelation, bodyLaw⟩ := bodyIH (arity + 1) parameters predicates
        obtain ⟨result, resultLaw⟩ := pcAlgebra_projects_first_forall model algebra arity bodyRelation
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, bodyLaw, assignTuple_cons, Formula.truth]
    | existsPredicate source body bodyIH =>
        intro parameters predicates
        obtain ⟨top, universal⟩ := pcAlgebra_supply_top model algebra source
        obtain ⟨result, resultLaw⟩ := bodyIH arity parameters (pushPredicate predicates source top)
        refine ⟨result, ?_⟩
        intro arguments
        exact (resultLaw arguments).trans
          (exists_predicate_iff_top model body _ predicates source top universal).symm
    | forallPredicate source body bodyIH =>
        intro parameters predicates
        obtain ⟨least, minimal⟩ := pcAlgebra_supply_least model algebra source
        obtain ⟨result, resultLaw⟩ := bodyIH arity parameters (pushPredicate predicates source least)
        refine ⟨result, ?_⟩
        intro arguments
        exact (resultLaw arguments).trans
          (forall_predicate_iff_least model body _ predicates source least minimal).symm

/-- Every new algebra instance is directly a positive-comprehension instance. -/
theorem positiveComprehension_implies_pcAlgebra (model : Interpretation D R)
    (comprehension : HasPositiveComprehension model) : PCAlgebra model := by
  classical
  have old := positive_comprehension_implies_closure model comprehension
  refine {
    equality := old.equality
    termPreimage := ?_
    intersection := old.intersection
    union := old.union
    existsProjection := old.existsProjection
    forallProjection := old.forallProjection
  }
  intro source target relation terms parameters
  let initial : PredicateAssignment R := fun arity _ =>
    Classical.choice (comprehension.relations_nonempty arity)
  let predicates := pushPredicate initial source relation
  obtain ⟨result, resultLaw⟩ := comprehension.comprehend target
    (.relation source 0 terms) parameters predicates
  refine ⟨result, ?_⟩
  intro arguments
  simpa only [Formula.truth, predicates, pushPredicate, dite_true] using resultLaw arguments

/-- Standalone equivalence: no computational equations or nontriviality premise. -/
theorem pcAlgebra_iff_positiveComprehension (model : Interpretation D R) :
    PCAlgebra model ↔ HasPositiveComprehension model :=
  ⟨pcAlgebra_implies_positiveComprehension model,
    positiveComprehension_implies_pcAlgebra model⟩

/-- Term representability proves the compatibility bridge to the old algebra.
The bridge itself does not need extensionality or nontriviality. -/
theorem positiveClosure_implies_pcAlgebra (model : Interpretation D R)
    (laws : CombinatoryLaws model) (closure : PositiveClosure model) : PCAlgebra model where
  equality := closure.equality
  termPreimage := closure_under_term_preimages model laws closure
  intersection := closure.intersection
  union := closure.union
  existsProjection := closure.existsProjection
  forallProjection := closure.forallProjection

theorem pcAlgebra_iff_positiveClosure (model : Interpretation D R)
    (laws : CombinatoryLaws model) : PCAlgebra model ↔ PositiveClosure model :=
  ⟨pcAlgebra_implies_positiveClosure model, positiveClosure_implies_pcAlgebra model laws⟩

end FregeanECA.V2
