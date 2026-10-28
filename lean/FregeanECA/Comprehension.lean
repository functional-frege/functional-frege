import FregeanECA.Positive
import FregeanECA.Model

namespace FregeanECA.Positive

open Frege
universe u v
variable {D : Type u} {R : Nat → Type v}

/-- Vary a finite initial segment and retain all remaining object parameters. -/
def assignTuple : (length : Nat) → (Fin length → D) → ObjectAssignment D → ObjectAssignment D
  | 0, _, parameters => parameters
  | length + 1, arguments, parameters =>
      pushObject (assignTuple length (fun i => arguments i.succ) parameters) (arguments 0)

@[simp] theorem assignTuple_at (length : Nat) (arguments : Fin length → D)
    (parameters : ObjectAssignment D) (index : Fin length) :
    assignTuple length arguments parameters index = arguments index := by
  induction length with
  | zero => exact Fin.elim0 index
  | succ length ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · rfl
      · exact ih _ index

@[simp] theorem assignTuple_after (length : Nat) (arguments : Fin length → D)
    (parameters : ObjectAssignment D) (index : Nat) :
    assignTuple length arguments parameters (length + index) = parameters index := by
  induction length with
  | zero => simp [assignTuple]
  | succ length ih =>
      simpa [assignTuple, pushObject, Nat.succ_add] using ih (fun i => arguments i.succ)

@[simp] theorem assignTuple_cons (length : Nat) (arguments : Fin length → D)
    (parameters : ObjectAssignment D) (value : D) :
    assignTuple (length + 1) (Fin.cases value arguments) parameters =
      pushObject (assignTuple length arguments parameters) value := rfl

/-- Nonempty relation sorts are part of the paper's many-sorted semantics. -/
structure HasPositiveComprehension (model : Interpretation D R) : Prop where
  relations_nonempty : ∀ arity, Nonempty (R arity)
  comprehend : ∀ (arity : Nat) (formula : Formula) (parameters : ObjectAssignment D)
    (predicates : PredicateAssignment R),
    ∃ relation : R arity, ∀ arguments,
      model.satisfies arity relation arguments ↔
        formula.truth model (assignTuple (arity + 1) arguments parameters) predicates

/-- Append the projected variable in the last coordinate, as in B4 and B5. -/
def appendLast {length : Nat} (arguments : Fin length → D) (value : D) :
    Fin (length + 1) → D := Fin.lastCases value arguments

@[simp] theorem appendLast_last {length : Nat} (arguments : Fin length → D) (value : D) :
    appendLast arguments value (Fin.last length) = value := by simp [appendLast]

@[simp] theorem appendLast_castSucc {length : Nat} (arguments : Fin length → D)
    (value : D) (i : Fin length) :
    appendLast arguments value i.castSucc = arguments i := by simp [appendLast]

/-- Exactly B1--B5; preimages use actual program objects, never arbitrary maps. -/
structure PositiveClosure (model : Interpretation D R) : Prop extends EqualityAndPreimages model where
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

/-- The K/S laws for the exact interpretation operation and constants. -/
structure CombinatoryLaws (model : Interpretation D R) : Prop where
  constant : ∀ x y, model.apply (model.apply model.constantK x) y = x
  distribute : ∀ x y z,
    model.apply (model.apply (model.apply model.constantS x) y) z =
      model.apply (model.apply x z) (model.apply y z)

def CombinatoryLaws.algebra {model : Interpretation D R} (laws : CombinatoryLaws model) :
    CombinatoryAlgebra D where
  apply := model.apply
  constant := model.constantK
  distribute := model.constantS
  constant_returns_first_argument := laws.constant
  distribute_applies_the_same_argument := laws.distribute

theorem applyArguments_append (model : Interpretation D R) (length : Nat)
    (code : D) (arguments : Fin (length + 1) → D) :
    applyArguments model code arguments =
      model.apply (applyArguments model code (fun i : Fin length => arguments i.castSucc))
        (arguments (Fin.last length)) := by
  induction length generalizing code with
  | zero => rfl
  | succ length ih =>
      exact ih (model.apply code (arguments 0)) (fun i => arguments i.succ)

/-- Explicit bridge from the reused reverse-de-Bruijn application convention. -/
theorem reversed_application_agrees (model : Interpretation D R) (laws : CombinatoryLaws model)
    (length : Nat) (code : D) (arguments : Fin length → D) :
    FregeanECA.applyArguments laws.algebra code (fun i => arguments i.rev) =
      applyArguments model code arguments := by
  induction length with
  | zero => rfl
  | succ length ih =>
      rw [FregeanECA.applyArguments]
      simp only [Fin.rev_succ, Fin.rev_zero]
      rw [ih (fun i => arguments i.castSucc)]
      exact (applyArguments_append model length code arguments).symm

def Term.asCombinator (model : Interpretation D R) (length : Nat)
    (parameters : ObjectAssignment D) : Term → CombinatorTerm D length
  | .var index =>
      if within : index < length then .variable (Fin.rev ⟨index, within⟩)
      else .coefficient (parameters (index - length))
  | .constantK => .constant
  | .constantS => .distribute
  | .app left right => .application (left.asCombinator model length parameters)
      (right.asCombinator model length parameters)

theorem term_asCombinator_correct (model : Interpretation D R) (laws : CombinatoryLaws model)
    (length : Nat) (parameters : ObjectAssignment D) (term : Term) (arguments : Fin length → D) :
    CombinatorTerm.evaluate laws.algebra id (term.asCombinator model length parameters)
      (fun i => arguments i.rev) =
      term.value model (assignTuple length arguments parameters) := by
  induction term with
  | var index =>
      by_cases within : index < length
      · simp only [Term.asCombinator, dif_pos within, CombinatorTerm.evaluate, Term.value, Fin.rev_rev]
        exact (assignTuple_at length arguments parameters ⟨index, within⟩).symm
      · have index_eq : index = length + (index - length) := by omega
        simp only [Term.asCombinator, dif_neg within, CombinatorTerm.evaluate, id_eq, Term.value]
        exact (assignTuple_after length arguments parameters (index - length)).symm.trans
          (congrArg (assignTuple length arguments parameters) index_eq.symm)
  | constantK => rfl
  | constantS => rfl
  | app left right leftIH rightIH =>
      change model.apply _ _ = model.apply _ _
      rw [leftIH, rightIH]

/-- Every finite applicative term has a code, derived from the actual K/S laws. -/
theorem terms_have_codes (model : Interpretation D R) (laws : CombinatoryLaws model)
    (length : Nat) (parameters : ObjectAssignment D) (term : Term) :
    ∃ code : D, ∀ arguments : Fin length → D,
      applyArguments model code arguments =
        term.value model (assignTuple length arguments parameters) := by
  refine ⟨FregeanECA.closeTerm laws.algebra (term.asCombinator model length parameters), ?_⟩
  intro arguments
  rw [← reversed_application_agrees model laws length]
  exact (FregeanECA.closeTerm_spec laws.algebra _ _).trans
    (term_asCombinator_correct model laws length parameters term arguments)


/-- B3 combined with proved term representability, not an additional closure axiom. -/
theorem closure_under_term_preimages (model : Interpretation D R) (laws : CombinatoryLaws model)
    (closure : PositiveClosure model) (source target : Nat) (relation : R source)
    (terms : Fin (source + 1) → Term) (parameters : ObjectAssignment D) :
    ∃ result : R target, ∀ arguments,
      model.satisfies target result arguments ↔
        model.satisfies source relation
          (fun i => (terms i).value model (assignTuple (target + 1) arguments parameters)) := by
  classical
  let programs : Fin (source + 1) → D := fun i =>
    Classical.choose (terms_have_codes model laws (target + 1) parameters (terms i))
  have programLaw (i : Fin (source + 1)) (arguments : Fin (target + 1) → D) :
      applyArguments model (programs i) arguments =
        (terms i).value model (assignTuple (target + 1) arguments parameters) :=
    Classical.choose_spec (terms_have_codes model laws (target + 1) parameters (terms i)) arguments
  obtain ⟨result, resultLaw⟩ := closure.preimage source target relation programs
  refine ⟨result, ?_⟩
  intro arguments
  rw [resultLaw]
  have same : (fun i => applyArguments model (programs i) arguments) =
      (fun i => (terms i).value model (assignTuple (target + 1) arguments parameters)) :=
    funext (fun i => programLaw i arguments)
  rw [same]

theorem closure_moves_last_to_front (model : Interpretation D R) (laws : CombinatoryLaws model)
    (closure : PositiveClosure model) (arity : Nat) (relation : R (arity + 1)) :
    ∃ result : R (arity + 1), ∀ arguments,
      model.satisfies (arity + 1) result arguments ↔
        model.satisfies (arity + 1) relation
          (Fin.cases (arguments (Fin.last (arity + 1))) (fun i => arguments i.castSucc)) := by
  let position : Fin (arity + 2) → Fin (arity + 2) :=
    Fin.cases (Fin.last (arity + 1)) (fun i => i.castSucc)
  obtain ⟨result, resultLaw⟩ := closure_under_term_preimages model laws closure
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

theorem closure_projects_first_exists (model : Interpretation D R) (laws : CombinatoryLaws model)
    (closure : PositiveClosure model) (arity : Nat) (relation : R (arity + 1)) :
    ∃ result : R arity, ∀ arguments,
      model.satisfies arity result arguments ↔
        ∃ value, model.satisfies (arity + 1) relation (Fin.cases value arguments) := by
  obtain ⟨reordered, reorderedLaw⟩ := closure_moves_last_to_front model laws closure arity relation
  obtain ⟨result, resultLaw⟩ := closure.existsProjection arity reordered
  refine ⟨result, ?_⟩
  intro arguments
  simp only [resultLaw, reorderedLaw, appendLast_last, appendLast_castSucc]

theorem closure_projects_first_forall (model : Interpretation D R) (laws : CombinatoryLaws model)
    (closure : PositiveClosure model) (arity : Nat) (relation : R (arity + 1)) :
    ∃ result : R arity, ∀ arguments,
      model.satisfies arity result arguments ↔
        ∀ value, model.satisfies (arity + 1) relation (Fin.cases value arguments) := by
  obtain ⟨reordered, reorderedLaw⟩ := closure_moves_last_to_front model laws closure arity relation
  obtain ⟨result, resultLaw⟩ := closure.forallProjection arity reordered
  refine ⟨result, ?_⟩
  intro arguments
  simp only [resultLaw, reorderedLaw, appendLast_last, appendLast_castSucc]

/-- Full structural comprehension, including parameters and nested predicate binders. -/
theorem positive_closure_implies_comprehension (model : Interpretation D R)
    (laws : CombinatoryLaws model) (nontrivial : ∃ a b : D, a ≠ b)
    (closure : PositiveClosure model) : HasPositiveComprehension model := by
  refine ⟨?_, ?_⟩
  · intro arity
    obtain ⟨top, _⟩ := equality_and_preimages_supply_top model closure.toEqualityAndPreimages arity
    exact ⟨top⟩
  · intro arity formula
    induction formula generalizing arity with
    | equal left right =>
        intro parameters predicates
        obtain ⟨equality, equalityLaw⟩ := closure.equality
        let terms : Fin 2 → Term := Fin.cases left (fun _ => right)
        obtain ⟨result, resultLaw⟩ :=
          closure_under_term_preimages model laws closure 1 arity equality terms parameters
        refine ⟨result, ?_⟩
        intro arguments
        exact (resultLaw arguments).trans (equalityLaw _)
    | relation source index terms =>
        intro parameters predicates
        exact closure_under_term_preimages model laws closure source arity
          (predicates source index) terms parameters
    | conjunction left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨result, resultLaw⟩ := closure.intersection arity a b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, aLaw, bLaw, Formula.truth]
    | disjunction left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨result, resultLaw⟩ := closure.union arity a b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, aLaw, bLaw, Formula.truth]
    | existsObject body bodyIH =>
        intro parameters predicates
        obtain ⟨bodyRelation, bodyLaw⟩ := bodyIH (arity + 1) parameters predicates
        obtain ⟨result, resultLaw⟩ := closure_projects_first_exists model laws closure arity bodyRelation
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, bodyLaw, assignTuple_cons, Formula.truth]
    | forallObject body bodyIH =>
        intro parameters predicates
        obtain ⟨bodyRelation, bodyLaw⟩ := bodyIH (arity + 1) parameters predicates
        obtain ⟨result, resultLaw⟩ := closure_projects_first_forall model laws closure arity bodyRelation
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, bodyLaw, assignTuple_cons, Formula.truth]
    | existsPredicate source body bodyIH =>
        intro parameters predicates
        obtain ⟨top, universal⟩ :=
          equality_and_preimages_supply_top model closure.toEqualityAndPreimages source
        obtain ⟨result, resultLaw⟩ := bodyIH arity parameters (pushPredicate predicates source top)
        refine ⟨result, ?_⟩
        intro arguments
        exact (resultLaw arguments).trans
          (exists_predicate_iff_top model body _ predicates source top universal).symm
    | forallPredicate source body bodyIH =>
        intro parameters predicates
        obtain ⟨bottom, empty⟩ := equality_and_preimages_supply_bottom model
          closure.toEqualityAndPreimages laws.constant nontrivial source
        obtain ⟨result, resultLaw⟩ := bodyIH arity parameters (pushPredicate predicates source bottom)
        refine ⟨result, ?_⟩
        intro arguments
        exact (resultLaw arguments).trans
          (forall_predicate_iff_bottom model body _ predicates source bottom empty).symm



def Term.applyTuple : {length : Nat} → Term → (Fin length → Term) → Term
  | 0, function, _ => function
  | _ + 1, function, arguments =>
      Term.applyTuple (.app function (arguments 0)) (fun i => arguments i.succ)

theorem value_applyTuple (model : Interpretation D R) (objects : ObjectAssignment D)
    (length : Nat) (function : Term) (arguments : Fin length → Term) :
    (Term.applyTuple function arguments).value model objects =
      applyArguments model (function.value model objects)
        (fun i => (arguments i).value model objects) := by
  induction length generalizing function with
  | zero => rfl
  | succ length ih => exact ih (.app function (arguments 0)) (fun i => arguments i.succ)

def programTerm (length index : Nat) : Term :=
  Term.applyTuple (.var (length + index)) (fun i : Fin length => .var i.val)

@[simp] theorem value_programTerm (model : Interpretation D R) (length index : Nat)
    (arguments : Fin length → D) (parameters : ObjectAssignment D) :
    (programTerm length index).value model (assignTuple length arguments parameters) =
      applyArguments model (parameters index) arguments := by
  simp only [programTerm, value_applyTuple, Term.value, assignTuple_after, assignTuple_at]

def relationAtom (arity index : Nat) : Formula :=
  .relation arity index (fun i => .var i.val)

@[simp] theorem truth_relationAtom (model : Interpretation D R) (arity index : Nat)
    (arguments : Fin (arity + 1) → D) (parameters : ObjectAssignment D)
    (predicates : PredicateAssignment R) :
    (relationAtom arity index).truth model (assignTuple (arity + 1) arguments parameters) predicates ↔
      model.satisfies arity (predicates arity index) arguments := by
  simp only [relationAtom, Formula.truth, Term.value, assignTuple_at]

def projectionAtom (arity : Nat) : Formula :=
  .relation (arity + 1) 0
    (Fin.lastCases (.var 0) (fun i : Fin (arity + 1) => .var (i.val + 1)))

@[simp] theorem truth_projectionAtom (model : Interpretation D R) (arity : Nat)
    (arguments : Fin (arity + 1) → D) (parameters : ObjectAssignment D)
    (predicates : PredicateAssignment R) (value : D) :
    (projectionAtom arity).truth model
      (pushObject (assignTuple (arity + 1) arguments parameters) value) predicates ↔
      model.satisfies (arity + 1) (predicates (arity + 1) 0) (appendLast arguments value) := by
  unfold projectionAtom Formula.truth
  have same : (fun i : Fin (arity + 2) =>
      Term.value model (pushObject (assignTuple (arity + 1) arguments parameters) value)
        (Fin.lastCases (.var 0) (fun i : Fin (arity + 1) => .var (i.val + 1)) i)) =
      appendLast arguments value := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.lastCases_last, Term.value, pushObject, appendLast_last]
    · simp only [Fin.lastCases_castSucc, Term.value, pushObject, appendLast_castSucc]
      exact assignTuple_at _ _ _ i
  rw [same]

/-- Every B1--B5 instance is an instance of the concrete positive grammar. -/
theorem positive_comprehension_implies_closure (model : Interpretation D R)
    (comprehension : HasPositiveComprehension model) : PositiveClosure model := by
  classical
  let initial : PredicateAssignment R := fun arity _ =>
    Classical.choice (comprehension.relations_nonempty arity)
  let parameters : ObjectAssignment D := fun _ => model.constantK
  refine {
    toEqualityAndPreimages := { equality := ?_, preimage := ?_ }
    intersection := ?_
    union := ?_
    existsProjection := ?_
    forallProjection := ?_
  }
  · obtain ⟨result, resultLaw⟩ := comprehension.comprehend 1
      (.equal (.var 0) (.var 1)) parameters initial
    refine ⟨result, ?_⟩
    intro arguments
    exact resultLaw arguments
  · intro source target relation programs
    let predicates := pushPredicate initial source relation
    let coefficients := assignTuple (source + 1) programs parameters
    let body := Formula.relation source 0
      (fun i : Fin (source + 1) => programTerm (target + 1) i.val)
    obtain ⟨result, resultLaw⟩ := comprehension.comprehend target body coefficients predicates
    refine ⟨result, ?_⟩
    intro arguments
    simpa only [body, Formula.truth, value_programTerm, coefficients,
      assignTuple_at, predicates, pushPredicate, dite_true] using resultLaw arguments
  · intro arity left right
    let predicates := pushPredicate (pushPredicate initial arity right) arity left
    obtain ⟨result, resultLaw⟩ := comprehension.comprehend arity
      (.conjunction (relationAtom arity 0) (relationAtom arity 1)) parameters predicates
    refine ⟨result, ?_⟩
    intro arguments
    simpa only [Formula.truth, relationAtom, Term.value, assignTuple_at, predicates,
      pushPredicate, dite_true] using resultLaw arguments
  · intro arity left right
    let predicates := pushPredicate (pushPredicate initial arity right) arity left
    obtain ⟨result, resultLaw⟩ := comprehension.comprehend arity
      (.disjunction (relationAtom arity 0) (relationAtom arity 1)) parameters predicates
    refine ⟨result, ?_⟩
    intro arguments
    simpa only [Formula.truth, relationAtom, Term.value, assignTuple_at, predicates,
      pushPredicate, dite_true] using resultLaw arguments
  · intro arity relation
    let predicates := pushPredicate initial (arity + 1) relation
    obtain ⟨result, resultLaw⟩ := comprehension.comprehend arity
      (.existsObject (projectionAtom arity)) parameters predicates
    refine ⟨result, ?_⟩
    intro arguments
    change model.satisfies arity result arguments ↔ _
    rw [resultLaw]
    change (∃ value, (projectionAtom arity).truth model
      (pushObject (assignTuple (arity + 1) arguments parameters) value) predicates) ↔ _
    simp only [truth_projectionAtom, predicates, pushPredicate, dite_true]
  · intro arity relation
    let predicates := pushPredicate initial (arity + 1) relation
    obtain ⟨result, resultLaw⟩ := comprehension.comprehend arity
      (.forallObject (projectionAtom arity)) parameters predicates
    refine ⟨result, ?_⟩
    intro arguments
    rw [resultLaw]
    change (∀ value, (projectionAtom arity).truth model
      (pushObject (assignTuple (arity + 1) arguments parameters) value) predicates) ↔ _
    simp only [truth_projectionAtom, predicates, pushPredicate, dite_true]

/-- B1--B5 and strict-positive comprehension are equivalent over a nontrivial
K/S algebra. No extensionality or predicate-identity principle is required. -/
theorem positive_closure_iff_comprehension (model : Interpretation D R)
    (laws : CombinatoryLaws model) (nontrivial : ∃ a b : D, a ≠ b) :
    PositiveClosure model ↔ HasPositiveComprehension model :=
  ⟨positive_closure_implies_comprehension model laws nontrivial,
    positive_comprehension_implies_closure model⟩


end FregeanECA.Positive
