import Std

/-!
# Strictly positive applicative formulas

The relation sort indexed by n has arity n + 1. Predicate variables have
separate de Bruijn indices at each arity. Relation representatives may be
duplicated: only their satisfaction relation is used, never their identity.

This module proves structural semantic monotonicity and predicate-quantifier
collapse. Equality and program preimages supply the extremal relations using
iterated K and nontriviality. The construction of witnesses for every positive
comprehension instance, and the TF/TS interpretation, are not encoded here.
-/

namespace FregeanECA.Positive

universe u v

/-- Finite applicative terms. Predicate variables cannot occur in terms. -/
inductive Term where
  | var (index : Nat)
  | constantK
  | constantS
  | app (function argument : Term)

/-- Exactly the positive constructors; no predicate identity, negation, or implication. -/
inductive Formula where
  | equal (left right : Term)
  | relation (arity index : Nat) (arguments : Fin (arity + 1) → Term)
  | conjunction (left right : Formula)
  | disjunction (left right : Formula)
  | existsObject (body : Formula)
  | forallObject (body : Formula)
  | existsPredicate (arity : Nat) (body : Formula)
  | forallPredicate (arity : Nat) (body : Formula)

/-- Arbitrary Henkin relation domains; no extensionality or full powerset assumption. -/
structure Interpretation (D : Type u) (R : Nat → Type v) where
  apply : D → D → D
  constantK : D
  constantS : D
  satisfies : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop

abbrev ObjectAssignment (D : Type u) := Nat → D
abbrev PredicateAssignment (R : Nat → Type v) := (arity : Nat) → Nat → R arity

variable {D : Type u} {R : Nat → Type v}

def pushObject (objects : ObjectAssignment D) (value : D) : ObjectAssignment D
  | 0 => value
  | index + 1 => objects index

/-- Bind a predicate at one arity, leaving variables of other arities unchanged. -/
def pushPredicate (predicates : PredicateAssignment R) (arity : Nat)
    (value : R arity) : PredicateAssignment R :=
  fun other index =>
    if same : other = arity then
      same.symm ▸ (match index with
        | 0 => value
        | index + 1 => predicates arity index)
    else predicates other index

def Term.value (model : Interpretation D R) (objects : ObjectAssignment D) : Term → D
  | .var index => objects index
  | .constantK => model.constantK
  | .constantS => model.constantS
  | .app function argument => model.apply (function.value model objects) (argument.value model objects)

def Formula.truth (model : Interpretation D R) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) : Formula → Prop
  | .equal left right => left.value model objects = right.value model objects
  | .relation arity index arguments =>
      model.satisfies arity (predicates arity index)
        (fun position => (arguments position).value model objects)
  | .conjunction left right => left.truth model objects predicates ∧ right.truth model objects predicates
  | .disjunction left right => left.truth model objects predicates ∨ right.truth model objects predicates
  | .existsObject body => ∃ value, body.truth model (pushObject objects value) predicates
  | .forallObject body => ∀ value, body.truth model (pushObject objects value) predicates
  | .existsPredicate arity body =>
      ∃ value : R arity, body.truth model objects (pushPredicate predicates arity value)
  | .forallPredicate arity body =>
      ∀ value : R arity, body.truth model objects (pushPredicate predicates arity value)

/-- Every assigned lower extension is included in the corresponding upper extension. -/
def AssignmentLE (model : Interpretation D R)
    (lower upper : PredicateAssignment R) : Prop :=
  ∀ arity index arguments,
    model.satisfies arity (lower arity index) arguments →
      model.satisfies arity (upper arity index) arguments

theorem assignment_le_refl (model : Interpretation D R) (predicates : PredicateAssignment R) :
    AssignmentLE model predicates predicates := by
  intro arity index arguments holds
  exact holds

theorem push_predicate_preserves_inclusion
    (model : Interpretation D R) (lower upper : PredicateAssignment R)
    (related : AssignmentLE model lower upper)
    (arity : Nat) (left right : R arity)
    (values : ∀ arguments, model.satisfies arity left arguments →
      model.satisfies arity right arguments) :
    AssignmentLE model (pushPredicate lower arity left)
      (pushPredicate upper arity right) := by
  intro other index arguments
  by_cases same : other = arity
  · subst other
    cases index with
    | zero => simpa [pushPredicate] using values arguments
    | succ index => simpa [pushPredicate] using related arity index arguments
  · simpa [pushPredicate, same] using related other index arguments

/-- Structural monotonicity, including arbitrarily nested predicate quantifiers. -/
theorem positive_truth_is_monotone (model : Interpretation D R) (formula : Formula) :
    ∀ (objects : ObjectAssignment D) (lower upper : PredicateAssignment R),
      AssignmentLE model lower upper →
      formula.truth model objects lower → formula.truth model objects upper := by
  induction formula with
  | equal left right =>
      intro objects lower upper related holds
      exact holds
  | relation arity index arguments =>
      intro objects lower upper related holds
      exact related arity index _ holds
  | conjunction left right leftIH rightIH =>
      intro objects lower upper related holds
      exact ⟨leftIH objects lower upper related holds.1,
        rightIH objects lower upper related holds.2⟩
  | disjunction left right leftIH rightIH =>
      intro objects lower upper related holds
      cases holds with
      | inl left => exact Or.inl (leftIH objects lower upper related left)
      | inr right => exact Or.inr (rightIH objects lower upper related right)
  | existsObject body bodyIH =>
      intro objects lower upper related holds
      obtain ⟨value, holds⟩ := holds
      exact ⟨value, bodyIH (pushObject objects value) lower upper related holds⟩
  | forallObject body bodyIH =>
      intro objects lower upper related holds value
      exact bodyIH (pushObject objects value) lower upper related (holds value)
  | existsPredicate arity body bodyIH =>
      intro objects lower upper related holds
      obtain ⟨value, holds⟩ := holds
      refine ⟨value, bodyIH objects _ _ ?_ holds⟩
      exact push_predicate_preserves_inclusion model lower upper related arity value value
        (fun _ holds => holds)
  | forallPredicate arity body bodyIH =>
      intro objects lower upper related holds value
      apply bodyIH objects _ _ _ (holds value)
      exact push_predicate_preserves_inclusion model lower upper related arity value value
        (fun _ holds => holds)

/-- Duplicate predicate representatives cannot be distinguished by positive formulas. -/
theorem positive_truth_depends_only_on_assigned_extensions
    (model : Interpretation D R) (formula : Formula) (objects : ObjectAssignment D)
    (left right : PredicateAssignment R)
    (same : ∀ arity index arguments,
      model.satisfies arity (left arity index) arguments ↔
        model.satisfies arity (right arity index) arguments) :
    formula.truth model objects left ↔ formula.truth model objects right := by
  constructor
  · exact positive_truth_is_monotone model formula objects left right
      (fun arity index arguments => (same arity index arguments).mp)
  · exact positive_truth_is_monotone model formula objects right left
      (fun arity index arguments => (same arity index arguments).mpr)

def IsTop (model : Interpretation D R) (arity : Nat) (top : R arity) : Prop :=
  ∀ arguments, model.satisfies arity top arguments

def IsBottom (model : Interpretation D R) (arity : Nat) (bottom : R arity) : Prop :=
  ∀ arguments, ¬ model.satisfies arity bottom arguments

/-- Existential predicate quantification reduces to a greatest available extension. -/
theorem exists_predicate_iff_top
    (model : Interpretation D R) (body : Formula) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) (arity : Nat) (top : R arity)
    (universal : IsTop model arity top) :
    (Formula.existsPredicate arity body).truth model objects predicates ↔
      body.truth model objects (pushPredicate predicates arity top) := by
  constructor
  · intro holds
    obtain ⟨value, holds⟩ := holds
    apply positive_truth_is_monotone model body objects _ _ _ holds
    exact push_predicate_preserves_inclusion model predicates predicates
      (assignment_le_refl model predicates) arity value top
      (fun arguments _ => universal arguments)
  · intro holds
    exact ⟨top, holds⟩

/-- Universal predicate quantification reduces to a least available extension. -/
theorem forall_predicate_iff_bottom
    (model : Interpretation D R) (body : Formula) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) (arity : Nat) (bottom : R arity)
    (empty : IsBottom model arity bottom) :
    (Formula.forallPredicate arity body).truth model objects predicates ↔
      body.truth model objects (pushPredicate predicates arity bottom) := by
  constructor
  · intro holds
    exact holds bottom
  · intro holds value
    apply positive_truth_is_monotone model body objects _ _ _ holds
    exact push_predicate_preserves_inclusion model predicates predicates
      (assignment_le_refl model predicates) arity bottom value
      (fun arguments impossible => False.elim (empty arguments impossible))


/-- Apply a code successively to a finite tuple, from its first coordinate onward. -/
def applyArguments (model : Interpretation D R) : {length : Nat} →
    D → (Fin length → D) → D
  | 0, code, _ => code
  | _ + 1, code, arguments =>
      applyArguments model (model.apply code (arguments 0))
        (fun position => arguments position.succ)

/-- Iterated K represents a constant function of any finite arity. -/
def constantProgram (model : Interpretation D R) : Nat → D → D
  | 0, value => value
  | length + 1, value => model.apply model.constantK (constantProgram model length value)

theorem constant_program_returns_value
    (model : Interpretation D R)
    (constantLaw : ∀ x y, model.apply (model.apply model.constantK x) y = x)
    (length : Nat) (value : D) (arguments : Fin length → D) :
    applyArguments model (constantProgram model length value) arguments = value := by
  induction length with
  | zero => rfl
  | succ length ih =>
      simp only [constantProgram, applyArguments, constantLaw]
      exact ih _

/-- The precise B1 and B3 instances needed to supply extremal relations. -/
structure EqualityAndPreimages (model : Interpretation D R) : Prop where
  equality : ∃ relation : R 1, ∀ arguments,
    model.satisfies 1 relation arguments ↔ arguments 0 = arguments 1
  preimage : ∀ (source target : Nat) (relation : R source)
    (programs : Fin (source + 1) → D),
    ∃ result : R target, ∀ arguments,
      model.satisfies target result arguments ↔
        model.satisfies source relation
          (fun position => applyArguments model (programs position) arguments)

/-- B1 and B3 already give the full relation at every positive arity. -/
theorem equality_and_preimages_supply_top
    (model : Interpretation D R) (closure : EqualityAndPreimages model) (arity : Nat) :
    ∃ top : R arity, IsTop model arity top := by
  obtain ⟨equality, equalityLaw⟩ := closure.equality
  obtain ⟨top, topLaw⟩ := closure.preimage 1 arity equality (fun _ => model.constantK)
  refine ⟨top, ?_⟩
  intro arguments
  exact (topLaw arguments).mpr ((equalityLaw _).mpr rfl)

/-- In a nontrivial K algebra, B1 and B3 also give the empty relation at every arity. -/
theorem equality_and_preimages_supply_bottom
    (model : Interpretation D R) (closure : EqualityAndPreimages model)
    (constantLaw : ∀ x y, model.apply (model.apply model.constantK x) y = x)
    (nontrivial : ∃ a b : D, a ≠ b) (arity : Nat) :
    ∃ bottom : R arity, IsBottom model arity bottom := by
  obtain ⟨a, b, different⟩ := nontrivial
  obtain ⟨equality, equalityLaw⟩ := closure.equality
  let programs : Fin 2 → D := fun position =>
    if position = 0 then constantProgram model (arity + 1) a
    else constantProgram model (arity + 1) b
  obtain ⟨bottom, bottomLaw⟩ := closure.preimage 1 arity equality programs
  refine ⟨bottom, ?_⟩
  intro arguments holds
  have same := (equalityLaw _).mp ((bottomLaw arguments).mp holds)
  have : a = b := by
    simpa [programs, constant_program_returns_value model constantLaw] using same
  exact different this

/-- B1+B3 and nontriviality supply the witnesses needed by both collapse theorems. -/
theorem closure_supplies_predicate_quantifier_collapse
    (model : Interpretation D R) (closure : EqualityAndPreimages model)
    (constantLaw : ∀ x y, model.apply (model.apply model.constantK x) y = x)
    (nontrivial : ∃ a b : D, a ≠ b) (arity : Nat) :
    ∃ top bottom : R arity, ∀ (body : Formula) (objects : ObjectAssignment D)
      (predicates : PredicateAssignment R),
      ((Formula.existsPredicate arity body).truth model objects predicates ↔
        body.truth model objects (pushPredicate predicates arity top)) ∧
      ((Formula.forallPredicate arity body).truth model objects predicates ↔
        body.truth model objects (pushPredicate predicates arity bottom)) := by
  obtain ⟨top, universal⟩ := equality_and_preimages_supply_top model closure arity
  obtain ⟨bottom, empty⟩ :=
    equality_and_preimages_supply_bottom model closure constantLaw nontrivial arity
  refine ⟨top, bottom, ?_⟩
  intro body objects predicates
  exact ⟨exists_predicate_iff_top model body objects predicates arity top universal,
    forall_predicate_iff_bottom model body objects predicates arity bottom empty⟩


end FregeanECA.Positive
