import FregeanECA.Positive

/-! The two actual first-order languages, with separate variable stacks for
each sort. Equality of relation and function representatives is permitted in
ambient formulas but deliberately absent from positive comprehension bodies.
-/
namespace FregeanECA
universe u v w

namespace Applicative

inductive Formula where
  | equal (left right : Positive.Term)
  | relation (arity index : Nat) (arguments : Fin (arity + 1) → Positive.Term)
  | relationEqual (arity left right : Nat)
  | falsum
  | implies (left right : Formula)
  | conjunction (left right : Formula)
  | disjunction (left right : Formula)
  | existsObject (body : Formula)
  | forallObject (body : Formula)
  | existsPredicate (arity : Nat) (body : Formula)
  | forallPredicate (arity : Nat) (body : Formula)

def Formula.truth {D : Type u} {R : Nat → Type v}
    (model : Positive.Interpretation D R) (objects : Nat → D)
    (predicates : Positive.PredicateAssignment R) : Formula → Prop
  | .equal left right => left.value model objects = right.value model objects
  | .relation arity index arguments => model.satisfies arity (predicates arity index)
      (fun i => (arguments i).value model objects)
  | .relationEqual arity left right => predicates arity left = predicates arity right
  | .falsum => False
  | .implies left right => left.truth model objects predicates → right.truth model objects predicates
  | .conjunction left right => left.truth model objects predicates ∧ right.truth model objects predicates
  | .disjunction left right => left.truth model objects predicates ∨ right.truth model objects predicates
  | .existsObject body => ∃ x, body.truth model (Positive.pushObject objects x) predicates
  | .forallObject body => ∀ x, body.truth model (Positive.pushObject objects x) predicates
  | .existsPredicate arity body => ∃ P, body.truth model objects (Positive.pushPredicate predicates arity P)
  | .forallPredicate arity body => ∀ P, body.truth model objects (Positive.pushPredicate predicates arity P)

end Applicative

namespace Functional

inductive Term where
  | var (index : Nat)
  | constantK
  | constantS
  | app (function argument : Term)
  | eval (function : Nat) (argument : Term)
  | delta (function : Nat)

structure Interpretation (D : Type u) (F : Type v) (R : Nat → Type w) where
  applicative : Positive.Interpretation D R
  eval : F → D → D
  delta : F → D

/-- The paper's f(x-vector), encoded by the represented object and its
nonempty argument vector. `evalVector_eq_curried` identifies this with native
evaluation at the first argument followed by the remaining arguments. -/
abbrev Interpretation.evalVector {D : Type u} {F : Type v} {R : Nat → Type w}
    (model : Interpretation D F R) (f : F) {arity : Nat}
    (arguments : Fin (arity + 1) → D) : D :=
  Positive.applyArguments model.applicative (model.delta f) arguments

/-- The notation agrees with the original curried evaluation under the
already present defining equation for object application. -/
theorem Interpretation.evalVector_eq_curried {D : Type u} {F : Type v} {R : Nat → Type w}
    (model : Interpretation D F R)
    (evaluation : ∀ f x, model.eval f x = model.applicative.apply (model.delta f) x)
    (f : F) {arity : Nat} (arguments : Fin (arity + 1) → D) :
    model.evalVector f arguments =
      Positive.applyArguments model.applicative (model.eval f (arguments 0))
        (fun i => arguments i.succ) := by
  change Positive.applyArguments model.applicative
    (model.applicative.apply (model.delta f) (arguments 0)) _ = _
  rw [evaluation]

theorem Interpretation.evalVector_unary {D : Type u} {F : Type v} {R : Nat → Type w}
    (model : Interpretation D F R)
    (evaluation : ∀ f x, model.eval f x = model.applicative.apply (model.delta f) x)
    (f : F) (x : D) : model.evalVector f (fun _ : Fin 1 => x) = model.eval f x :=
  (evaluation f x).symm

def Term.value {D : Type u} {F : Type v} {R : Nat → Type w}
    (model : Interpretation D F R) (objects : Nat → D) (functions : Nat → F) : Term → D
  | .var i => objects i
  | .constantK => model.applicative.constantK
  | .constantS => model.applicative.constantS
  | .app f x => model.applicative.apply (f.value model objects functions) (x.value model objects functions)
  | .eval f x => model.eval (functions f) (x.value model objects functions)
  | .delta f => model.delta (functions f)

inductive PositiveFormula where
  | equal (left right : Term)
  | relation (arity index : Nat) (arguments : Fin (arity + 1) → Term)
  | conjunction (left right : PositiveFormula)
  | disjunction (left right : PositiveFormula)
  | existsObject (body : PositiveFormula)
  | forallObject (body : PositiveFormula)
  | existsFunction (body : PositiveFormula)
  | forallFunction (body : PositiveFormula)
  | existsPredicate (arity : Nat) (body : PositiveFormula)
  | forallPredicate (arity : Nat) (body : PositiveFormula)

def PositiveFormula.truth {D : Type u} {F : Type v} {R : Nat → Type w}
    (model : Interpretation D F R) (objects : Nat → D) (functions : Nat → F)
    (predicates : Positive.PredicateAssignment R) : PositiveFormula → Prop
  | .equal left right => left.value model objects functions = right.value model objects functions
  | .relation arity index arguments => model.applicative.satisfies arity (predicates arity index)
      (fun i => (arguments i).value model objects functions)
  | .conjunction left right => left.truth model objects functions predicates ∧ right.truth model objects functions predicates
  | .disjunction left right => left.truth model objects functions predicates ∨ right.truth model objects functions predicates
  | .existsObject body => ∃ x, body.truth model (Positive.pushObject objects x) functions predicates
  | .forallObject body => ∀ x, body.truth model (Positive.pushObject objects x) functions predicates
  | .existsFunction body => ∃ f, body.truth model objects (Positive.pushObject functions f) predicates
  | .forallFunction body => ∀ f, body.truth model objects (Positive.pushObject functions f) predicates
  | .existsPredicate arity body => ∃ P, body.truth model objects functions (Positive.pushPredicate predicates arity P)
  | .forallPredicate arity body => ∀ P, body.truth model objects functions (Positive.pushPredicate predicates arity P)

inductive Formula where
  | equal (left right : Term)
  | relation (arity index : Nat) (arguments : Fin (arity + 1) → Term)
  | relationEqual (arity left right : Nat)
  | functionEqual (left right : Nat)
  | falsum
  | implies (left right : Formula)
  | conjunction (left right : Formula)
  | disjunction (left right : Formula)
  | existsObject (body : Formula)
  | forallObject (body : Formula)
  | existsFunction (body : Formula)
  | forallFunction (body : Formula)
  | existsPredicate (arity : Nat) (body : Formula)
  | forallPredicate (arity : Nat) (body : Formula)

def Formula.truth {D : Type u} {F : Type v} {R : Nat → Type w}
    (model : Interpretation D F R) (objects : Nat → D) (functions : Nat → F)
    (predicates : Positive.PredicateAssignment R) : Formula → Prop
  | .equal left right => left.value model objects functions = right.value model objects functions
  | .relation arity index arguments => model.applicative.satisfies arity (predicates arity index)
      (fun i => (arguments i).value model objects functions)
  | .relationEqual arity left right => predicates arity left = predicates arity right
  | .functionEqual left right => functions left = functions right
  | .falsum => False
  | .implies left right => left.truth model objects functions predicates → right.truth model objects functions predicates
  | .conjunction left right => left.truth model objects functions predicates ∧ right.truth model objects functions predicates
  | .disjunction left right => left.truth model objects functions predicates ∨ right.truth model objects functions predicates
  | .existsObject body => ∃ x, body.truth model (Positive.pushObject objects x) functions predicates
  | .forallObject body => ∀ x, body.truth model (Positive.pushObject objects x) functions predicates
  | .existsFunction body => ∃ f, body.truth model objects (Positive.pushObject functions f) predicates
  | .forallFunction body => ∀ f, body.truth model objects (Positive.pushObject functions f) predicates
  | .existsPredicate arity body => ∃ P, body.truth model objects functions (Positive.pushPredicate predicates arity P)
  | .forallPredicate arity body => ∀ P, body.truth model objects functions (Positive.pushPredicate predicates arity P)

/-- Lift a variable map under a binder of its own sort. -/
def bindMap (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f n + 1

/-- Lift variables of a different source sort past the new target object binder. -/
def shiftMap (f : Nat → Nat) (n : Nat) : Nat := f n + 1

def Term.translate (objects functions : Nat → Nat) : Term → Positive.Term
  | .var i => .var (objects i)
  | .constantK => .constantK
  | .constantS => .constantS
  | .app f x => .app (f.translate objects functions) (x.translate objects functions)
  | .eval f x => .app (.var (functions f)) (x.translate objects functions)
  | .delta f => .var (functions f)

def PositiveFormula.translate (objects functions : Nat → Nat) : PositiveFormula → Positive.Formula
  | .equal left right => .equal (left.translate objects functions) (right.translate objects functions)
  | .relation arity index arguments => .relation arity index (fun i => (arguments i).translate objects functions)
  | .conjunction left right => .conjunction (left.translate objects functions) (right.translate objects functions)
  | .disjunction left right => .disjunction (left.translate objects functions) (right.translate objects functions)
  | .existsObject body => .existsObject (body.translate (bindMap objects) (shiftMap functions))
  | .forallObject body => .forallObject (body.translate (bindMap objects) (shiftMap functions))
  | .existsFunction body => .existsObject (body.translate (shiftMap objects) (bindMap functions))
  | .forallFunction body => .forallObject (body.translate (shiftMap objects) (bindMap functions))
  | .existsPredicate arity body => .existsPredicate arity (body.translate objects functions)
  | .forallPredicate arity body => .forallPredicate arity (body.translate objects functions)

def Formula.translate (objects functions : Nat → Nat) : Formula → Applicative.Formula
  | .equal left right => .equal (left.translate objects functions) (right.translate objects functions)
  | .relation arity index arguments => .relation arity index (fun i => (arguments i).translate objects functions)
  | .relationEqual arity left right => .relationEqual arity left right
  | .functionEqual left right => .equal (.var (functions left)) (.var (functions right))
  | .falsum => .falsum
  | .implies left right => .implies (left.translate objects functions) (right.translate objects functions)
  | .conjunction left right => .conjunction (left.translate objects functions) (right.translate objects functions)
  | .disjunction left right => .disjunction (left.translate objects functions) (right.translate objects functions)
  | .existsObject body => .existsObject (body.translate (bindMap objects) (shiftMap functions))
  | .forallObject body => .forallObject (body.translate (bindMap objects) (shiftMap functions))
  | .existsFunction body => .existsObject (body.translate (shiftMap objects) (bindMap functions))
  | .forallFunction body => .forallObject (body.translate (shiftMap objects) (bindMap functions))
  | .existsPredicate arity body => .existsPredicate arity (body.translate objects functions)
  | .forallPredicate arity body => .forallPredicate arity (body.translate objects functions)

end Functional

def Positive.Term.functional : Positive.Term → Functional.Term
  | .var i => .var i
  | .constantK => .constantK
  | .constantS => .constantS
  | .app f x => .app f.functional x.functional

def Positive.Formula.functional : Positive.Formula → Functional.PositiveFormula
  | .equal left right => .equal left.functional right.functional
  | .relation arity index arguments => .relation arity index (fun i => (arguments i).functional)
  | .conjunction left right => .conjunction left.functional right.functional
  | .disjunction left right => .disjunction left.functional right.functional
  | .existsObject body => .existsObject body.functional
  | .forallObject body => .forallObject body.functional
  | .existsPredicate arity body => .existsPredicate arity body.functional
  | .forallPredicate arity body => .forallPredicate arity body.functional

def Applicative.Formula.functional : Applicative.Formula → Functional.Formula
  | .equal left right => .equal left.functional right.functional
  | .relation arity index arguments => .relation arity index (fun i => (arguments i).functional)
  | .relationEqual arity left right => .relationEqual arity left right
  | .falsum => .falsum
  | .implies left right => .implies left.functional right.functional
  | .conjunction left right => .conjunction left.functional right.functional
  | .disjunction left right => .disjunction left.functional right.functional
  | .existsObject body => .existsObject body.functional
  | .forallObject body => .forallObject body.functional
  | .existsPredicate arity body => .existsPredicate arity body.functional
  | .forallPredicate arity body => .forallPredicate arity body.functional

end FregeanECA
