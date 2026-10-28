import Frege.Programs

/-!
# The algebra used in the consistency construction

This file proves the bracket-abstraction part of Appendix D.3. It does not
assume a lambda interpreter: it constructs program meanings from an application
operation and the two combinator laws. Extensionality is a separate property.

Existence of a nontrivial algebra and completion by concept abstractions are
separate obligations. In particular, this file alone is not a consistency proof.
-/

namespace Frege

universe u c

/-- A total combinatory algebra, presented by its operation and defining laws. -/
structure CombinatoryAlgebra (Object : Type u) where
  apply : Object → Object → Object
  constant : Object
  distribute : Object
  constant_returns_first_argument : ∀ first second,
    apply (apply constant first) second = first
  distribute_applies_the_same_argument : ∀ left right argument,
    apply (apply (apply distribute left) right) argument =
      apply (apply left argument) (apply right argument)

namespace CombinatoryAlgebra

variable {Object : Type u} (algebra : CombinatoryAlgebra Object)

/-- Objects are equal whenever they agree on every argument. -/
def IsExtensional : Prop := ∀ left right,
  (∀ argument, algebra.apply left argument = algebra.apply right argument) → left = right

def identity : Object :=
  algebra.apply (algebra.apply algebra.distribute algebra.constant) algebra.constant

/-- The usual identity combinator really returns its argument. -/
theorem identity_returns_its_argument (argument : Object) :
    algebra.apply algebra.identity argument = argument := by
  unfold identity
  rw [algebra.distribute_applies_the_same_argument]
  exact algebra.constant_returns_first_argument _ _

end CombinatoryAlgebra

/-- Terms with no binders: all abstraction will be eliminated into combinators. -/
inductive CombinatorTerm (Coefficient : Type c) : Nat → Type c where
  | variable : Fin n → CombinatorTerm Coefficient n
  | coefficient : Coefficient → CombinatorTerm Coefficient n
  | constant : CombinatorTerm Coefficient n
  | distribute : CombinatorTerm Coefficient n
  | application : CombinatorTerm Coefficient n → CombinatorTerm Coefficient n →
      CombinatorTerm Coefficient n

namespace CombinatorTerm

variable {Coefficient : Type c} {Object : Type u}

/-- Eliminate the newest variable. Coefficients are independent of binders. -/
def abstractNewest : CombinatorTerm Coefficient (n + 1) → CombinatorTerm Coefficient n
  | .variable index => Fin.cases
      (.application (.application .distribute .constant) .constant)
      (fun older => .application .constant (.variable older)) index
  | .coefficient value => .application .constant (.coefficient value)
  | .constant => .application .constant .constant
  | .distribute => .application .constant .distribute
  | .application left right =>
      .application (.application .distribute (abstractNewest left)) (abstractNewest right)

def evaluate (algebra : CombinatoryAlgebra Object) (coefficient : Coefficient → Object) :
    CombinatorTerm Coefficient n → (Fin n → Object) → Object
  | .variable index, environment => environment index
  | .coefficient value, _ => coefficient value
  | .constant, _ => algebra.constant
  | .distribute, _ => algebra.distribute
  | .application left right, environment =>
      algebra.apply (evaluate algebra coefficient left environment)
        (evaluate algebra coefficient right environment)

/-- Applying the abstracted code evaluates the body with the supplied argument.

Proof: variables use identity or a constant; application uses the distributive
combinator and the two induction hypotheses. No extensionality is needed.
-/
theorem applying_an_abstraction_substitutes_its_argument
    (algebra : CombinatoryAlgebra Object) (coefficient : Coefficient → Object)
    (body : CombinatorTerm Coefficient (n + 1))
    (environment : Fin n → Object) (argument : Object) :
    algebra.apply (evaluate algebra coefficient body.abstractNewest environment) argument =
      evaluate algebra coefficient body (Fin.cases argument environment) := by
  induction body with
  | «variable» index =>
      refine Fin.cases ?_ (fun older => ?_) index
      · exact algebra.identity_returns_its_argument argument
      · exact algebra.constant_returns_first_argument _ _
  | coefficient value => exact algebra.constant_returns_first_argument _ _
  | constant => exact algebra.constant_returns_first_argument _ _
  | distribute => exact algebra.constant_returns_first_argument _ _
  | application left right left_correct right_correct =>
      simp only [abstractNewest, evaluate]
      rw [algebra.distribute_applies_the_same_argument, left_correct, right_correct]

/-- Translate every program, eliminating inner binders before outer binders. -/
def fromProgram : Program Coefficient n → CombinatorTerm Coefficient n
  | .var index => .variable index
  | .coeff value => .coefficient value
  | .app left right => .application (fromProgram left) (fromProgram right)
  | .lam body => abstractNewest (fromProgram body)

end CombinatorTerm

namespace CombinatoryAlgebra

variable {Object : Type u} {Coefficient : Type c}
variable (algebra : CombinatoryAlgebra Object) (coefficient : Coefficient → Object)

/-- The constructed meaning of a program, not a separately assumed interpreter. -/
def programMeaning (program : Program Coefficient n) (environment : Fin n → Object) : Object :=
  CombinatorTerm.evaluate algebra coefficient (CombinatorTerm.fromProgram program) environment

@[simp] theorem meaning_of_a_variable (index : Fin n) (environment : Fin n → Object) :
    algebra.programMeaning coefficient (.var index) environment = environment index := rfl

@[simp] theorem meaning_of_a_coefficient (value : Coefficient) (environment : Fin n → Object) :
    algebra.programMeaning coefficient (.coeff value) environment = coefficient value := rfl

@[simp] theorem meaning_of_an_application (left right : Program Coefficient n)
    (environment : Fin n → Object) :
    algebra.programMeaning coefficient (.app left right) environment =
      algebra.apply (algebra.programMeaning coefficient left environment)
        (algebra.programMeaning coefficient right environment) := rfl

/-- Every admitted program binder satisfies substitution in the constructed algebra. -/
theorem every_program_binder_evaluates_its_body
    (body : Program Coefficient (n + 1)) (environment : Fin n → Object) (argument : Object) :
    algebra.apply (algebra.programMeaning coefficient (.lam body) environment) argument =
      algebra.programMeaning coefficient body (Fin.cases argument environment) :=
  CombinatorTerm.applying_an_abstraction_substitutes_its_argument
    algebra coefficient (CombinatorTerm.fromProgram body) environment argument

/-- Extensionality ensures that equal bodies have equal abstraction codes. -/
theorem abstractions_of_pointwise_equal_bodies_are_equal
    (extensional : algebra.IsExtensional)
    (left right : Program Coefficient (n + 1)) (environment : Fin n → Object)
    (bodies_agree : ∀ argument,
      algebra.programMeaning coefficient left (Fin.cases argument environment) =
      algebra.programMeaning coefficient right (Fin.cases argument environment)) :
    algebra.programMeaning coefficient (.lam left) environment =
      algebra.programMeaning coefficient (.lam right) environment := by
  apply extensional
  intro argument
  rw [algebra.every_program_binder_evaluates_its_body,
      algebra.every_program_binder_evaluates_its_body]
  exact bodies_agree argument

end CombinatoryAlgebra
end Frege
