import FregeanECA.Part2.ArithmeticInterpretation

/-! The fixed arithmetic formula translation is sound from full comprehension
and a supplied Peano domain alone. This reuses only the generic recursion and
syntax lemmas, not the ECA construction of that domain or prior proof-transfer
endpoints. In the standard Frege route, HP supplies the Peano domain. -/

namespace FregeanECA.Part2.ArithmeticModelInterpretation
open Arithmetic ArithmeticInterpretation
universe u v
variable {D : Type u} {R : Nat → Type v}

def arithmetic_of_definitions (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A P : R 2} (addition : LeastAddition M N A)
    (multiplication : LeastMultiplication M N A P) : FullArithmetic M N where
  domain := domain
  addition := A
  multiplication := P
  addition_support := addition_support M full domain addition
  multiplication_support := multiplication_support M full domain addition multiplication
  addition_total_unique := addition_total_unique M full domain addition
  multiplication_total_unique := multiplication_total_unique M full domain addition multiplication
  addition_zero_recursion := addition_zero_recursion M full domain addition
  addition_successor_recursion := addition_successor_recursion M full domain addition
  multiplication_zero_recursion := multiplication_zero_recursion M full domain multiplication
  multiplication_successor_recursion := multiplication_successor_recursion M full domain multiplication

theorem interpreted_valid (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    (p : SecondOrderArithmetic.Formula)
    (valid : ∀ G : FullArithmetic M N,
      SecondOrderArithmetic.Valid (SecondOrderArithmetic.arithmeticOperations G) p)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    (ArithmeticInterpretation.interpret p).truth M objects predicates := by
  obtain ⟨A, addition⟩ := full_has_least_addition M full N
  obtain ⟨P, multiplication⟩ := full_has_least_multiplication M full N A
  have defs : definitions.truth M objects (withDefinitions predicates N A P) := by
    apply (definitions_truth M objects _).mpr
    simpa [withDefinitions, Positive.pushPredicate] using
      And.intro domain.represents_least (And.intro addition multiplication)
  refine ⟨N, P, A, defs, ?_⟩
  let assigned := withDefinitions predicates N A P
  let G := arithmetic_of_definitions M full domain addition multiplication
  apply SecondOrderArithmetic.guarded_translation_of_valid
    (SecondOrderArithmetic.arithmeticOperations G) p (valid G) objects assigned rfl
  constructor
  · intro x y z
    simpa [SecondOrderArithmetic.triple_eq_arithmetic, member3, G,
      arithmetic_of_definitions, assigned, withDefinitions, Positive.pushPredicate]
      using SecondOrderArithmetic.arithmetic_add_graph G x y z
  · intro x y z
    simpa [SecondOrderArithmetic.triple_eq_arithmetic, member3, G,
      arithmetic_of_definitions, assigned, withDefinitions, Positive.pushPredicate]
      using SecondOrderArithmetic.arithmetic_multiply_graph G x y z

open FFL FFL.FirstOrder

/-- Every actual Z2 proof validates the fixed target formula from these exact
model hypotheses. No ECA or previous target Z2 theorem is a premise. -/
theorem interpreted_proof_truth (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    (ArithmeticInterpretation.interpret p).truth M objects predicates :=
  interpreted_valid M full domain p
    (fun G => ArithmeticEncoding.arithmetic_proof_truth G full p proof) objects predicates

end FregeanECA.Part2.ArithmeticModelInterpretation
