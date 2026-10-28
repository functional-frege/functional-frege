import FregeanECA.Part2.SecondOrderArithmetic
import FregeanECA.Part2.ArithmeticFreeVariables
import FregeanECA.Part2.ArithmeticEncoding
import FregeanECA.Part2.Theorems

/-! Canonical, actual formula definitions for the interpreted number domain
and arithmetic graphs. Witness predicates are constrained by their least
definitions; they are never silently treated as arbitrary free parameters. -/

namespace FregeanECA.Part2.ArithmeticInterpretation
open Arithmetic
universe u v
variable {D : Type u} {R : Nat → Type v}

def biconditional (p q : Applicative.Formula) : Applicative.Formula :=
  .conjunction (.implies p q) (.implies q p)

def naturalDefinition : Applicative.Formula :=
  .forallObject (biconditional (unary 0 (.var 0)) leastInductiveFormula)

def additionDefinition : Applicative.Formula :=
  .forallObject (.forallObject (.forallObject
    (biconditional (ternary 0 (.var 0) (.var 1) (.var 2)) leastAdditionFormula)))

def multiplicationDefinition : Applicative.Formula :=
  .forallObject (.forallObject (.forallObject
    (biconditional (ternary 1 (.var 0) (.var 1) (.var 2)) leastMultiplicationFormula)))

def definitions : Applicative.Formula :=
  .conjunction naturalDefinition (.conjunction additionDefinition multiplicationDefinition)

theorem biconditional_truth (M : Positive.Interpretation D R)
    (p q : Applicative.Formula) (objects : Positive.ObjectAssignment D)
    (predicates : Positive.PredicateAssignment R) :
    (biconditional p q).truth M objects predicates ↔
      (p.truth M objects predicates ↔ q.truth M objects predicates) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem natural_definition_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    naturalDefinition.truth M objects predicates ↔ RepresentsLeast M (predicates 0 0) := by
  simp only [naturalDefinition, Applicative.Formula.truth, biconditional_truth,
    least_inductive_formula_truth, unary, Positive.Term.value, Positive.pushObject,
    RepresentsLeast, member]

theorem least_addition_iff_definition (M : Positive.Interpretation D R)
    (N : R 0) (A : R 2) :
    LeastAddition M N A ↔ ∀ x y z, member3 M A x y z ↔
      ∀ P : R 2, AdditionClosed M N P → member3 M P x y z := by
  constructor
  · intro least x y z
    exact ⟨fun h P closed => least.least P closed x y z h,
      fun h => h A least.closed⟩
  · intro law
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro y ny
      exact (law _ _ _).mpr (fun P closed => closed.1 y ny)
    · intro x y z h
      exact (law _ _ _).mpr (fun P closed => closed.2 x y z ((law _ _ _).mp h P closed))
    · intro P closed x y z h
      exact (law _ _ _).mp h P closed

theorem least_multiplication_iff_definition (M : Positive.Interpretation D R)
    (N : R 0) (A P : R 2) :
    LeastMultiplication M N A P ↔ ∀ x y z, member3 M P x y z ↔
      ∀ Q : R 2, MultiplicationClosed M N A Q → member3 M Q x y z := by
  constructor
  · intro least x y z
    exact ⟨fun h Q closed => least.least Q closed x y z h,
      fun h => h P least.closed⟩
  · intro law
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro y ny
      exact (law _ _ _).mpr (fun Q closed => closed.1 y ny)
    · intro x y z w h add
      exact (law _ _ _).mpr (fun Q closed => closed.2 x y z w ((law _ _ _).mp h Q closed) add)
    · intro Q closed x y z h
      exact (law _ _ _).mp h Q closed

theorem addition_definition_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    additionDefinition.truth M objects predicates ↔
      LeastAddition M (predicates 0 0) (predicates 2 0) := by
  rw [least_addition_iff_definition]
  simp only [additionDefinition, Applicative.Formula.truth, biconditional_truth,
    ternary_truth, least_addition_formula_truth, Positive.Term.value, Positive.pushObject]
  constructor <;> intro h x y z <;> exact h z y x

theorem multiplication_definition_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    multiplicationDefinition.truth M objects predicates ↔
      LeastMultiplication M (predicates 0 0) (predicates 2 0) (predicates 2 1) := by
  rw [least_multiplication_iff_definition]
  simp only [multiplicationDefinition, Applicative.Formula.truth, biconditional_truth,
    ternary_truth, least_multiplication_formula_truth, Positive.Term.value, Positive.pushObject]
  constructor <;> intro h x y z <;> exact h z y x

theorem definitions_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    definitions.truth M objects predicates ↔
      RepresentsLeast M (predicates 0 0) ∧
      LeastAddition M (predicates 0 0) (predicates 2 0) ∧
      LeastMultiplication M (predicates 0 0) (predicates 2 0) (predicates 2 1) := by
  simp only [definitions, Applicative.Formula.truth, natural_definition_truth,
    addition_definition_truth, multiplication_definition_truth]

theorem domain_of_definition (M : Positive.Interpretation D R) (full : FullTSConditions M)
    {N : R 0} (represents : RepresentsLeast M N) : PeanoDomain M N := by
  have closed := represented_least_is_inductive M represents
  refine ⟨represents, closed.1, closed.2,
    zero_not_successor full.combinatory.algebra full.nontrivial,
    fun _ _ h => successor_injective full.combinatory.algebra h, ?_⟩
  intro formula objects predicates base step
  exact represented_formula_induction M
    (positive_closure_supplies_unary_intersections M full.closure) represents
    formula objects predicates
    (full_comprehension_represents_unary_formula M full.full_comprehension
      formula objects predicates) base step

def arithmetic_of_definitions (M : Positive.Interpretation D R) (full : FullTSConditions M)
    {N : R 0} {A P : R 2} (represents : RepresentsLeast M N)
    (addition : LeastAddition M N A) (multiplication : LeastMultiplication M N A P) :
    FullArithmetic M N where
  domain := domain_of_definition M full represents
  addition := A
  multiplication := P
  addition_support := addition_support M full.full_comprehension
    (domain_of_definition M full represents) addition
  multiplication_support := multiplication_support M full.full_comprehension
    (domain_of_definition M full represents) addition multiplication
  addition_total_unique := addition_total_unique M full.full_comprehension
    (domain_of_definition M full represents) addition
  multiplication_total_unique := multiplication_total_unique M full.full_comprehension
    (domain_of_definition M full represents) addition multiplication
  addition_zero_recursion := addition_zero_recursion M full.full_comprehension
    (domain_of_definition M full represents) addition
  addition_successor_recursion := addition_successor_recursion M full.full_comprehension
    (domain_of_definition M full represents) addition
  multiplication_zero_recursion := multiplication_zero_recursion M full.full_comprehension
    (domain_of_definition M full represents) multiplication
  multiplication_successor_recursion := multiplication_successor_recursion M full.full_comprehension
    (domain_of_definition M full represents) multiplication

/-- Binder order leaves N at unary slot zero, addition at ternary slot zero,
and multiplication at ternary slot one. -/
def withDefinitions (predicates : Positive.PredicateAssignment R) (N : R 0) (A P : R 2) :=
  Positive.pushPredicate (Positive.pushPredicate (Positive.pushPredicate predicates 0 N) 2 P) 2 A

theorem definitions_exist (M : Positive.Interpretation D R) (full : FullTSConditions M)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    ∃ (N : R 0) (P A : R 2), definitions.truth M objects (withDefinitions predicates N A P) := by
  obtain ⟨N, domain⟩ := full_ts_has_peano_domain M full
  obtain ⟨A, addition⟩ := full_has_least_addition M full.full_comprehension N
  obtain ⟨P, multiplication⟩ := full_has_least_multiplication M full.full_comprehension N A
  refine ⟨N, P, A, ?_⟩
  apply (definitions_truth M objects _).mpr
  simpa [withDefinitions, Positive.pushPredicate] using
    And.intro domain.represents_least (And.intro addition multiplication)

/-- A fixed formula translation. Its existentially bound number domain and
graphs must satisfy their canonical least definitions. Source free number
parameters are guarded; source set parameters remain available relations. -/
def interpret (p : SecondOrderArithmetic.Formula) : Applicative.Formula :=
  .existsPredicate 0 (.existsPredicate 2 (.existsPredicate 2
    (.conjunction definitions (SecondOrderArithmetic.guardedTranslation p))))

theorem interpreted_valid (M : Positive.Interpretation D R) (full : FullTSConditions M)
    (p : SecondOrderArithmetic.Formula)
    (valid : ∀ (N : R 0) (G : FullArithmetic M N),
      SecondOrderArithmetic.Valid (SecondOrderArithmetic.arithmeticOperations G) p)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    (interpret p).truth M objects predicates := by
  obtain ⟨N, P, A, defs⟩ := definitions_exist M full objects predicates
  refine ⟨N, P, A, defs, ?_⟩
  let assigned := withDefinitions predicates N A P
  obtain ⟨natural, addition, multiplication⟩ := (definitions_truth M objects assigned).mp defs
  let G := arithmetic_of_definitions M full natural addition multiplication
  apply SecondOrderArithmetic.guarded_translation_of_valid
    (SecondOrderArithmetic.arithmeticOperations G) p (valid _ G) objects assigned rfl
  constructor
  · intro x y z
    simpa only [SecondOrderArithmetic.triple_eq_arithmetic, member3, G, arithmetic_of_definitions] using
      SecondOrderArithmetic.arithmetic_add_graph G x y z
  · intro x y z
    simpa only [SecondOrderArithmetic.triple_eq_arithmetic, member3, G, arithmetic_of_definitions] using
      SecondOrderArithmetic.arithmetic_multiply_graph G x y z

open FFL FFL.FirstOrder
open scoped FFL.FirstOrder

/-- Target completeness turns the verified model interpretation into an
actual Foundation derivation. The remaining premise will be discharged by
source-calculus soundness, not assumed arithmetic validity. -/
theorem interpreted_provable (p : SecondOrderArithmetic.Formula)
    (valid : ∀ (D : Type) (R : Nat → Type) (M : Positive.Interpretation D R),
      FullTSConditions M → ∀ (N : R 0) (G : FullArithmetic M N),
        SecondOrderArithmetic.Valid (SecondOrderArithmetic.arithmeticOperations G) p) :
    fullAlgebraTheory ⊢ Guarded.sentence (interpret p).functional := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ hM
  have := Encoded.sorts_of_model hM
  let native := Guarded.extracted M
  have full : FullTSConditions native.applicative :=
    (algebra_axioms_iff_conditions native).mp
      ((Encoded.model_iff_valid (Guarded.extractedRealization M) AlgebraAxiom).mp hM)
  apply (Guarded.sentence_truth (Guarded.extractedRealization M)
    inferInstance (fun _ => inferInstance) (interpret p).functional).mpr
  intro objects functions predicates
  exact (shared_formula_preserves_truth native (interpret p) objects functions predicates).mpr
    (interpreted_valid native.applicative full p (valid _ _ _ full) objects predicates)

/-- Every actual Z2 proof transfers to the full algebraic theory under the
fixed, canonically guarded translation defined above. -/
theorem Z2_proof_transfer (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    fullAlgebraTheory ⊢ Guarded.sentence (interpret p).functional :=
  interpreted_provable p (fun _ _ _ full _ G =>
    ArithmeticEncoding.arithmetic_proof_truth G full.full_comprehension p proof)

/-- The same arithmetic interpretation transfers through the proved Fregean
equivalence; no second arithmetic construction is needed. -/
theorem Z2_proof_transfer_fregean (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    fullFunctionalTheory ⊢ Guarded.sentence (interpret p).functional :=
  (full_functional_algebra_provability (interpret p)).mpr (Z2_proof_transfer p proof)

theorem interpretation_preserves_falsum (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    (interpret .falsum).truth M objects predicates ↔ False := by
  simp [interpret, SecondOrderArithmetic.guardedTranslation,
    SecondOrderArithmetic.numberGuards, SecondOrderArithmetic.Formula.numberBound,
    SecondOrderArithmetic.Formula.translate, Applicative.Formula.truth]

end FregeanECA.Part2.ArithmeticInterpretation
