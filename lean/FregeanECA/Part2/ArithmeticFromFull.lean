import FregeanECA.Part2.Arithmetic
import FregeanECA.Part2.Models
import FregeanECA.Part2.Closure

/-!
# Full comprehension supplies the arithmetic domain

This module discharges the explicit comprehension and intersection premises
of Arithmetic.lean from the actual FullTSConditions. The final certificate
contains induction for every existing Applicative.Formula with parameters.
Addition, multiplication, and a Z2 proof translation remain separate work.
-/

namespace FregeanECA.Part2.Arithmetic

universe u v
variable {D : Type u} {R : Nat → Type v}

theorem full_comprehension_represents_unary_formula
    (M : Positive.Interpretation D R) (full : HasFullComprehension M)
    (formula : Applicative.Formula) (parameters : Positive.ObjectAssignment D)
    (predicates : Positive.PredicateAssignment R) :
    ∃ P : R 0, ∀ x, member M P x ↔
      formula.truth M (Positive.pushObject parameters x) predicates := by
  obtain ⟨P, represents⟩ := full.comprehend 0 formula parameters predicates
  exact ⟨P, fun x => represents (fun _ => x)⟩

/-- This is the specific impredicative instance, now proved from the full schema. -/
theorem full_comprehension_supplies_least_instance
    (M : Positive.Interpretation D R) (full : HasFullComprehension M)
    (parameters : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    LeastComprehensionInstance M parameters predicates :=
  full_comprehension_represents_unary_formula M full leastInductiveFormula parameters predicates

/-- Unary intersections require only the old positive closure axiom B2. -/
theorem positive_closure_supplies_unary_intersections
    (M : Positive.Interpretation D R) (closure : Positive.PositiveClosure M) :
    UnaryIntersection M := by
  intro P Q
  obtain ⟨H, represents⟩ := closure.intersection 0 P Q
  exact ⟨H, fun x => represents (fun _ => x)⟩

/-- A Peano successor domain and induction for every classical object/relation
formula in the actual syntax. This record does not contain arithmetic operations. -/
structure PeanoDomain (M : Positive.Interpretation D R) (N : R 0) : Prop where
  represents_least : RepresentsLeast M N
  zero_member : member M N (modelZero M)
  successor_closed : ∀ x, member M N x → member M N (modelSuccessor M x)
  zero_not_successor : ∀ x, modelZero M ≠ modelSuccessor M x
  successor_injective : ∀ x y, modelSuccessor M x = modelSuccessor M y → x = y
  formula_induction : ∀ (formula : Applicative.Formula)
    (parameters : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R),
    formula.truth M (Positive.pushObject parameters (modelZero M)) predicates →
    (∀ x, member M N x →
      formula.truth M (Positive.pushObject parameters x) predicates →
      formula.truth M (Positive.pushObject parameters (modelSuccessor M x)) predicates) →
    ∀ x, member M N x →
      formula.truth M (Positive.pushObject parameters x) predicates

/-- Every full specification model contains the required successor domain;
no separate comprehension instance or pre-existing arithmetic domain is assumed. -/
theorem full_ts_has_peano_domain (M : Positive.Interpretation D R)
    (full : FullTSConditions M) : ∃ N : R 0, PeanoDomain M N := by
  classical
  let parameters : Positive.ObjectAssignment D := fun _ => M.constantK
  let predicates : Positive.PredicateAssignment R :=
    fun n _ => Classical.choice (full.full_comprehension.relations_nonempty n)
  obtain ⟨N, represents, closed, _⟩ := least_inductive_domain M parameters predicates
    (full_comprehension_supplies_least_instance M full.full_comprehension parameters predicates)
  have intersections := positive_closure_supplies_unary_intersections M full.closure
  refine ⟨N, { represents_least := represents
               zero_member := closed.1
               successor_closed := closed.2
               zero_not_successor := ?_
               successor_injective := ?_
               formula_induction := ?_ }⟩
  · exact zero_not_successor full.combinatory.algebra full.nontrivial
  · intro x y same
    exact successor_injective full.combinatory.algebra same
  · intro formula objectParameters relationParameters base step
    exact represented_formula_induction M intersections represents formula
      objectParameters relationParameters
      (full_comprehension_represents_unary_formula M full.full_comprehension
        formula objectParameters relationParameters) base step

/-- The explicit open-term full model is an unconditional instance of the
preceding general theorem. -/
theorem open_specification_has_peano_domain :
    ∃ N, PeanoDomain openSpecification N :=
  full_ts_has_peano_domain openSpecification openSpecification_satisfies_full_TS

end FregeanECA.Part2.Arithmetic
