import FregeanECA.Part2.Axioms

namespace FregeanECA.Part2
open Axioms
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

def complementBody (n : Nat) : Applicative.Formula :=
  .implies (.relation n 0 (fun i => .var i.val)) .falsum

def complementAxiom (n : Nat) : Functional.Formula :=
  fullRelationalComprehension n (complementBody n).functional

def predicateProjectionAxiom (n m : Nat) (body : Applicative.Formula) : Functional.Formula :=
  .implies
    (.forallPredicate m (fullRelationalComprehension n body.functional))
    (fullRelationalComprehension n (Applicative.Formula.existsPredicate m body).functional)

/-- Literal ECA+B1--B5+C+Q, rather than using comprehension as its axiom. -/
inductive AlgebraAxiom : Functional.Formula → Prop where
  | original {p} (h : SpecificationAxiom p) : AlgebraAxiom p
  | complement (n) : AlgebraAxiom (complementAxiom n)
  | projection (n m) (body : Applicative.Formula) : AlgebraAxiom (predicateProjectionAxiom n m body)

theorem shared_full_comprehension_truth (M : Functional.Interpretation D F R)
    (n : Nat) (body : Applicative.Formula) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    (fullRelationalComprehension n body.functional).truth M o f r ↔
      ∃ p : R n, ∀ xs, M.applicative.satisfies n p xs ↔
        body.truth M.applicative (Positive.assignTuple (n+1) xs o) r := by
  rw [fullRelationalComprehension_truth]
  exact exists_congr (fun p => forall_congr' (fun xs =>
    iff_congr Iff.rfl (shared_formula_preserves_truth M body _ _ _)))

theorem complement_body_truth (M : Positive.Interpretation D R) (n : Nat)
    (xs : Fin (n+1) → D) (o : Nat → D) (r : Positive.PredicateAssignment R) :
    (complementBody n).truth M (Positive.assignTuple (n+1) xs o) r ↔
      ¬ M.satisfies n (r n 0) xs := by
  simp only [complementBody, Applicative.Formula.truth, Positive.Term.value,
    Positive.assignTuple_at]

theorem algebra_axioms_of_conditions (M : Functional.Interpretation D F R)
    (h : FullTSConditions M.applicative) : ∀ p, AlgebraAxiom p → Valid M p := by
  intro p hp o f r
  cases hp with
  | original old => exact specification_axioms_of_conditions M h.toTSConditions p old o f r
  | complement n =>
      exact (shared_full_comprehension_truth M n (complementBody n) o f r).mpr
        (h.full_comprehension.comprehend n (complementBody n) o r)
  | projection n m body =>
      intro _
      exact (shared_full_comprehension_truth M n (.existsPredicate m body) o f r).mpr
        (h.full_comprehension.comprehend n (.existsPredicate m body) o r)

theorem conditions_of_algebra_axioms (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, AlgebraAxiom p → Valid M p) : FullTSConditions M.applicative := by
  classical
  let f : Nat → F := fun _ => Classical.choice inferInstance
  let rs : Positive.PredicateAssignment R := fun _ _ => Classical.choice inferInstance
  let os : Nat → D := fun _ => M.applicative.constantK
  have ts := conditions_of_specification_axioms M (fun p hp => h p (.original hp))
  have closure : ClassicalClosure M.applicative := {
    positive := ts.closure
    complemented := {
      complement := by
        intro n p
        let r := Positive.pushPredicate rs n p
        obtain ⟨q, law⟩ := (shared_full_comprehension_truth M n (complementBody n) os f r).mp
          (h _ (.complement n) os f r)
        refine ⟨q, ?_⟩
        intro xs
        simpa only [r, Positive.pushPredicate, dite_true] using
          (law xs).trans (complement_body_truth M.applicative n xs os r) }
    predicateProjection := {
      project := by
        intro n m body o r sections
        have project := h _ (.projection n m body) o f r
        apply (shared_full_comprehension_truth M n (.existsPredicate m body) o f r).mp
        apply project
        intro p
        exact (shared_full_comprehension_truth M n body o f
          (Positive.pushPredicate r m p)).mpr (sections p) } }
  exact { toTSConditions := ts
          full_comprehension := classical_closure_implies_full_comprehension
            M.applicative ts.combinatory closure }

theorem algebra_axioms_iff_conditions (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, AlgebraAxiom p → Valid M p) ↔ FullTSConditions M.applicative :=
  ⟨conditions_of_algebra_axioms M, algebra_axioms_of_conditions M⟩

end FregeanECA.Part2
