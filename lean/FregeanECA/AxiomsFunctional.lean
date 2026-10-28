import FregeanECA.Axioms
import FregeanECA.Equivalence

namespace FregeanECA.Axioms
open Functional
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

def Valid (M : Interpretation D F R) (p : Formula) : Prop :=
  ∀ o f r, p.truth M o f r

theorem kLaw_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    kLaw.truth M o f r ↔ ∀ x y,
      M.applicative.apply (M.applicative.apply M.applicative.constantK x) y = x := by
  change (∀ y x, M.applicative.apply (M.applicative.apply M.applicative.constantK x) y = x) ↔ _
  exact forall_comm

theorem sLaw_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    sLaw.truth M o f r ↔ ∀ x y z,
      M.applicative.apply (M.applicative.apply (M.applicative.apply M.applicative.constantS x) y) z =
        M.applicative.apply (M.applicative.apply x z) (M.applicative.apply y z) := by
  constructor
  · intro h x y z; exact h z y x
  · intro h z y x; exact h x y z

theorem lawV_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    lawV.truth M o f r ↔ ∀ a b,
      M.delta a = M.delta b ↔ ∀ x, M.eval a x = M.eval b x := by
  constructor
  · intro h a b; exact (iffF_truth M _ _ _ _ _).mp (h b a)
  · intro h b a; exact (iffF_truth M _ _ _ _ _).mpr (h a b)

theorem coverage_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    coverage.truth M o f r ↔ ∀ a, ∃ g, M.delta g = a := Iff.rfl

theorem evaluation_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    evaluation.truth M o f r ↔ ∀ g x, M.eval g x = M.applicative.apply (M.delta g) x := Iff.rfl

theorem nontriviality_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    nontriviality.truth M o f r ↔ ∃ a b : D, a ≠ b := by
  constructor
  · rintro ⟨b,a,h⟩; exact ⟨a,b,h⟩
  · rintro ⟨a,b,h⟩; exact ⟨b,a,h⟩

theorem functional_axioms_of_conditions (M : Interpretation D F R)
    (h : TFConditions M) : ∀ p, FunctionalAxiom p → Valid M p := by
  intro p hp o f r
  cases hp with
  | relational n body =>
      exact (relationalComprehension_truth M n body o f r).mpr
        (h.comprehension.comprehend n body o f r)
  | functional n body =>
      exact (functionalComprehension_truth M n body o f r).mpr
        (h.functional_comprehension n body o)
  | lawV => exact (lawV_truth M o f r).mpr h.lawV
  | coverage => exact (coverage_truth M o f r).mpr h.coverage
  | nontriviality => exact (nontriviality_truth M o f r).mpr h.nontrivial
  | evaluation => exact (evaluation_truth M o f r).mpr h.evaluation
  | k => exact (kLaw_truth M o f r).mpr h.combinatory.constant
  | s => exact (sLaw_truth M o f r).mpr h.combinatory.distribute

theorem conditions_of_functional_axioms (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, FunctionalAxiom p → Valid M p) : TFConditions M := by
  classical
  let o : Nat → D := fun _ => M.applicative.constantK
  let f : Nat → F := fun _ => Classical.choice (inferInstance : Nonempty F)
  let r : Positive.PredicateAssignment R := fun n _ => Classical.choice (inferInstance : Nonempty (R n))
  exact {
    comprehension := {
      relations_nonempty := fun n => inferInstance
      comprehend := fun n body os fs rs => (relationalComprehension_truth M n body os fs rs).mp
        (h _ (.relational n body) os fs rs) }
    functional_comprehension := fun n t os => (functionalComprehension_truth M n t os f r).mp
      (h _ (.functional n t) os f r)
    lawV := (lawV_truth M o f r).mp (h _ .lawV o f r)
    coverage := (coverage_truth M o f r).mp (h _ .coverage o f r)
    nontrivial := (nontriviality_truth M o f r).mp (h _ .nontriviality o f r)
    evaluation := (evaluation_truth M o f r).mp (h _ .evaluation o f r)
    combinatory := {
      constant := (kLaw_truth M o f r).mp (h _ .k o f r)
      distribute := (sLaw_truth M o f r).mp (h _ .s o f r) } }

theorem functional_axioms_iff_conditions (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, FunctionalAxiom p → Valid M p) ↔ TFConditions M :=
  ⟨conditions_of_functional_axioms M, functional_axioms_of_conditions M⟩

end FregeanECA.Axioms
