import FregeanECA.Part2.Models
import FregeanECA.AxiomsSpecification

/-! Actual full-comprehension formula schemas for Part II. This preserves the
Part I finite-term A2; only relational comprehension is strengthened. -/

namespace FregeanECA.Part2
open Functional Axioms
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- Capture-avoiding renaming of predicate variables in the entire functional
grammar, including primitive predicate identity and every classical connective. -/
def renameFullPredicates (m : Nat → Nat → Nat) : Formula → Formula
  | .equal a b => .equal a b
  | .relation arity index arguments => .relation arity (m arity index) arguments
  | .relationEqual arity left right => .relationEqual arity (m arity left) (m arity right)
  | .functionEqual left right => .functionEqual left right
  | .falsum => .falsum
  | .implies a b => .implies (renameFullPredicates m a) (renameFullPredicates m b)
  | .conjunction a b => .conjunction (renameFullPredicates m a) (renameFullPredicates m b)
  | .disjunction a b => .disjunction (renameFullPredicates m a) (renameFullPredicates m b)
  | .existsObject body => .existsObject (renameFullPredicates m body)
  | .forallObject body => .forallObject (renameFullPredicates m body)
  | .existsFunction body => .existsFunction (renameFullPredicates m body)
  | .forallFunction body => .forallFunction (renameFullPredicates m body)
  | .existsPredicate arity body =>
      .existsPredicate arity (renameFullPredicates (bindPredicateMap m arity) body)
  | .forallPredicate arity body =>
      .forallPredicate arity (renameFullPredicates (bindPredicateMap m arity) body)

theorem renameFullPredicates_truth (M : Interpretation D F R) (p : Formula) :
    ∀ m o f r, (renameFullPredicates m p).truth M o f r ↔
      p.truth M o f (fun a i => r a (m a i)) := by
  induction p with
  | equal _ _ => intros; exact Iff.rfl
  | relation _ _ _ => intros; exact Iff.rfl
  | relationEqual _ _ _ => intros; exact Iff.rfl
  | functionEqual _ _ => intros; exact Iff.rfl
  | falsum => intros; exact Iff.rfl
  | implies _ _ ih1 ih2 => intros; exact imp_congr (ih1 _ _ _ _) (ih2 _ _ _ _)
  | conjunction _ _ ih1 ih2 => intros; exact and_congr (ih1 _ _ _ _) (ih2 _ _ _ _)
  | disjunction _ _ ih1 ih2 => intros; exact or_congr (ih1 _ _ _ _) (ih2 _ _ _ _)
  | existsObject _ ih => intros; exact exists_congr (fun _ => ih _ _ _ _)
  | forallObject _ ih => intros; exact forall_congr' (fun _ => ih _ _ _ _)
  | existsFunction _ ih => intros; exact exists_congr (fun _ => ih _ _ _ _)
  | forallFunction _ ih => intros; exact forall_congr' (fun _ => ih _ _ _ _)
  | existsPredicate arity body ih =>
      intro m o f r
      apply exists_congr
      intro P
      exact (ih _ _ _ _).trans (by rw [predicateMap_under_binder])
  | forallPredicate arity body ih =>
      intro m o f r
      apply forall_congr'
      intro P
      exact (ih _ _ _ _).trans (by rw [predicateMap_under_binder])

theorem shiftFullPredicate_truth (M : Interpretation D F R) (p : Formula)
    (arity : Nat) (P : R arity) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    (renameFullPredicates (fun a i => if a = arity then i+1 else i) p).truth
      M o f (Positive.pushPredicate r arity P) ↔ p.truth M o f r := by
  rw [renameFullPredicates_truth]
  have h : (fun a i => Positive.pushPredicate r arity P a
      (if a = arity then i+1 else i)) = r := by
    funext a i
    by_cases same : a = arity
    · subst a; simp [Positive.pushPredicate]
    · simp [Positive.pushPredicate, same]
  rw [h]

/-- The witness predicate is fresh: all existing predicates of its arity are
shifted past its binder, including occurrences under nested predicate binders. -/
def fullRelationalComprehension (arity : Nat) (body : Formula) : Formula :=
  .existsPredicate arity (allObjects (arity + 1)
    (iffF (relationAtom arity 0)
      (renameFullPredicates
        (fun other index => if other = arity then index + 1 else index) body)))

theorem fullRelationalComprehension_truth (M : Interpretation D F R)
    (arity : Nat) (p : Formula) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    (fullRelationalComprehension arity p).truth M o f r ↔
      ∃ P : R arity, ∀ xs,
        M.applicative.satisfies arity P xs ↔
          p.truth M (Positive.assignTuple (arity+1) xs o) f r := by
  change (∃ P, _) ↔ _
  apply exists_congr
  intro P
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  rw [iffF_truth, shiftFullPredicate_truth]
  simp [relationAtom, Formula.truth, Term.value, Positive.pushPredicate]

/-- The original functional axioms, plus full classical A1 in their language. -/
inductive FullFunctionalAxiom : Formula → Prop where
  | original {p : Formula} : FunctionalAxiom p → FullFunctionalAxiom p
  | comprehend (arity : Nat) (body : Formula) :
      FullFunctionalAxiom (fullRelationalComprehension arity body)

/-- The original specification axioms, plus full classical comprehension in
the applicative language. The function sort in the host is unused here. -/
inductive FullRelationalAxiom : Formula → Prop where
  | original {p : Formula} : SpecificationAxiom p → FullRelationalAxiom p
  | comprehend (arity : Nat) (body : Applicative.Formula) :
      FullRelationalAxiom (fullRelationalComprehension arity body.functional)

theorem full_functional_axioms_of_conditions (M : Interpretation D F R)
    (h : FullTFConditions M) : ∀ p, FullFunctionalAxiom p → Valid M p := by
  intro p hp
  cases hp with
  | original old => exact functional_axioms_of_conditions M h.toTFConditions p old
  | comprehend arity body =>
      intro o f r
      exact (fullRelationalComprehension_truth M arity body o f r).mpr
        (h.full_comprehension.comprehend arity body o f r)

theorem conditions_of_full_functional_axioms (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, FullFunctionalAxiom p → Valid M p) : FullTFConditions M where
  toTFConditions := conditions_of_functional_axioms M (fun p old => h p (.original old))
  full_comprehension := {
    relations_nonempty := fun _ => inferInstance
    comprehend := fun n body os fs rs => (fullRelationalComprehension_truth M n body os fs rs).mp
      (h _ (.comprehend n body) os fs rs) }

theorem full_functional_axioms_iff_conditions (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, FullFunctionalAxiom p → Valid M p) ↔ FullTFConditions M :=
  ⟨conditions_of_full_functional_axioms M, full_functional_axioms_of_conditions M⟩

theorem full_relational_axioms_of_conditions (M : Interpretation D F R)
    (h : FullTSConditions M.applicative) : ∀ p, FullRelationalAxiom p → Valid M p := by
  intro p hp
  cases hp with
  | original old => exact specification_axioms_of_conditions M h.toTSConditions p old
  | comprehend arity body =>
      intro o f r
      obtain ⟨P, hP⟩ := h.full_comprehension.comprehend arity body o r
      apply (fullRelationalComprehension_truth M arity body.functional o f r).mpr
      exact ⟨P, fun xs => (hP xs).trans (shared_formula_preserves_truth M body _ _ _).symm⟩

theorem conditions_of_full_relational_axioms (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, FullRelationalAxiom p → Valid M p) : FullTSConditions M.applicative := by
  classical
  let f : Nat → F := fun _ => Classical.choice (inferInstance : Nonempty F)
  refine {
    toTSConditions := conditions_of_specification_axioms M (fun p old => h p (.original old))
    full_comprehension := { relations_nonempty := fun _ => inferInstance, comprehend := ?_ } }
  intro arity body o r
  obtain ⟨P, hP⟩ := (fullRelationalComprehension_truth M arity body.functional o f r).mp
    (h _ (.comprehend arity body) o f r)
  exact ⟨P, fun xs => (hP xs).trans (shared_formula_preserves_truth M body _ _ _)⟩

theorem full_relational_axioms_iff_conditions (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, FullRelationalAxiom p → Valid M p) ↔ FullTSConditions M.applicative :=
  ⟨conditions_of_full_relational_axioms M, full_relational_axioms_of_conditions M⟩

end FregeanECA.Part2
