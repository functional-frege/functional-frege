import FregeanECA.Equivalence

namespace FregeanECA.Pure
universe u v w

/-- Exactly the object/app/K/S signature, without relation or function sorts. -/
structure Interpretation (D : Type u) where
  apply : D → D → D
  constantK : D
  constantS : D

abbrev Term := Positive.Term

def termValue {D : Type u} (M : Interpretation D) (objects : Nat → D) : Term → D
  | .var i => objects i
  | .constantK => M.constantK
  | .constantS => M.constantS
  | .app f x => M.apply (termValue M objects f) (termValue M objects x)

inductive Formula where
  | equal (left right : Term)
  | falsum
  | implies (left right : Formula)
  | conjunction (left right : Formula)
  | disjunction (left right : Formula)
  | existsObject (body : Formula)
  | forallObject (body : Formula)

def Formula.truth {D : Type u} (M : Interpretation D) (objects : Nat → D) : Formula → Prop
  | .equal left right => termValue M objects left = termValue M objects right
  | .falsum => False
  | .implies left right => left.truth M objects → right.truth M objects
  | .conjunction left right => left.truth M objects ∧ right.truth M objects
  | .disjunction left right => left.truth M objects ∨ right.truth M objects
  | .existsObject body => ∃ x, body.truth M (Positive.pushObject objects x)
  | .forallObject body => ∀ x, body.truth M (Positive.pushObject objects x)

def Formula.applicative : Formula → Applicative.Formula
  | .equal left right => .equal left right
  | .falsum => .falsum
  | .implies left right => .implies left.applicative right.applicative
  | .conjunction left right => .conjunction left.applicative right.applicative
  | .disjunction left right => .disjunction left.applicative right.applicative
  | .existsObject body => .existsObject body.applicative
  | .forallObject body => .forallObject body.applicative

def Formula.functional (formula : Formula) : Functional.Formula := formula.applicative.functional

structure ECAConditions {D : Type u} (M : Interpretation D) : Prop where
  constant : ∀ x y, M.apply (M.apply M.constantK x) y = x
  distribute : ∀ x y z, M.apply (M.apply (M.apply M.constantS x) y) z =
    M.apply (M.apply x z) (M.apply y z)
  extensional : ∀ a b, (∀ x, M.apply a x = M.apply b x) → a = b
  nontrivial : ∃ a b : D, a ≠ b

end FregeanECA.Pure

namespace FregeanECA
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

def Positive.Interpretation.pure (M : Positive.Interpretation D R) : Pure.Interpretation D where
  apply := M.apply
  constantK := M.constantK
  constantS := M.constantS

theorem pure_term_preserves_value (M : Positive.Interpretation D R)
    (objects : Nat → D) (term : Pure.Term) :
    Pure.termValue M.pure objects term = term.value M objects := by
  induction term with
  | var i => rfl
  | constantK => rfl
  | constantS => rfl
  | app f x hf hx =>
      change M.apply (Pure.termValue M.pure objects f) (Pure.termValue M.pure objects x) = _
      rw [hf, hx]
      rfl

theorem pure_applicative_embedding_preserves_truth (M : Positive.Interpretation D R)
    (formula : Pure.Formula) : ∀ objects predicates,
    formula.applicative.truth M objects predicates ↔ formula.truth M.pure objects := by
  induction formula with
  | equal left right =>
      intros
      simp only [Pure.Formula.applicative, Applicative.Formula.truth, Pure.Formula.truth,
        pure_term_preserves_value]
  | falsum => intros; exact Iff.rfl
  | implies left right hl hr => intros; exact imp_congr (hl _ _) (hr _ _)
  | conjunction left right hl hr => intros; exact and_congr (hl _ _) (hr _ _)
  | disjunction left right hl hr => intros; exact or_congr (hl _ _) (hr _ _)
  | existsObject body ih => intros; exact exists_congr (fun _ => ih _ _)
  | forallObject body ih => intros; exact forall_congr' (fun _ => ih _ _)

theorem pure_functional_embedding_preserves_truth (M : Functional.Interpretation D F R)
    (formula : Pure.Formula) (objects : Nat → D) (functions : Nat → F)
    (predicates : Positive.PredicateAssignment R) :
    formula.functional.truth M objects functions predicates ↔
      formula.truth M.applicative.pure objects :=
  (shared_formula_preserves_truth M formula.applicative objects functions predicates).trans
    (pure_applicative_embedding_preserves_truth M.applicative formula objects predicates)

/-- Changing arbitrary relation domains and function sorts cannot change the
truth of any pure classical formula when the underlying algebra is unchanged. -/
theorem pure_truth_preserved_between_expansions
    {F' : Type v} {R' : Nat → Type w}
    (M : Functional.Interpretation D F R) (N : Functional.Interpretation D F' R')
    (same : M.applicative.pure = N.applicative.pure) (formula : Pure.Formula)
    (objects : Nat → D) (functions : Nat → F) (otherFunctions : Nat → F')
    (predicates : Positive.PredicateAssignment R) (otherPredicates : Positive.PredicateAssignment R') :
    formula.functional.truth M objects functions predicates ↔
      formula.functional.truth N objects otherFunctions otherPredicates := by
  rw [pure_functional_embedding_preserves_truth, pure_functional_embedding_preserves_truth, same]

theorem TSConditions.eca {M : Positive.Interpretation D R} (h : TSConditions M) :
    Pure.ECAConditions M.pure :=
  ⟨h.combinatory.constant, h.combinatory.distribute, h.extensional, h.nontrivial⟩

end FregeanECA
