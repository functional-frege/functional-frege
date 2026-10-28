import FregeanECA.Part2.Closure
import FregeanECA.Concrete
import FregeanECA.Part2.AlgebraAxioms

/-!
A concrete generated relation expansion of an arbitrary ECA. This checks the
positive half of the proposed complement-only countermodel: B1--B5 and C
hold by evaluating finite relation expressions. It does NOT assert failure
of predicate projection or nondefinability of a truth/jump relation.
-/

namespace FregeanECA.Part2.Generated
open Frege
universe u

/-- A finite relation expression; n denotes positive arity n+1. Base
relations have natural-number names. Object coefficients in preimages are
actual computational objects, not arbitrary external maps. -/
inductive Relation (D : Type u) : Nat → Type u
  | base (arity name : Nat) : Relation D arity
  | equality : Relation D 1
  | preimage {source target : Nat} (relation : Relation D source)
      (programs : Fin (source + 1) → D) : Relation D target
  | intersection {arity : Nat} (left right : Relation D arity) : Relation D arity
  | union {arity : Nat} (left right : Relation D arity) : Relation D arity
  | complement {arity : Nat} (relation : Relation D arity) : Relation D arity
  | existsProjection {arity : Nat} (relation : Relation D (arity + 1)) : Relation D arity
  | forallProjection {arity : Nat} (relation : Relation D (arity + 1)) : Relation D arity

def Relation.truth {D : Type u} (A : CombinatoryAlgebra D)
    (base : ∀ n, Nat → (Fin (n + 1) → D) → Prop) :
    {arity : Nat} → Relation D arity → (Fin (arity + 1) → D) → Prop
  | _, .base arity name, xs => base arity name xs
  | _, .equality, xs => xs 0 = xs 1
  | _, .preimage relation programs, xs => relation.truth A base
      (fun i => Positive.applyArguments (fullRelations A) (programs i) xs)
  | _, .intersection left right, xs => left.truth A base xs ∧ right.truth A base xs
  | _, .union left right, xs => left.truth A base xs ∨ right.truth A base xs
  | _, .complement relation, xs => ¬ relation.truth A base xs
  | _, .existsProjection relation, xs => ∃ x, relation.truth A base (Positive.appendLast xs x)
  | _, .forallProjection relation, xs => ∀ x, relation.truth A base (Positive.appendLast xs x)

def interpretation {D : Type u} (A : CombinatoryAlgebra D)
    (base : ∀ n, Nat → (Fin (n + 1) → D) → Prop) :
    Positive.Interpretation D (Relation D) where
  apply := A.apply
  constantK := A.constant
  constantS := A.distribute
  satisfies := fun _ relation xs => relation.truth A base xs

theorem applyArguments_agrees {D : Type u} (A : CombinatoryAlgebra D)
    (base : ∀ n, Nat → (Fin (n + 1) → D) → Prop) (length : Nat)
    (code : D) (xs : Fin length → D) :
    Positive.applyArguments (interpretation A base) code xs =
      Positive.applyArguments (fullRelations A) code xs := by
  induction length generalizing code with
  | zero => rfl
  | succ n ih => exact ih (A.apply code (xs 0)) (fun i => xs i.succ)

theorem positive_closure {D : Type u} (A : CombinatoryAlgebra D)
    (base : ∀ n, Nat → (Fin (n + 1) → D) → Prop) :
    Positive.PositiveClosure (interpretation A base) where
  equality := ⟨.equality, fun _ => Iff.rfl⟩
  preimage := by
    intro source target relation programs
    refine ⟨.preimage relation programs, ?_⟩
    intro xs
    change relation.truth A base (fun i => Positive.applyArguments (fullRelations A) (programs i) xs) ↔
      relation.truth A base (fun i => Positive.applyArguments (interpretation A base) (programs i) xs)
    simp only [applyArguments_agrees]
  intersection := fun _ left right => ⟨.intersection left right, fun _ => Iff.rfl⟩
  union := fun _ left right => ⟨.union left right, fun _ => Iff.rfl⟩
  existsProjection := fun _ relation => ⟨.existsProjection relation, fun _ => Iff.rfl⟩
  forallProjection := fun _ relation => ⟨.forallProjection relation, fun _ => Iff.rfl⟩

theorem complemented {D : Type u} (A : CombinatoryAlgebra D)
    (base : ∀ n, Nat → (Fin (n + 1) → D) → Prop) :
    ComplementClosure (interpretation A base) where
  complement := fun _ relation => ⟨.complement relation, fun _ => Iff.rfl⟩

/-- No closure axiom is assumed: every witness is an explicit finite code. -/
theorem specification_with_complements {D : Type u} (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) (nontrivial : ∃ a b : D, a ≠ b)
    (base : ∀ n, Nat → (Fin (n + 1) → D) → Prop) :
    TSConditions (interpretation A base) ∧ ComplementClosure (interpretation A base) :=
  ⟨{combinatory := ⟨A.constant_returns_first_argument, A.distribute_applies_the_same_argument⟩
    extensional := ext
    nontrivial := nontrivial
    closure := positive_closure A base}, complemented A base⟩

/-- Concrete ECA seed, leaving the named base relation interpretation free
for the arithmetic/oracle interface. This is not yet a Q countermodel. -/
theorem open_specification_with_complements
    (base : ∀ n, Nat → (Fin (n + 1) → OpenObject) → Prop) :
    TSConditions (interpretation OpenLambda.algebra base) ∧
      ComplementClosure (interpretation OpenLambda.algebra base) :=
  specification_with_complements OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional open_nontrivial base

/-- The literal axiom schemes whose countermodel is sought: exactly the
original specification axioms and complementation, omitting Q. -/
inductive ComplementedAxiom : Functional.Formula → Prop where
  | original {p} (h : Axioms.SpecificationAxiom p) : ComplementedAxiom p
  | complement (n : Nat) : ComplementedAxiom (complementAxiom n)

theorem satisfies_literal_complemented_axioms {D : Type u}
    (A : CombinatoryAlgebra D) (ext : A.IsExtensional)
    (nontrivial : ∃ a b : D, a ≠ b)
    (base : ∀ n, Nat → (Fin (n + 1) → D) → Prop) :
    ∀ p, ComplementedAxiom p → Axioms.Valid (copyExpansion (interpretation A base)) p := by
  intro p axiomInstance
  cases axiomInstance with
  | original old =>
      exact Axioms.specification_axioms_of_conditions _
        (specification_with_complements A ext nontrivial base).1 p old
  | complement n =>
      intro objects functions predicates
      obtain ⟨q, qlaw⟩ := (complemented A base).complement n (predicates n 0)
      apply (shared_full_comprehension_truth (copyExpansion (interpretation A base))
        n (complementBody n) objects functions predicates).mpr
      exact ⟨q, fun xs => (qlaw xs).trans
        (complement_body_truth (interpretation A base) n xs objects predicates).symm⟩

/-- No existence premise. The unproved countermodel obligation is a further
actual Q instance falsified in a suitable choice of these base relations. -/
theorem open_satisfies_literal_complemented_axioms
    (base : ∀ n, Nat → (Fin (n + 1) → OpenObject) → Prop) :
    ∀ p, ComplementedAxiom p →
      Axioms.Valid (copyExpansion (interpretation OpenLambda.algebra base)) p :=
  satisfies_literal_complemented_axioms OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional open_nontrivial base

end FregeanECA.Part2.Generated
