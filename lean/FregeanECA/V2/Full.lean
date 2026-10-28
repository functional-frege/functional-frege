import FregeanECA.V2.Positive
import FregeanECA.Part2.Correspondence

/-!
# Version 2: full relational algebra independently of computation

The positive algebra has syntactic term substitution as a primitive closure
operation. Adding complement and the existing impredicative predicate
projection is exactly full relational comprehension, with no K/S laws,
application extensionality, or nontriviality in that equivalence.

The final bridges preserve the existing Part II Fregean correspondence and its
models. This file proves semantic conditions; the separate V2 axiom module
connects them to the literal formal theory and proof certificates.
-/

namespace FregeanECA.V2
open Positive Part2
universe u v w
variable {D : Type u} {R : Nat → Type v}

/-- The full relational algebra: positive closure, complement, and predicate
projection. No computational equations are fields of this structure. -/
structure FCAlgebra (model : Interpretation D R) : Prop where
  positive : PCAlgebra model
  complemented : ComplementClosure model
  predicateProjection : PredicateProjection model

/-- A constant proposition is represented by the top or bottom relation.
This includes primitive equality of relation representatives. -/
theorem FCAlgebra.represents_constant {model : Interpretation D R}
    (algebra : FCAlgebra model) (arity : Nat) (p : Prop) :
    ∃ result : R arity, ∀ arguments, model.satisfies arity result arguments ↔ p := by
  classical
  obtain ⟨top, topLaw⟩ := pcAlgebra_supply_top model algebra.positive arity
  by_cases holds : p
  · exact ⟨top, fun arguments => ⟨fun _ => holds, fun _ => topLaw arguments⟩⟩
  · obtain ⟨bottom, bottomLaw⟩ := algebra.complemented.complement arity top
    exact ⟨bottom, fun arguments =>
      ⟨fun h => False.elim ((bottomLaw arguments).mp h (topLaw arguments)),
       fun h => False.elim (holds h)⟩⟩

/-- Structural induction handles every constructor of the complete classical
syntax. Term substitution and object projection need no combinatory laws. -/
theorem fcAlgebra_implies_fullComprehension (model : Interpretation D R)
    (algebra : FCAlgebra model) : HasFullComprehension model := by
  classical
  refine ⟨?_, ?_⟩
  · intro arity
    obtain ⟨top, _⟩ := pcAlgebra_supply_top model algebra.positive arity
    exact ⟨top⟩
  · intro arity formula
    induction formula generalizing arity with
    | equal left right =>
        intro parameters predicates
        obtain ⟨equality, equalityLaw⟩ := algebra.positive.equality
        let terms : Fin 2 → Term := Fin.cases left (fun _ => right)
        obtain ⟨result, resultLaw⟩ := algebra.positive.termPreimage
          1 arity equality terms parameters
        exact ⟨result, fun arguments => (resultLaw arguments).trans (equalityLaw _)⟩
    | relation source index terms =>
        intro parameters predicates
        exact algebra.positive.termPreimage source arity
          (predicates source index) terms parameters
    | relationEqual source left right =>
        intro parameters predicates
        exact algebra.represents_constant arity (predicates source left = predicates source right)
    | falsum =>
        intro parameters predicates
        exact algebra.represents_constant arity False
    | implies left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨notA, notALaw⟩ := algebra.complemented.complement arity a
        obtain ⟨result, resultLaw⟩ := algebra.positive.union arity notA b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, notALaw, aLaw, bLaw, Applicative.Formula.truth]
        by_cases h : left.truth model (assignTuple (arity + 1) arguments parameters) predicates
        · simp [h]
        · simp [h]
    | conjunction left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨result, resultLaw⟩ := algebra.positive.intersection arity a b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, aLaw, bLaw, Applicative.Formula.truth]
    | disjunction left right leftIH rightIH =>
        intro parameters predicates
        obtain ⟨a, aLaw⟩ := leftIH arity parameters predicates
        obtain ⟨b, bLaw⟩ := rightIH arity parameters predicates
        obtain ⟨result, resultLaw⟩ := algebra.positive.union arity a b
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, aLaw, bLaw, Applicative.Formula.truth]
    | existsObject body bodyIH =>
        intro parameters predicates
        obtain ⟨bodyRelation, bodyLaw⟩ := bodyIH (arity + 1) parameters predicates
        obtain ⟨result, resultLaw⟩ :=
          pcAlgebra_projects_first_exists model algebra.positive arity bodyRelation
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, bodyLaw, assignTuple_cons, Applicative.Formula.truth]
    | forallObject body bodyIH =>
        intro parameters predicates
        obtain ⟨bodyRelation, bodyLaw⟩ := bodyIH (arity + 1) parameters predicates
        obtain ⟨result, resultLaw⟩ :=
          pcAlgebra_projects_first_forall model algebra.positive arity bodyRelation
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, bodyLaw, assignTuple_cons, Applicative.Formula.truth]
    | existsPredicate source body bodyIH =>
        intro parameters predicates
        exact algebra.predicateProjection.project arity source body parameters predicates
          (fun predicate => bodyIH arity parameters (pushPredicate predicates source predicate))
    | forallPredicate source body bodyIH =>
        intro parameters predicates
        have sections : ∀ predicate : R source, ∃ slice : R arity, ∀ arguments,
            model.satisfies arity slice arguments ↔
              (Applicative.Formula.implies body .falsum).truth model
                (assignTuple (arity + 1) arguments parameters)
                (pushPredicate predicates source predicate) := by
          intro predicate
          obtain ⟨slice, sectionLaw⟩ :=
            bodyIH arity parameters (pushPredicate predicates source predicate)
          obtain ⟨negated, negatedLaw⟩ := algebra.complemented.complement arity slice
          exact ⟨negated, fun arguments => (negatedLaw arguments).trans
            (not_congr (sectionLaw arguments))⟩
        obtain ⟨counterexamples, counterexamplesLaw⟩ := algebra.predicateProjection.project
          arity source (.implies body .falsum) parameters predicates sections
        obtain ⟨result, resultLaw⟩ := algebra.complemented.complement arity counterexamples
        refine ⟨result, ?_⟩
        intro arguments
        simp only [resultLaw, counterexamplesLaw, Applicative.Formula.truth]
        constructor
        · intro none predicate
          apply Classical.byContradiction
          intro failure
          exact none ⟨predicate, failure⟩
        · rintro all ⟨predicate, failure⟩
          exact failure (all predicate)

/-- Each closure operation is a comprehension instance. The positive fragment
uses the independently proved Version 2 equivalence. -/
theorem fullComprehension_implies_fcAlgebra (model : Interpretation D R)
    (full : HasFullComprehension model) : FCAlgebra model where
  positive := (pcAlgebra_iff_positiveComprehension model).mpr
    (full_comprehension_implies_positive_comprehension model full)
  complemented := full_comprehension_implies_complement model full
  predicateProjection := full_comprehension_implies_predicate_projection model full

/-- Standalone full algebra/comprehension equivalence. The only background is
the declared applicative-relational interpretation; no ECA laws are assumed. -/
theorem fcAlgebra_iff_fullComprehension (model : Interpretation D R) :
    FCAlgebra model ↔ HasFullComprehension model :=
  ⟨fcAlgebra_implies_fullComprehension model,
    fullComprehension_implies_fcAlgebra model⟩

/-- With K/S available, the new algebra is equivalent to the original Part II
closure presentation. This bridge preserves all existing downstream proofs. -/
theorem fcAlgebra_iff_classicalClosure (model : Interpretation D R)
    (laws : CombinatoryLaws model) : FCAlgebra model ↔ ClassicalClosure model :=
  (fcAlgebra_iff_fullComprehension model).trans
    (classical_closure_iff_full_comprehension model laws).symm

/-- The existing Part II conditions are exactly nontrivial ECA plus the new
full relational algebra. There is no increase in strength over computation. -/
theorem fullTSConditions_iff (model : Interpretation D R) :
    FullTSConditions model ↔
      CombinatoryLaws model ∧
      (∀ a b, (∀ x, model.apply a x = model.apply b x) → a = b) ∧
      (∃ a b : D, a ≠ b) ∧ FCAlgebra model := by
  constructor
  · intro h
    exact ⟨h.combinatory, h.extensional, h.nontrivial,
      fullComprehension_implies_fcAlgebra model h.full_comprehension⟩
  · rintro ⟨laws, extensionality, nontriviality, algebra⟩
    have full := fcAlgebra_implies_fullComprehension model algebra
    exact {
      combinatory := laws
      extensional := extensionality
      nontrivial := nontriviality
      closure := (full_comprehension_implies_classical_closure model full).positive
      full_comprehension := full
    }

/-- A Part II Fregean model yields the new algebra on its shared reduct. -/
theorem fullTF_reduct_satisfies_fcAlgebra {F : Type w}
    {model : Functional.Interpretation D F R} [Nonempty F]
    (h : FullTFConditions model) : FCAlgebra model.applicative :=
  fullComprehension_implies_fcAlgebra model.applicative
    (full_tf_reduct_satisfies_full_ts h).full_comprehension

/-- Conversely, ECA plus the new algebra has the unchanged canonical
Fregean copy-function expansion, including full functional comprehension. -/
theorem fcAlgebra_eca_expansion_satisfies_fullTF (model : Interpretation D R)
    (laws : CombinatoryLaws model)
    (extensionality : ∀ a b, (∀ x, model.apply a x = model.apply b x) → a = b)
    (nontriviality : ∃ a b : D, a ≠ b) (algebra : FCAlgebra model) :
    FullTFConditions (copyExpansion model) :=
  full_ts_expansion_satisfies_full_tf
    ((fullTSConditions_iff model).mpr ⟨laws, extensionality, nontriviality, algebra⟩)

/-- The concrete open lambda model witnesses consistency of the new semantic
conditions without any model-existence premise. The V2 proof-theory module
uses the same witness for its syntactic consistency certificate. -/
theorem openSpecification_satisfies_fcAlgebra : FCAlgebra openSpecification :=
  fullComprehension_implies_fcAlgebra openSpecification
    openSpecification_satisfies_full_TS.full_comprehension

end FregeanECA.V2
