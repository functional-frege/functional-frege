import FregeanECA.AxiomsSpecification
import FregeanECA.Pure

namespace FregeanECA.Axioms
open Functional
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- The genuine four object-only first-order ECA axioms. -/
inductive ECAAxiom : Formula → Prop where
  | k : ECAAxiom kLaw
  | s : ECAAxiom sLaw
  | ext : ECAAxiom extensionality
  | nontrivial : ECAAxiom nontriviality

/-- ECA plus exactly the applicative strict-positive comprehension scheme. -/
inductive RelationalAxiom : Formula → Prop where
  | eca {p : Formula} : ECAAxiom p → RelationalAxiom p
  | comprehend (arity : Nat) (body : Positive.Formula) :
      RelationalAxiom (relationalComprehension arity body.functional)

theorem eca_axioms_of_conditions (M : Interpretation D F R)
    (h : Pure.ECAConditions M.applicative.pure) : ∀ p, ECAAxiom p → Valid M p := by
  intro p hp o f r
  cases hp with
  | k => exact (kLaw_truth M o f r).mpr h.constant
  | s => exact (sLaw_truth M o f r).mpr h.distribute
  | ext => exact (extensionality_truth M o f r).mpr h.extensional
  | nontrivial => exact (nontriviality_truth M o f r).mpr h.nontrivial

theorem conditions_of_eca_axioms (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, ECAAxiom p → Valid M p) : Pure.ECAConditions M.applicative.pure := by
  classical
  let o : Nat → D := fun _ => M.applicative.constantK
  let f : Nat → F := fun _ => Classical.choice (inferInstance : Nonempty F)
  let r : Positive.PredicateAssignment R := fun n _ => Classical.choice (inferInstance : Nonempty (R n))
  exact ⟨(kLaw_truth M o f r).mp (h _ .k o f r),
    (sLaw_truth M o f r).mp (h _ .s o f r),
    (extensionality_truth M o f r).mp (h _ .ext o f r),
    (nontriviality_truth M o f r).mp (h _ .nontrivial o f r)⟩

theorem eca_axioms_iff_conditions (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, ECAAxiom p → Valid M p) ↔ Pure.ECAConditions M.applicative.pure :=
  ⟨conditions_of_eca_axioms M, eca_axioms_of_conditions M⟩

theorem relational_axioms_of_conditions (M : Interpretation D F R)
    (h : TSConditions M.applicative) : ∀ p, RelationalAxiom p → Valid M p := by
  intro p hp
  cases hp with
  | eca algebraAxiom => exact eca_axioms_of_conditions M h.eca _ algebraAxiom
  | comprehend arity body =>
      intro o f r
      have pc := Positive.positive_closure_implies_comprehension M.applicative
        h.combinatory h.nontrivial h.closure
      obtain ⟨P, hP⟩ := pc.comprehend arity body o r
      apply (relationalComprehension_truth M arity body.functional o f r).mpr
      refine ⟨P, ?_⟩
      intro xs
      exact (hP xs).trans (shared_positive_preserves_truth M body _ _ _).symm

theorem conditions_of_relational_axioms (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, RelationalAxiom p → Valid M p) : TSConditions M.applicative := by
  classical
  have eca := conditions_of_eca_axioms M (fun p hp => h p (.eca hp))
  let f : Nat → F := fun _ => Classical.choice (inferInstance : Nonempty F)
  have pc : Positive.HasPositiveComprehension M.applicative := {
    relations_nonempty := fun _ => inferInstance
    comprehend := by
      intro arity body o r
      obtain ⟨P, hP⟩ := (relationalComprehension_truth M arity body.functional o f r).mp
        (h _ (.comprehend arity body) o f r)
      refine ⟨P, ?_⟩
      intro xs
      exact (hP xs).trans (shared_positive_preserves_truth M body _ _ _) }
  exact {
    combinatory := ⟨eca.constant, eca.distribute⟩
    extensional := eca.extensional
    nontrivial := eca.nontrivial
    closure := Positive.positive_comprehension_implies_closure M.applicative pc }

/-- The ECA+PC presentation has exactly the same models as ECA+B1--B5,
proved for the actual formula schemes over arbitrary nonempty Henkin sorts. -/
theorem relational_axioms_iff_conditions (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, RelationalAxiom p → Valid M p) ↔ TSConditions M.applicative :=
  ⟨conditions_of_relational_axioms M, relational_axioms_of_conditions M⟩

theorem specification_and_relational_axioms_same_models (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, SpecificationAxiom p → Valid M p) ↔ (∀ p, RelationalAxiom p → Valid M p) :=
  (specification_axioms_iff_conditions M).trans (relational_axioms_iff_conditions M).symm

end FregeanECA.Axioms
