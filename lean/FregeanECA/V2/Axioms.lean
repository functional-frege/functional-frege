import FregeanECA.V2.Full
import FregeanECA.AxiomsRelational
import FregeanECA.Part2.AlgebraAxioms

/-! Literal v2 relation-algebra axioms. The replacement B3 is an atomic
term-substitution scheme, not an alias for positive comprehension. -/
namespace FregeanECA.V2
open Axioms
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- B3*: substitute a tuple of finite terms, retaining object parameters. -/
def termSubstitution (source target : Nat)
    (terms : Fin (source + 1) → Positive.Term) : Functional.Formula :=
  relationalComprehension target
    (.relation source 0 (fun i => (terms i).functional))

/-- The standalone positive relation algebra, with no ECA axioms. -/
inductive PCAxiom : Functional.Formula → Prop where
  | equality : PCAxiom equalityRelation
  | intersection (n) : PCAxiom (Axioms.intersection n)
  | union (n) : PCAxiom (Axioms.union n)
  | substitution (m n) (terms : Fin (m + 1) → Positive.Term) :
      PCAxiom (termSubstitution m n terms)
  | existsProjection (n) : PCAxiom (Axioms.existsProjection n)
  | forallProjection (n) : PCAxiom (Axioms.forallProjection n)

/-- Strict-positive comprehension alone in the same applicative language. -/
inductive PCComprehensionAxiom : Functional.Formula → Prop where
  | comprehend (n) (body : Positive.Formula) :
      PCComprehensionAxiom (relationalComprehension n body.functional)

/-- Full relation algebra: the literal positive algebra plus C and Q. -/
inductive FCAxiom : Functional.Formula → Prop where
  | positive {p} : PCAxiom p → FCAxiom p
  | complement (n) : FCAxiom (Part2.complementAxiom n)
  | projection (n m) (body : Applicative.Formula) :
      FCAxiom (Part2.predicateProjectionAxiom n m body)

/-- Full comprehension alone; the unused function sort adds no proper axioms. -/
inductive FCComprehensionAxiom : Functional.Formula → Prop where
  | comprehend (n) (body : Applicative.Formula) :
      FCComprehensionAxiom (Part2.fullRelationalComprehension n body.functional)

/-- ECA is added separately to either relation algebra. -/
inductive WithECA (extra : Functional.Formula → Prop) : Functional.Formula → Prop where
  | eca {p} : ECAAxiom p → WithECA extra p
  | extra {p} : extra p → WithECA extra p

theorem termSubstitution_truth (M : Functional.Interpretation D F R)
    (source target : Nat) (terms : Fin (source + 1) → Positive.Term)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (termSubstitution source target terms).truth M o f r ↔
      ∃ P : R target, ∀ xs, M.applicative.satisfies target P xs ↔
        M.applicative.satisfies source (r source 0)
          (fun i => (terms i).value M.applicative
            (Positive.assignTuple (target + 1) xs o)) := by
  rw [termSubstitution, relationalComprehension_truth]
  simp only [Functional.PositiveFormula.truth, applicativeTerm_value]

theorem pc_axioms_of_conditions (M : Functional.Interpretation D F R)
    (h : PCAlgebra M.applicative) : ∀ p, PCAxiom p → Valid M p := by
  intro p hp o f r
  cases hp with
  | equality => exact (equalityRelation_truth M o f r).mpr h.equality
  | intersection n =>
    exact (intersection_truth M n o f r).mpr (h.intersection n (r n 0) (r n 1))
  | union n => exact (union_truth M n o f r).mpr (h.union n (r n 0) (r n 1))
  | substitution m n terms =>
    exact (termSubstitution_truth M m n terms o f r).mpr
      (h.termPreimage m n (r m 0) terms o)
  | existsProjection n =>
    exact (existsProjection_truth M n o f r).mpr (h.existsProjection n (r (n + 1) 0))
  | forallProjection n =>
    exact (forallProjection_truth M n o f r).mpr (h.forallProjection n (r (n + 1) 0))

theorem conditions_of_pc_axioms (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, PCAxiom p → Valid M p) : PCAlgebra M.applicative := by
  classical
  let o : Nat → D := fun _ => M.applicative.constantK
  let f : Nat → F := fun _ => Classical.choice inferInstance
  let r : Positive.PredicateAssignment R := fun _ _ => Classical.choice inferInstance
  refine {
    equality := (equalityRelation_truth M o f r).mp (h _ .equality o f r)
    termPreimage := ?_
    intersection := ?_
    union := ?_
    existsProjection := ?_
    forallProjection := ?_ }
  · intro source target relation terms parameters
    let predicates := Positive.pushPredicate r source relation
    have ht := (termSubstitution_truth M source target terms parameters f predicates).mp
      (h _ (.substitution source target terms) parameters f predicates)
    simpa [predicates, Positive.pushPredicate] using ht
  · intro arity left right
    let predicates := Positive.pushPredicate (Positive.pushPredicate r arity right) arity left
    have ht := (intersection_truth M arity o f predicates).mp
      (h _ (.intersection arity) o f predicates)
    simpa [predicates, Positive.pushPredicate] using ht
  · intro arity left right
    let predicates := Positive.pushPredicate (Positive.pushPredicate r arity right) arity left
    have ht := (union_truth M arity o f predicates).mp
      (h _ (.union arity) o f predicates)
    simpa [predicates, Positive.pushPredicate] using ht
  · intro arity relation
    let predicates := Positive.pushPredicate r (arity + 1) relation
    have ht := (existsProjection_truth M arity o f predicates).mp
      (h _ (.existsProjection arity) o f predicates)
    simpa [predicates, Positive.pushPredicate] using ht
  · intro arity relation
    let predicates := Positive.pushPredicate r (arity + 1) relation
    have ht := (forallProjection_truth M arity o f predicates).mp
      (h _ (.forallProjection arity) o f predicates)
    simpa [predicates, Positive.pushPredicate] using ht

theorem pc_axioms_iff_conditions (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, PCAxiom p → Valid M p) ↔ PCAlgebra M.applicative :=
  ⟨conditions_of_pc_axioms M, pc_axioms_of_conditions M⟩

theorem pc_comprehension_axioms_iff (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, PCComprehensionAxiom p → Valid M p) ↔
      Positive.HasPositiveComprehension M.applicative := by
  classical
  constructor
  · intro h
    let f : Nat → F := fun _ => Classical.choice inferInstance
    refine ⟨fun _ => inferInstance, ?_⟩
    intro n body o r
    obtain ⟨P, law⟩ := (relationalComprehension_truth M n body.functional o f r).mp
      (h _ (.comprehend n body) o f r)
    exact ⟨P, fun xs => (law xs).trans (shared_positive_preserves_truth M body _ _ _)⟩
  · intro h p hp o f r
    cases hp with
    | comprehend n body =>
      obtain ⟨P, law⟩ := h.comprehend n body o r
      exact (relationalComprehension_truth M n body.functional o f r).mpr
        ⟨P, fun xs => (law xs).trans (shared_positive_preserves_truth M body _ _ _).symm⟩

theorem fc_axioms_of_conditions (M : Functional.Interpretation D F R)
    (h : FCAlgebra M.applicative) : ∀ p, FCAxiom p → Valid M p := by
  have full := (fcAlgebra_iff_fullComprehension M.applicative).mp h
  intro p hp o f r
  cases hp with
  | positive old => exact pc_axioms_of_conditions M h.positive p old o f r
  | complement n =>
    exact (Part2.shared_full_comprehension_truth M n (Part2.complementBody n) o f r).mpr
      (full.comprehend n (Part2.complementBody n) o r)
  | projection n m body =>
    intro _
    exact (Part2.shared_full_comprehension_truth M n (.existsPredicate m body) o f r).mpr
      (full.comprehend n (.existsPredicate m body) o r)

theorem conditions_of_fc_axioms (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, FCAxiom p → Valid M p) : FCAlgebra M.applicative := by
  classical
  let f : Nat → F := fun _ => Classical.choice inferInstance
  let rs : Positive.PredicateAssignment R := fun _ _ => Classical.choice inferInstance
  let os : Nat → D := fun _ => M.applicative.constantK
  refine {
    positive := conditions_of_pc_axioms M (fun p hp => h p (.positive hp))
    complemented := ⟨?_⟩
    predicateProjection := ⟨?_⟩ }
  · intro n p
    let r := Positive.pushPredicate rs n p
    obtain ⟨q, law⟩ :=
      (Part2.shared_full_comprehension_truth M n (Part2.complementBody n) os f r).mp
        (h _ (.complement n) os f r)
    refine ⟨q, ?_⟩
    intro xs
    simpa only [r, Positive.pushPredicate, dite_true] using
      (law xs).trans (Part2.complement_body_truth M.applicative n xs os r)
  · intro n m body o r sections
    have project := h _ (.projection n m body) o f r
    apply (Part2.shared_full_comprehension_truth M n (.existsPredicate m body) o f r).mp
    apply project
    intro p
    exact (Part2.shared_full_comprehension_truth M n body o f
      (Positive.pushPredicate r m p)).mpr (sections p)

theorem fc_axioms_iff_conditions (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, FCAxiom p → Valid M p) ↔ FCAlgebra M.applicative :=
  ⟨conditions_of_fc_axioms M, fc_axioms_of_conditions M⟩

theorem fc_comprehension_axioms_iff (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, FCComprehensionAxiom p → Valid M p) ↔
      Part2.HasFullComprehension M.applicative := by
  classical
  constructor
  · intro h
    let f : Nat → F := fun _ => Classical.choice inferInstance
    refine ⟨fun _ => inferInstance, ?_⟩
    intro n body o r
    exact (Part2.shared_full_comprehension_truth M n body o f r).mp
      (h _ (.comprehend n body) o f r)
  · intro h p hp o f r
    cases hp with
    | comprehend n body =>
      exact (Part2.shared_full_comprehension_truth M n body o f r).mpr
        (h.comprehend n body o r)

theorem withECA_valid_iff (M : Functional.Interpretation D F R)
    (extra : Functional.Formula → Prop) :
    (∀ p, WithECA extra p → Valid M p) ↔
      (∀ p, ECAAxiom p → Valid M p) ∧ (∀ p, extra p → Valid M p) := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (.eca hp), fun p hp => h p (.extra hp)⟩
  · rintro ⟨eca, more⟩ p hp
    cases hp with
    | eca h => exact eca p h
    | extra h => exact more p h

theorem combined_pc_axioms_iff (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, WithECA PCAxiom p → Valid M p) ↔ TSConditions M.applicative := by
  rw [withECA_valid_iff, eca_axioms_iff_conditions, pc_axioms_iff_conditions]
  constructor
  · rintro ⟨eca, pc⟩
    exact {
      combinatory := ⟨eca.constant, eca.distribute⟩
      extensional := eca.extensional
      nontrivial := eca.nontrivial
      closure := (pcAlgebra_iff_positiveClosure M.applicative
        ⟨eca.constant, eca.distribute⟩).mp pc }
  · intro ts
    exact ⟨ts.eca, (pcAlgebra_iff_positiveClosure M.applicative ts.combinatory).mpr ts.closure⟩

theorem combined_fc_axioms_iff (M : Functional.Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, WithECA FCAxiom p → Valid M p) ↔ Part2.FullTSConditions M.applicative := by
  rw [withECA_valid_iff, eca_axioms_iff_conditions, fc_axioms_iff_conditions]
  constructor
  · rintro ⟨eca, fc⟩
    have full := (fcAlgebra_iff_fullComprehension M.applicative).mp fc
    exact {
      combinatory := ⟨eca.constant, eca.distribute⟩
      extensional := eca.extensional
      nontrivial := eca.nontrivial
      closure := Positive.positive_comprehension_implies_closure M.applicative
        (Part2.full_comprehension_implies_positive_comprehension M.applicative full)
      full_comprehension := full }
  · intro ts
    exact ⟨ts.toTSConditions.eca,
      (fcAlgebra_iff_fullComprehension M.applicative).mpr ts.full_comprehension⟩

end FregeanECA.V2
