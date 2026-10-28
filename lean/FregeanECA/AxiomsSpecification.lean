import FregeanECA.AxiomsFunctional

namespace FregeanECA.Axioms
open Functional
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

theorem extensionality_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) : extensionality.truth M o f r ↔
    ∀ a b, (∀ x, M.applicative.apply a x = M.applicative.apply b x) → a = b := by
  change (∀ b a, (∀ x, M.applicative.apply a x = M.applicative.apply b x) → a = b) ↔ _
  exact ⟨fun h a b => h b a, fun h b a => h a b⟩

theorem equalityRelation_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) : equalityRelation.truth M o f r ↔
    ∃ P : R 1, ∀ xs, M.applicative.satisfies 1 P xs ↔ xs 0 = xs 1 := by
  change (∃ P, _) ↔ _
  apply exists_congr
  intro P
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  rw [iffF_truth]
  have h0 : Positive.assignTuple 2 xs o 0 = xs 0 := Positive.assignTuple_at 2 xs o (0 : Fin 2)
  have h1 : Positive.assignTuple 2 xs o 1 = xs 1 := Positive.assignTuple_at 2 xs o (1 : Fin 2)
  simp [relationAtom, Formula.truth, Term.value, Positive.pushPredicate, h0, h1]

theorem intersection_truth (M : Interpretation D F R) (arity : Nat)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (intersection arity).truth M o f r ↔
    ∃ P : R arity, ∀ xs, M.applicative.satisfies arity P xs ↔
      M.applicative.satisfies arity (r arity 0) xs ∧ M.applicative.satisfies arity (r arity 1) xs := by
  change (∃ P, _) ↔ _
  apply exists_congr
  intro P
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  rw [iffF_truth]
  simp [relationAtom, Formula.truth, Term.value, Positive.pushPredicate]

theorem union_truth (M : Interpretation D F R) (arity : Nat)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (union arity).truth M o f r ↔
    ∃ P : R arity, ∀ xs, M.applicative.satisfies arity P xs ↔
      M.applicative.satisfies arity (r arity 0) xs ∨ M.applicative.satisfies arity (r arity 1) xs := by
  change (∃ P, _) ↔ _
  apply exists_congr
  intro P
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  rw [iffF_truth]
  simp [relationAtom, Formula.truth, Term.value, Positive.pushPredicate]

theorem preimage_truth (M : Interpretation D F R) (source target : Nat)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (preimage source target).truth M o f r ↔
    ∃ P : R target, ∀ xs, M.applicative.satisfies target P xs ↔
      M.applicative.satisfies source (r source 0)
        (fun i : Fin (source+1) => Positive.applyArguments M.applicative (o i) xs) := by
  change (∃ P, _) ↔ _
  apply exists_congr
  intro P
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  rw [iffF_truth]
  have sourceP : Positive.pushPredicate r target P source (if source = target then 1 else 0) = r source 0 := by
    by_cases h : source = target
    · subst source; simp [Positive.pushPredicate]
    · simp [Positive.pushPredicate, h]
  simp only [relationAtom, Formula.truth, Term.value, applyVariables_value,
    Positive.assignTuple_at, Positive.assignTuple_after, sourceP]
  simp [Positive.pushPredicate]

theorem projection_arguments_value (M : Interpretation D F R) (arity : Nat)
    (xs : Fin (arity+1) → D) (value : D) (o : Nat → D) (f : Nat → F) :
    (fun i : Fin (arity+1+1) => (Fin.lastCases (motive := fun _ => Term)
      (Term.var 0) (fun j => Term.var (j.val+1)) i).value M
      (Positive.pushObject (Positive.assignTuple (arity+1) xs o) value) f) =
      Positive.appendLast xs value := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Term.value, Positive.pushObject]
  · simp [Term.value, Positive.pushObject]

theorem existsProjection_truth (M : Interpretation D F R) (arity : Nat)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (existsProjection arity).truth M o f r ↔
    ∃ P : R arity, ∀ xs, M.applicative.satisfies arity P xs ↔
      ∃ value, M.applicative.satisfies (arity+1) (r (arity+1) 0) (Positive.appendLast xs value) := by
  change (∃ P, _) ↔ _
  apply exists_congr
  intro P
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  rw [iffF_truth]
  simp only [relationAtom, Formula.truth, Term.value, Positive.pushPredicate, dite_true,
    Positive.assignTuple_at]
  simp only [Nat.add_one_ne_self, dite_false, projection_arguments_value]

theorem forallProjection_truth (M : Interpretation D F R) (arity : Nat)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (forallProjection arity).truth M o f r ↔
    ∃ P : R arity, ∀ xs, M.applicative.satisfies arity P xs ↔
      ∀ value, M.applicative.satisfies (arity+1) (r (arity+1) 0) (Positive.appendLast xs value) := by
  change (∃ P, _) ↔ _
  apply exists_congr
  intro P
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  rw [iffF_truth]
  simp only [relationAtom, Formula.truth, Term.value, Positive.pushPredicate, dite_true,
    Positive.assignTuple_at]
  simp only [Nat.add_one_ne_self, dite_false, projection_arguments_value]

theorem specification_axioms_of_conditions (M : Interpretation D F R)
    (h : TSConditions M.applicative) : ∀ p, SpecificationAxiom p → Valid M p := by
  intro p hp o f r
  cases hp with
  | k => exact (kLaw_truth M o f r).mpr h.combinatory.constant
  | s => exact (sLaw_truth M o f r).mpr h.combinatory.distribute
  | ext => exact (extensionality_truth M o f r).mpr h.extensional
  | nontrivial => exact (nontriviality_truth M o f r).mpr h.nontrivial
  | equality => exact (equalityRelation_truth M o f r).mpr h.closure.equality
  | intersection n =>
      exact (intersection_truth M n o f r).mpr (h.closure.intersection n (r n 0) (r n 1))
  | union n => exact (union_truth M n o f r).mpr (h.closure.union n (r n 0) (r n 1))
  | preimage source target =>
      exact (preimage_truth M source target o f r).mpr
        (h.closure.preimage source target (r source 0) (fun i => o i))
  | existsProjection n =>
      exact (existsProjection_truth M n o f r).mpr (h.closure.existsProjection n (r (n+1) 0))
  | forallProjection n =>
      exact (forallProjection_truth M n o f r).mpr (h.closure.forallProjection n (r (n+1) 0))

theorem conditions_of_specification_axioms (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, SpecificationAxiom p → Valid M p) : TSConditions M.applicative := by
  classical
  let o : Nat → D := fun _ => M.applicative.constantK
  let f : Nat → F := fun _ => Classical.choice (inferInstance : Nonempty F)
  let r : Positive.PredicateAssignment R := fun n _ => Classical.choice (inferInstance : Nonempty (R n))
  refine {
    combinatory := ⟨(kLaw_truth M o f r).mp (h _ .k o f r),
      (sLaw_truth M o f r).mp (h _ .s o f r)⟩
    extensional := (extensionality_truth M o f r).mp (h _ .ext o f r)
    nontrivial := (nontriviality_truth M o f r).mp (h _ .nontrivial o f r)
    closure := {
      equality := (equalityRelation_truth M o f r).mp (h _ .equality o f r)
      intersection := ?_
      union := ?_
      preimage := ?_
      existsProjection := ?_
      forallProjection := ?_ } }
  · intro source target relation programs
    let predicates := Positive.pushPredicate r source relation
    let objects := Positive.assignTuple (source+1) programs o
    have instanceTruth := (preimage_truth M source target objects f predicates).mp
      (h _ (.preimage source target) objects f predicates)
    simpa [predicates, objects, Positive.pushPredicate] using instanceTruth
  · intro arity left right
    let predicates := Positive.pushPredicate (Positive.pushPredicate r arity right) arity left
    have instanceTruth := (intersection_truth M arity o f predicates).mp
      (h _ (.intersection arity) o f predicates)
    simpa [predicates, Positive.pushPredicate] using instanceTruth
  · intro arity left right
    let predicates := Positive.pushPredicate (Positive.pushPredicate r arity right) arity left
    have instanceTruth := (union_truth M arity o f predicates).mp
      (h _ (.union arity) o f predicates)
    simpa [predicates, Positive.pushPredicate] using instanceTruth
  · intro arity relation
    let predicates := Positive.pushPredicate r (arity+1) relation
    have instanceTruth := (existsProjection_truth M arity o f predicates).mp
      (h _ (.existsProjection arity) o f predicates)
    simpa [predicates, Positive.pushPredicate] using instanceTruth
  · intro arity relation
    let predicates := Positive.pushPredicate r (arity+1) relation
    have instanceTruth := (forallProjection_truth M arity o f predicates).mp
      (h _ (.forallProjection arity) o f predicates)
    simpa [predicates, Positive.pushPredicate] using instanceTruth

/-- Exact truth of the syntactically declared ECA+B1--B5 axiom schemes is
equivalent to the semantic conditions used in the model correspondence. -/
theorem specification_axioms_iff_conditions (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, SpecificationAxiom p → Valid M p) ↔ TSConditions M.applicative :=
  ⟨conditions_of_specification_axioms M, specification_axioms_of_conditions M⟩

end FregeanECA.Axioms
