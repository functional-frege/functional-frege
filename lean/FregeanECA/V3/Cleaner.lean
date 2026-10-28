import FregeanECA.Part2.FunctionExtensionality

/-!
The V3 A1--A5, with their actual closed first-order encoding.

The core schema A2 has only variables and application in its term grammar;
its vector length is any natural number, including zero. Remaining parameters
are universally closed by `Guarded.sentence`, outside the witness existential.
Application and named K/S are carried in the existing expanded language. Their
defining clauses are separated below from the five mathematical clauses.
-/
namespace FregeanECA.V3.Cleaner

open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2
open scoped FFL.FirstOrder

universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- Finite application terms, with neither functional graph comprehension nor
primitive combinators in the generating grammar. -/
inductive ApplicationTerm where
  | var (index : Nat)
  | app (function argument : ApplicationTerm)

def ApplicationTerm.positive : ApplicationTerm → Positive.Term
  | .var i => .var i
  | .app t s => .app t.positive s.positive

/-- A1: full relational comprehension. The inherited arity index n denotes
n+1 relation arguments; relation arities are positive. -/
abbrev A1 := fullRelationalComprehension

/-- A2: n is the actual vector length, and may be zero. -/
def A2 (n : Nat) (t : ApplicationTerm) : Formula :=
  .existsFunction (allObjects n
    (.equal (applyVariables n (.delta 0)) t.positive.functional))

/-- A3: abstractions identify exactly identical represented functions. -/
def A3 : Formula := allFunctions 2
  (iffF (.equal (.delta 0) (.delta 1)) (.functionEqual 0 1))

abbrev A4 := functionExtensionality
abbrev A5 := nontriviality

inductive CoreAxiom : Formula → Prop where
  | a1 (n : Nat) (p : Formula) : CoreAxiom (A1 n p)
  | a2 (n : Nat) (t : ApplicationTerm) : CoreAxiom (A2 n t)
  | a3 : CoreAxiom A3
  | a4 : CoreAxiom A4
  | a5 : CoreAxiom A5

/-- These fix the existing notation for application and the uniquely specified
combinators. They are not extra clauses numbered A6--A8. -/
inductive DefinitionAxiom : Formula → Prop where
  | evaluation : DefinitionAxiom evaluation
  | k : DefinitionAxiom kLaw
  | s : DefinitionAxiom sLaw

def Axiom (p : Formula) : Prop := CoreAxiom p ∨ DefinitionAxiom p
abbrev theory := Encoded.theory Axiom

theorem A2_truth (M : Interpretation D F R) (n : Nat) (t : ApplicationTerm)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (A2 n t).truth M o f r ↔
      ∃ g : F, ∀ xs : Fin n → D,
        Positive.applyArguments M.applicative (M.delta g) xs =
          t.positive.value M.applicative (Positive.assignTuple n xs o) := by
  change (∃ g, _) ↔ _
  apply exists_congr
  intro g
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  change (applyVariables n (.delta 0)).value M _ _ = t.positive.functional.value M _ _ ↔ _
  rw [applyVariables_value, applicativeTerm_value]
  simp [Term.value, Positive.pushObject]

theorem A3_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    A3.truth M o f r ↔ ∀ a b : F, M.delta a = M.delta b ↔ a = b := by
  constructor
  · intro h a b
    exact (iffF_truth M _ _ _ _ _).mp (h b a)
  · intro h b a
    exact (iffF_truth M _ _ _ _ _).mpr (h a b)

/-- The zero-input instance has a free object parameter. Universal closure of
that parameter, not any infinitary rule about named instances, yields coverage. -/
theorem coverage_from_zero (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : Valid M (A2 0 (.var 0))) : Valid M coverage := by
  classical
  intro o f r x
  exact h (fun _ => x) f r

/-- The inverse already follows from the application-free zero instance and
A3. Neither FE nor an application equation is used to obtain it. -/
theorem inverse_from_zero_and_A3 (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (zero : Valid M (A2 0 (.var 0))) (injective : Valid M A3) :
    ∃ inverse : D → F,
      (∀ f, inverse (M.delta f) = f) ∧ (∀ x, M.delta (inverse x) = x) := by
  classical
  let o : Nat → D := fun _ => M.applicative.constantK
  let f : Nat → F := fun _ => Classical.choice inferInstance
  let r : Positive.PredicateAssignment R := fun _ _ => Classical.choice inferInstance
  have onto := (coverage_truth M o f r).mp (coverage_from_zero M zero o f r)
  have inj := (A3_truth M o f r).mp (injective o f r)
  let inverse : D → F := fun x => Classical.choose (onto x)
  have right : ∀ x, M.delta (inverse x) = x := fun x => Classical.choose_spec (onto x)
  exact ⟨inverse, fun g => (inj _ _).mp (right (M.delta g)), right⟩

/-- Replacing named K/S by two additional object parameters keeps the grammar
of A2 precisely variable/application-only. -/
def abstractConstants (n : Nat) : Positive.Term → ApplicationTerm
  | .var i => .var (if i < n then i else i + 2)
  | .constantK => .var n
  | .constantS => .var (n + 1)
  | .app t s => .app (abstractConstants n t) (abstractConstants n s)

theorem abstractConstants_value (M : Positive.Interpretation D R) (n : Nat)
    (t : Positive.Term) (xs : Fin n → D) (o : Nat → D) :
    (abstractConstants n t).positive.value M
      (Positive.assignTuple n xs
        (Positive.pushObject (Positive.pushObject o M.constantS) M.constantK)) =
      t.value M (Positive.assignTuple n xs o) := by
  induction t with
  | var i =>
      simp only [abstractConstants, ApplicationTerm.positive, Positive.Term.value]
      split_ifs with hi
      · exact (Positive.assignTuple_at n xs _ ⟨i, hi⟩).trans
          (Positive.assignTuple_at n xs o ⟨i, hi⟩).symm
      · have he : i = n + (i - n) := (Nat.add_sub_of_le (Nat.le_of_not_gt hi)).symm
        rw [he]
        simp only [Nat.add_assoc, Positive.assignTuple_after]
        simp [Positive.pushObject]
  | constantK =>
      simpa [abstractConstants, ApplicationTerm.positive, Positive.Term.value,
        Positive.pushObject] using
        (Positive.assignTuple_after n xs
          (Positive.pushObject (Positive.pushObject o M.constantS) M.constantK) 0)
  | constantS =>
      simp [abstractConstants, ApplicationTerm.positive, Positive.Term.value,
        Positive.pushObject]
  | app t s ih₁ ih₂ =>
      simp only [abstractConstants, ApplicationTerm.positive, Positive.Term.value, ih₁, ih₂]

/-- Arbitrary finite terms with the subsequently named K/S are admissible
instances because A2 permits arbitrary object parameters. -/
theorem original_functional_from_A2 (M : Interpretation D F R)
    (h : ∀ n t, Valid M (A2 n t)) (n : Nat) (t : Positive.Term) :
    Valid M (functionalComprehension n t) := by
  intro o f r
  obtain ⟨g, hg⟩ := (A2_truth M (n+1) (abstractConstants (n+1) t) _ f r).mp
    (h (n+1) (abstractConstants (n+1) t)
      (Positive.pushObject (Positive.pushObject o M.applicative.constantS)
        M.applicative.constantK) f r)
  apply (functionalComprehension_truth M n t o f r).mpr
  exact ⟨g, fun xs => (hg xs).trans (abstractConstants_value M.applicative (n+1) t xs o)⟩

theorem A2_from_original (M : Interpretation D F R)
    (h : ∀ n t, Valid M (functionalComprehension n t))
    (cover : Valid M coverage) (n : Nat) (t : ApplicationTerm) : Valid M (A2 n t) := by
  cases n with
  | zero =>
      intro o f r
      obtain ⟨g, hg⟩ := cover o f r (t.positive.value M.applicative o)
      apply (A2_truth M 0 t o f r).mpr
      exact ⟨g, fun _ => hg⟩
  | succ n => exact h n t.positive

/-- The five core clauses recover the original raw conditions before K/S are
selected. The only accompanying equation is the definition of application. -/
theorem core_raw_conditions (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, CoreAxiom p → Valid M p) (ev : Valid M evaluation) : RawTFConditions M := by
  classical
  let o : Nat → D := fun _ => M.applicative.constantK
  let f : Nat → F := fun _ => Classical.choice inferInstance
  let r : Positive.PredicateAssignment R := fun _ _ => Classical.choice inferInstance
  have inj := (A3_truth M o f r).mp (h _ .a3 o f r)
  have ext := (functionExtensionality_truth M o f r).mp (h _ .a4 o f r)
  refine {
    comprehension := { relations_nonempty := fun _ => inferInstance, comprehend := ?_ }
    functional_comprehension := ?_
    lawV := ?_
    coverage := (coverage_truth M o f r).mp (coverage_from_zero M (h _ (.a2 0 (.var 0))) o f r)
    nontrivial := (nontriviality_truth M o f r).mp (h _ .a5 o f r)
    evaluation := (evaluation_truth M o f r).mp (ev o f r) }
  · intro n body os fs rs
    obtain ⟨P, hP⟩ := (fullRelationalComprehension_truth M n (embedPositive body) os fs rs).mp
      (h _ (.a1 n (embedPositive body)) os fs rs)
    exact ⟨P, fun xs => (hP xs).trans (embedPositive_truth M body _ _ _)⟩
  · intro n t os
    exact (functionalComprehension_truth M n t os f r).mp
      (original_functional_from_A2 M (fun n t => h _ (.a2 n t)) n t os f r)
  · intro a b
    refine ⟨?_, fun pointwise => congrArg M.delta (ext a b pointwise)⟩
    intro same
    have samef := (inj a b).mp same
    subst b
    exact fun _ => rfl

/-- K and S exist uniquely before their names are fixed by the defining
clauses. Their equations are consequences of the five core axioms. -/
theorem core_combinators_unique (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, CoreAxiom p → Valid M p) (ev : Valid M evaluation) :
    (∃! k : D, ∀ x y, M.applicative.apply (M.applicative.apply k x) y = x) ∧
    (∃! s : D, ∀ x y z,
      M.applicative.apply (M.applicative.apply (M.applicative.apply s x) y) z =
        M.applicative.apply (M.applicative.apply x z) (M.applicative.apply y z)) := by
  have raw := core_raw_conditions M h ev
  obtain ⟨⟨k, hk⟩, ⟨s, hs⟩⟩ := raw.combinators_exist
  constructor
  · refine ⟨k, hk, ?_⟩
    intro k' hk'
    exact (combinator_choices_are_unique raw hk' hk hs hs).1
  · refine ⟨s, hs, ?_⟩
    intro s' hs'
    exact (combinator_choices_are_unique raw hk hk hs' hs).2

/-- Equality of model classes, with the same defined application/K/S names.
Coverage is derived from A2's zero case and is never assumed in the V3 set. -/
theorem axioms_iff_fullFE (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)] :
    (∀ p, Axiom p → Valid M p) ↔
      (∀ p, FunctionExtensionality.FullFEAxiom p → Valid M p) := by
  classical
  constructor
  · intro h
    have hc : Valid M coverage := coverage_from_zero M (h _ (Or.inl (.a2 0 (.var 0))))
    have hf : ∀ n t, Valid M (functionalComprehension n t) :=
      original_functional_from_A2 M (fun n t => h _ (Or.inl (.a2 n t)))
    have hv : Valid M lawV := by
      intro o f r
      have inj := (A3_truth M o f r).mp (h _ (Or.inl .a3) o f r)
      have ext := (functionExtensionality_truth M o f r).mp (h _ (Or.inl .a4) o f r)
      apply (lawV_truth M o f r).mpr
      intro a b
      constructor
      · intro eqd
        have eqf := (inj a b).mp eqd
        subst b
        exact fun _ => rfl
      · intro pointwise
        exact congrArg M.delta (ext a b pointwise)
    have old : ∀ p, FunctionalAxiom p → Valid M p := by
      intro p hp
      cases hp with
      | relational n body =>
          intro o f r
          obtain ⟨P, hP⟩ := (fullRelationalComprehension_truth M n (embedPositive body) o f r).mp
            (h _ (Or.inl (.a1 n (embedPositive body))) o f r)
          exact (relationalComprehension_truth M n body o f r).mpr
            ⟨P, fun xs => (hP xs).trans (embedPositive_truth M body _ _ _)⟩
      | functional n t => exact hf n t
      | lawV => exact hv
      | coverage => exact hc
      | nontriviality => exact h _ (Or.inl .a5)
      | evaluation => exact h _ (Or.inr .evaluation)
      | k => exact h _ (Or.inr .k)
      | s => exact h _ (Or.inr .s)
    intro p hp
    rcases hp with hp | rfl
    · cases hp with
      | original hp => exact old p hp
      | comprehend n body => exact h _ (Or.inl (.a1 n body))
    · exact h _ (Or.inl .a4)
  · intro h p hp
    rcases hp with hp | hp
    · cases hp with
      | a1 n body => exact h _ (Or.inl (.comprehend n body))
      | a2 n t =>
          exact A2_from_original M
            (fun n t => h _ (Or.inl (.original (.functional n t))))
            (h _ (Or.inl (.original .coverage))) n t
      | a3 =>
          intro o f r
          have lv := (lawV_truth M o f r).mp (h _ (Or.inl (.original .lawV)) o f r)
          have ext := (functionExtensionality_truth M o f r).mp (h _ (Or.inr rfl) o f r)
          apply (A3_truth M o f r).mpr
          intro a b
          exact ⟨fun hab => ext a b ((lv a b).mp hab), congrArg M.delta⟩
      | a4 => exact h _ (Or.inr rfl)
      | a5 => exact h _ (Or.inl (.original .nontriviality))
    · cases hp with
      | evaluation => exact h _ (Or.inl (.original .evaluation))
      | k => exact h _ (Or.inl (.original .k))
      | s => exact h _ (Or.inl (.original .s))

/-- Every sentence of the actual common expanded first-order language has the
same derivability status, not merely translated shared-language sentences. -/
theorem provability_iff_fullFE (σ : Sentence language) :
    (theory ⊢ σ) ↔ (FunctionExtensionality.fullFETheory ⊢ σ) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    have := sorts_of_model h
    have native := (model_iff_valid (extractedRealization M)
      FunctionExtensionality.FullFEAxiom).mp h
    exact ⟨M↓[language], (model_iff_valid (extractedRealization M) Axiom).mpr
      ((axioms_iff_fullFE (extracted M)).mpr native), Iff.rfl⟩
  · intro M _ _ _ h
    have := sorts_of_model h
    have native := (model_iff_valid (extractedRealization M) Axiom).mp h
    exact ⟨M↓[language], (model_iff_valid (extractedRealization M)
      FunctionExtensionality.FullFEAxiom).mpr
      ((axioms_iff_fullFE (extracted M)).mp native), Iff.rfl⟩

/-- The actual first-order proof from one universally closed A2 instance.
No other mathematical axiom or definitional equation is a premise. -/
theorem zero_instance_proves_coverage :
    (Encoded.theory (fun p => p = A2 0 (.var 0))) ⊢ sentence coverage := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ hM
  have := sorts_of_model hM
  have native := (model_iff_valid (extractedRealization M)
    (fun p => p = A2 0 (.var 0))).mp hM
  apply (sentence_truth (extractedRealization M)
    inferInstance (fun _ => inferInstance) coverage).mpr
  exact coverage_from_zero (extracted M) (native _ rfl)

theorem coverage_provable : theory ⊢ sentence coverage := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ hM
  have := sorts_of_model hM
  have native := (model_iff_valid (extractedRealization M) Axiom).mp hM
  apply (sentence_truth (extractedRealization M)
    inferInstance (fun _ => inferInstance) coverage).mpr
  exact coverage_from_zero (extracted M) (native _ (Or.inl (.a2 0 (.var 0))))

theorem conditions (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, Axiom p → Valid M p) :
    FullTFConditions M ∧ Valid M functionExtensionality :=
  FunctionExtensionality.conditions_of_axioms M ((axioms_iff_fullFE M).mp h)

/-- The inverse is a cross-sort map D → F; application is evaluation after
this inverse. Both inverse laws and the application equation are explicit. -/
theorem inverse_application (M : Interpretation D F R)
    [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, Axiom p → Valid M p) :
    ∃ inverse : D → F,
      (∀ f, inverse (M.delta f) = f) ∧
      (∀ x, M.delta (inverse x) = x) ∧
      (∀ x y, M.applicative.apply x y = M.eval (inverse x) y) := by
  obtain ⟨full, fe⟩ := conditions M h
  obtain ⟨inverse, left, right, app⟩ :=
    actual_FE_supplies_function_sort_isomorphism full.toRawTFConditions fe
  exact ⟨inverse, left, right, fun x y => (app x y).symm⟩

end FregeanECA.V3.Cleaner

#print axioms FregeanECA.V3.Cleaner.provability_iff_fullFE
#print axioms FregeanECA.V3.Cleaner.coverage_from_zero
#print axioms FregeanECA.V3.Cleaner.zero_instance_proves_coverage
#print axioms FregeanECA.V3.Cleaner.inverse_application
