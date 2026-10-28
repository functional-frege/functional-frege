import FregeanECA.Part2.FregeArithmeticAncestral

/-! The standard Frege theorem's Peano-axiom derivation from generic HP.
The difficult successor-existence argument uses the number of the available
predecessors-through-n concept. It follows the standard argument explained
in Heck, The Logic of Frege's Theorem, appendix, PDF pp.25--27.
No arithmetic domain, numerical enumeration, or prior Z2 theorem is assumed.
Addition/multiplication interpretation and encoded Z2 proof transfer remain
a separate interface step; the terminal record here states exactly what is proved. -/

namespace FregeanECA.Part2.FregeArithmetic
open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

def Downset (M : Interpretation D R) (n : D) (F : R 0) : Prop :=
  ∀ x, member M F x ↔ Ancestral M x n

theorem full_has_downset (M : Interpretation D R) (full : HasFullComprehension M) (n : D) :
    ∃ F : R 0, Downset M n F := by
  obtain ⟨A, ancestral⟩ := full_has_ancestral M full
  let predicates := pushPredicate (basePredicates M full) 1 A
  obtain ⟨F, law⟩ := full_represents_unary M full (binary 0 (.var 0) (.var 1))
    (fun _ => n) predicates
  refine ⟨F, ?_⟩
  intro x
  simpa [binary_truth, Term.value, predicates, pushPredicate, pushObject, ancestral] using law x

theorem downset_successor_deletion (M : Interpretation D R) (full : FullConditions M)
    {n s : D} (natural : Natural M full.comprehension n) (next : Precedes M n s) (x : D) :
    (Ancestral M x s ∧ x ≠ s) ↔ Ancestral M x n := by
  constructor
  · rintro ⟨xs, different⟩
    rcases (ancestral_rollback M full.comprehension x s).mp xs with same | ⟨y, xy, ys⟩
    · exact False.elim (different same.symm)
    · have same := predecession_injective M full ys next
      exact same ▸ xy
  · intro xn
    refine ⟨ancestral_step M xn next, ?_⟩
    intro same
    exact natural_no_back_edge M full n natural s next (same ▸ xn)

def SuccessorCandidate (M : Interpretation D R) (n : D) : Prop :=
  ∃ F : R 0, Downset M n F ∧ Precedes M n (M.number F)

def successorCandidateFormula : Formula :=
  .existsPredicate 0
    (.conjunction
      (.forallObject (iffFormula (unary 0 (.var 0)) (binary 0 (.var 0) (.var 1))))
      (binary 1 (.var 0) (.number 0)))

theorem successor_candidate_formula_truth (M : Interpretation D R)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R)
    (ancestral : ∀ x y, member2 M (predicates 1 0) x y ↔ Ancestral M x y)
    (precedes : ∀ x y, member2 M (predicates 1 1) x y ↔ Precedes M x y) :
    successorCandidateFormula.truth M objects predicates ↔ SuccessorCandidate M (objects 0) := by
  have iffTruth (o : ObjectAssignment D) (r : PredicateAssignment R) (p q : Formula) :
      (iffFormula p q).truth M o r ↔ (p.truth M o r ↔ q.truth M o r) :=
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩
  simp [successorCandidateFormula, Formula.truth, unary, binary_truth, iffTruth,
    Term.value, pushPredicate, pushObject, Downset, SuccessorCandidate, ancestral, precedes, member]

/-- The hard existence step of the standard proof: the next number is the
number of predecessors through the present number, including itself. -/
theorem natural_has_successor_candidate (M : Interpretation D R) (full : FullConditions M) :
    ∀ n, Natural M full.comprehension n → SuccessorCandidate M n := by
  obtain ⟨A, ancestral⟩ := full_has_ancestral M full.comprehension
  obtain ⟨P, precedes⟩ := full_has_predecession M full.comprehension
  let predicates := pushPredicate (pushPredicate (basePredicates M full.comprehension) 1 P) 1 A
  apply natural_formula_induction M full.comprehension successorCandidateFormula
    (baseObjects M full.comprehension) predicates (SuccessorCandidate M)
  · intro n
    exact successor_candidate_formula_truth M _ predicates ancestral precedes
  · obtain ⟨F, down⟩ := full_has_downset M full.comprehension (zero M full.comprehension)
    have fzero := (down _).mpr (ancestral_refl M _)
    obtain ⟨G, deletion, next⟩ := deletion_precedes M full.comprehension F _ fzero
    have empty : ∀ x, ¬ member M G x := by
      intro x gx
      obtain ⟨fx, different⟩ := (deletion x).mp gx
      exact different ((ancestral_to_zero M full x).mp ((down x).mp fx))
    have zeroEq := (number_zero_iff_empty M full G).mpr empty
    exact ⟨F, down, zeroEq ▸ next⟩
  · intro n s natural candidate next
    obtain ⟨F, downF, successorF⟩ := candidate
    have sNumberF := predecession_functional M full next successorF
    obtain ⟨H, downH⟩ := full_has_downset M full.comprehension s
    have hs := (downH s).mpr (ancestral_refl M s)
    obtain ⟨G, deletion, successorH⟩ := deletion_precedes M full.comprehension H s hs
    have sameConcepts : ∀ x, member M G x ↔ member M F x := by
      intro x
      exact (deletion x).trans ((and_congr (downH x) Iff.rfl).trans
        ((downset_successor_deletion M full natural next x).trans (downF x).symm))
    have numberG := (number_eq_of_coextension M full sameConcepts).trans sNumberF.symm
    exact ⟨H, downH, numberG ▸ successorH⟩

theorem natural_has_successor (M : Interpretation D R) (full : FullConditions M) :
    ∀ n, Natural M full.comprehension n → ∃ s, Precedes M n s := by
  intro n natural
  obtain ⟨F, _, next⟩ := natural_has_successor_candidate M full n natural
  exact ⟨M.number F, next⟩

/-- The seven second-order Peano laws in the standard relational presentation.
This record does not include a hidden arithmetic or model-existence premise. -/
structure FregePeanoLaws (M : Interpretation D R) (full : HasFullComprehension M) : Prop where
  zero_natural : Natural M full (zero M full)
  successor_closed : ∀ x y, Natural M full x → Precedes M x y → Natural M full y
  successor_unique : ∀ x y z, Natural M full x → Precedes M x y → Precedes M x z → y = z
  predecessor_unique : ∀ x y z, Natural M full x → Natural M full y →
    Precedes M x z → Precedes M y z → x = y
  zero_has_no_predecessor : ∀ x, Natural M full x → ¬ Precedes M x (zero M full)
  successor_exists : ∀ x, Natural M full x → ∃ y, Precedes M x y
  induction : ∀ (Q : R 0), member M Q (zero M full) →
    (∀ x y, Natural M full x → member M Q x → Precedes M x y → member M Q y) →
    ∀ x, Natural M full x → member M Q x

/-- Generic Frege arithmetic proves the relational second-order Peano laws.
The hypotheses are exactly HP and actual full source-language comprehension. -/
theorem hume_implies_frege_peano (M : Interpretation D R) (full : FullConditions M) :
    FregePeanoLaws M full.comprehension where
  zero_natural := natural_zero M full.comprehension
  successor_closed := fun _ _ => natural_successor M full.comprehension
  successor_unique := fun _ _ _ _ => predecession_functional M full
  predecessor_unique := fun _ _ _ _ _ => predecession_injective M full
  zero_has_no_predecessor := fun x _ => FregeArithmetic.zero_has_no_predecessor M full x
  successor_exists := natural_has_successor M full
  induction := natural_predicate_induction M full.comprehension

end FregeanECA.Part2.FregeArithmetic
