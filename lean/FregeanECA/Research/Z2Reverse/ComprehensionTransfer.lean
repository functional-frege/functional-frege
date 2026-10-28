import FregeanECA.Research.Z2Reverse.FormulaTranslation
import Mathlib.Data.Nat.Pairing

/-! Source full comprehension supplies every target comprehension instance.
The only coding hypotheses are the finite atomic interface; arbitrary
external predicates and powersets are never inserted into the source. -/

namespace FregeanECA.Research.Z2Reverse.ComprehensionTransfer
open Part2 ArithmeticModel NativeFormulaTools Positive RelationCoding ArithmeticCodeAtoms FormulaTranslation
universe u v w
variable {N : Type u} {S : Type v} {D : Type w}
  {A : ArithmeticStructure N S} {coding : Presentation D N}
  {application : D → D → D} {k s : D}
  {operations : coding.CodeOperations application k s}

def tupleVariables (length : Nat) (i : Nat) : NTerm :=
  .var (if i < length then i else i + 1)

theorem tupleVariables_value (length : Nat) (xs : Fin length → N)
    (numbers : Nat → N) (input : N) (i : Nat) :
    termValue A (assignTuple length xs (pushObject numbers input)) (tupleVariables length i) =
      assignTuple length xs numbers i := by
  by_cases hi : i < length
  · simp only [tupleVariables, if_pos hi, termValue]
    exact (assignTuple_at length xs _ ⟨i, hi⟩).trans (assignTuple_at length xs _ ⟨i, hi⟩).symm
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
    simp only [tupleVariables, if_neg hi, termValue]
    rw [Nat.add_assoc, assignTuple_after, assignTuple_after]
    rfl

def sourceSets (predicates : PredicateAssignment (coding.Relation (membership A))) : Nat → S :=
  fun i => (predicates (Nat.unpair i).1 (Nat.unpair i).2).val

theorem sourceSets_assigned (predicates : PredicateAssignment (coding.Relation (membership A))) :
    ∀ arity i, sourceSets predicates (Nat.pair arity i) = (predicates arity i).val := by
  intro arity i
  unfold sourceSets
  rw [Nat.unpair_pair]

namespace Definitions
variable (atoms : ArithmeticCodeAtoms.Definitions A coding operations)

def pullbackFormula (arity : Nat) (formula : Applicative.Formula) : NFormula :=
  existsNumbers (arity + 1) (.conjunction
    (atoms.tupleGraph arity (fun i => .var i.val) (.var (arity + 1)))
    (FormulaTranslation.Definitions.translate atoms (tupleVariables (arity + 1)) Nat.pair formula))

theorem pullbackFormula_truth (arity : Nat) (formula : Applicative.Formula)
    (numbers : Nat → N) (input : N)
    (predicates : PredicateAssignment (coding.Relation (membership A))) :
    truth A (pushObject numbers input) (sourceSets predicates) (pullbackFormula atoms arity formula) ↔
      ∃ xs : Fin (arity + 1) → N, input = coding.tuple arity xs ∧
        coding.codeTruth (membership A) operations (assignTuple (arity + 1) xs numbers) predicates formula := by
  simp only [pullbackFormula, existsNumbers_truth, truth, atoms.tupleGraph_truth, termValue, assignTuple_at]
  apply exists_congr
  intro xs
  have input_value : assignTuple (arity + 1) xs (pushObject numbers input) (arity + 1) = input := by
    simpa only [Nat.add_zero, pushObject] using assignTuple_after (arity + 1) xs (pushObject numbers input) 0
  rw [input_value]
  apply and_congr_right
  intro _
  exact FormulaTranslation.Definitions.translate_truth atoms formula _ _ _ _ _ _
    (tupleVariables_value _ _ _ _) (sourceSets_assigned predicates)

include atoms

theorem codePullbackRepresentation (model : ModelsZ2 A) (arity : Nat) (formula : Applicative.Formula)
    (numbers : Nat → N) (predicates : PredicateAssignment (coding.Relation (membership A))) :
    ∃ X : S, ∀ xs : Fin (arity + 1) → N,
      A.member (coding.tuple arity xs) X ↔
        coding.codeTruth (membership A) operations (assignTuple (arity + 1) xs numbers) predicates formula := by
  obtain ⟨X, represented⟩ := formula_comprehension A model
    (pullbackFormula atoms arity formula) numbers (sourceSets predicates)
  refine ⟨X, fun xs => ?_⟩
  rw [represented, pullbackFormula_truth]
  constructor
  · rintro ⟨ys, same, h⟩
    have identical : xs = ys := atoms.tuple_injective arity same
    simpa only [identical] using h
  · intro h; exact ⟨xs, rfl, h⟩

/-- The former whole-language representation obligation follows from source
Z2 comprehension and the finite atomic coding definitions. -/
theorem pullbackRepresentation (model : ModelsZ2 A) :
    coding.PullbackRepresentation (membership A) application k s := by
  intro arity formula parameters predicates
  obtain ⟨X, represented⟩ := codePullbackRepresentation atoms model arity formula
    (fun i => coding.representative (parameters i)) predicates
  refine ⟨X, fun xs => ?_⟩
  refine (represented xs).trans ?_
  rw [coding.codeTruth_iff_truth (membership A) application k s operations]
  rw [assignTuple_map]
  simp only [Presentation.decode_representative]
  rfl

/-- Every available-set Z2 model has full target comprehension once the
finite code graphs have been defined. The explicit set environment supplies
nonemptiness of the source set sort. -/
theorem fullComprehension (model : ModelsZ2 A) (sets : Nat → S) :
    HasFullComprehension (coding.interpretation (membership A) application k s) := by
  obtain ⟨empty, empty_law⟩ := formula_comprehension A model .falsum (fun _ => A.zero) sets
  apply coding.fullComprehension_of_pullbackRepresentation (membership A) application k s empty
  · intro c h
    exact (empty_law c).mp h
  · exact pullbackRepresentation atoms model

theorem fcAlgebra (model : ModelsZ2 A) (sets : Nat → S) :
    V2.FCAlgebra (coding.interpretation (membership A) application k s) :=
  V2.fullComprehension_implies_fcAlgebra _ (fullComprehension atoms model sets)

end Definitions
end FregeanECA.Research.Z2Reverse.ComprehensionTransfer
