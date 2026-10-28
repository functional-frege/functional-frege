import FregeanECA.Research.Z2Reverse.ModelTruth

/-! The converse truth lemma for the actual guarded arithmetic encoding.
Only free variables occurring in the formula need satisfy their sort guards.
-/
namespace FregeanECA.Research.Z2Reverse.ArithmeticModel

open FFL FFL.FirstOrder Part2 ArithmeticEncoding
open scoped FFL.FirstOrder

universe u
variable {M : Type u} [Structure language M]

open Classical in
noncomputable def recoverSorted (typing : SortCorrect M) (kind : SortName) (x : M) :
    {y : M // HasSort M kind y} :=
  if h : HasSort M kind x then ⟨x, h⟩
  else ⟨Classical.choose (typing.inhabited kind), Classical.choose_spec (typing.inhabited kind)⟩

theorem recoverSorted_val (typing : SortCorrect M) (kind : SortName) (x : M)
    (h : HasSort M kind x) : (recoverSorted typing kind x).val = x := by
  classical
  simp [recoverSorted, h]

theorem guarded_assignment_recovery (typing : SortCorrect M) (free : Nat → M) :
    ∃ (numbers : Nat → Number M) (sets : Nat → SetObject M),
      ∀ i, HasSort M (variableSort i) (free i) →
        encodedAssignment numbers sets i = free i := by
  let numbers := fun j => recoverSorted typing .number (free (variableCode .number j))
  let sets := fun j => recoverSorted typing .set (free (variableCode .set j))
  refine ⟨numbers, sets, ?_⟩
  intro i guarded
  have code := variableCode_recover i
  cases kind : variableSort i with
  | number =>
      have code' : variableCode .number (i / 2) = i := by simpa [kind] using code
      simp only [encodedAssignment, kind, numbers, code']
      exact recoverSorted_val typing .number (free i) (by simpa [kind] using guarded)
  | set =>
      have code' : variableCode .set (i / 2) = i := by simpa [kind] using code
      simp only [encodedAssignment, kind, sets, code']
      exact recoverSorted_val typing .set (free i) (by simpa [kind] using guarded)

theorem sentence_truth_backward [Nonempty M] [Structure.Eq language M]
    (typing : SortCorrect M) (p : SecondOrderArithmetic.Formula)
    (holds : ∀ numbers sets, truth (extracted M typing) numbers sets p) :
    (sentence p).Realize M := by
  rw [sentence, Semiformula.eval_univCl]
  intro free
  rw [LogicalConnective.HomClass.map_imply]
  intro guarded
  obtain ⟨numbers, sets, recovered⟩ := guarded_assignment_recovery typing free
  have encoded : Semiformula.Evalf (encodedAssignment numbers sets) (formula initialMap p) :=
    (formula_truth typing p _ _ _ _ _ (encodedAssignment_maps numbers sets)).mpr (holds numbers sets)
  apply (Semiformula.eval_iff_of_funEqOn (formula initialMap p) ?_).mp encoded
  intro i present
  apply recovered
  exact (freeGuards_truth _ _).mp guarded i (by simpa using present)

theorem sentence_truth_iff [Nonempty M] [Structure.Eq language M]
    (typing : SortCorrect M) (p : SecondOrderArithmetic.Formula) :
    (sentence p).Realize M ↔ ∀ numbers sets, truth (extracted M typing) numbers sets p :=
  ⟨sentence_truth_forward typing p, sentence_truth_backward typing p⟩

end FregeanECA.Research.Z2Reverse.ArithmeticModel

#print axioms FregeanECA.Research.Z2Reverse.ArithmeticModel.sentence_truth_backward
#print axioms FregeanECA.Research.Z2Reverse.ArithmeticModel.sentence_truth_iff
