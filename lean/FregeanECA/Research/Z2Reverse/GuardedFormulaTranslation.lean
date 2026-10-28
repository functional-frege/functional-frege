import FregeanECA.Research.Z2Reverse.UniformFormulaTranslation

/-! Finite saturation guards for universally closed target formulas. A
rectangular finite bound may include unused predicate names; it never omits
an occurring free predicate and is preserved under the de Bruijn binders. -/
namespace FregeanECA.Research.Z2Reverse.GuardedFormulaTranslation
open Part2 ArithmeticModel NativeFormulaTools Positive RelationCoding ArithmeticCodeAtoms
open FormulaTranslation

/-- A conservative finite bound on every predicate arity and index used. -/
def predicateBound : Applicative.Formula → Nat
  | .equal _ _ | .falsum => 0
  | .relation n i _ => max (n + 1) (i + 1)
  | .relationEqual n i j => max (n + 1) (max (i + 1) (j + 1))
  | .implies p q | .conjunction p q | .disjunction p q => max (predicateBound p) (predicateBound q)
  | .existsObject p | .forallObject p | .existsPredicate _ p | .forallPredicate _ p => predicateBound p

universe u v w
variable {N : Type u} {S : Type v} {D : Type w}
  {A : ArithmeticStructure N S} {coding : Presentation D N}
  {application : D → D → D} {k s : D}
  {operations : coding.CodeOperations application k s}

theorem bindRelationMap_assigned_below (map : Nat → Nat → Nat) (sets : Nat → S)
    (predicates : PredicateAssignment (coding.Relation (membership A))) (bound : Nat)
    (assigned : ∀ arity < bound, ∀ i < bound, sets (map arity i) = (predicates arity i).val)
    (arity : Nat) (X : coding.Relation (membership A) arity) :
    ∀ other < bound, ∀ i < bound, pushObject sets X.val (bindRelationMap map arity other i) =
      (pushPredicate predicates arity X other i).val := by
  intro other ho i hi
  by_cases same : other = arity
  · subst other
    cases i with
    | zero => simp [bindRelationMap, Functional.bindMap, pushObject, pushPredicate]
    | succ i => simpa [bindRelationMap, Functional.bindMap, pushObject, pushPredicate] using
        assigned arity ho i (by omega)
  · simp [bindRelationMap, same, pushObject, pushPredicate, assigned other ho i hi]

namespace Definitions
variable (atoms : ArithmeticCodeAtoms.Definitions A coding operations)
open FormulaTranslation.Definitions

theorem translate_truth_bounded (formula : Applicative.Formula) :
    ∀ (varTerms : Nat → NTerm) (relationMap : Nat → Nat → Nat)
      (objects numbers : Nat → N) (sets : Nat → S)
      (predicates : PredicateAssignment (coding.Relation (membership A))),
    (∀ i, termValue A numbers (varTerms i) = objects i) →
    (∀ arity < predicateBound formula, ∀ i < predicateBound formula,
      sets (relationMap arity i) = (predicates arity i).val) →
    (truth A numbers sets (translate atoms varTerms relationMap formula) ↔
      coding.codeTruth (membership A) operations objects predicates formula) := by
  induction formula with
  | equal a b =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      exact equalFormula_truth atoms _ _ _ _ _ _ obj
  | relation arity i args =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      simpa only [translate, Presentation.codeTruth, membership,
        rel arity (by simp [predicateBound]) i (by simp [predicateBound])] using
        relationFormula_truth atoms varTerms arity (relationMap arity i) args objects numbers sets obj
  | relationEqual arity i j =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      simp only [translate, truth, Presentation.codeTruth,
        rel arity (by simp [predicateBound]) i (by simp [predicateBound]),
        rel arity (by simp [predicateBound]) j (by simp [predicateBound])]
  | falsum => intros; exact Iff.rfl
  | implies p q hp hq =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      exact imp_congr (hp _ _ _ _ _ _ obj (fun a ha i hi => rel a
        (Nat.lt_of_lt_of_le ha (Nat.le_max_left _ _)) i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))))
        (hq _ _ _ _ _ _ obj (fun a ha i hi => rel a
        (Nat.lt_of_lt_of_le ha (Nat.le_max_right _ _)) i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))))
  | conjunction p q hp hq =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      exact and_congr (hp _ _ _ _ _ _ obj (fun a ha i hi => rel a
        (Nat.lt_of_lt_of_le ha (Nat.le_max_left _ _)) i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))))
        (hq _ _ _ _ _ _ obj (fun a ha i hi => rel a
        (Nat.lt_of_lt_of_le ha (Nat.le_max_right _ _)) i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))))
  | disjunction p q hp hq =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      exact or_congr (hp _ _ _ _ _ _ obj (fun a ha i hi => rel a
        (Nat.lt_of_lt_of_le ha (Nat.le_max_left _ _)) i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))))
        (hq _ _ _ _ _ _ obj (fun a ha i hi => rel a
        (Nat.lt_of_lt_of_le ha (Nat.le_max_right _ _)) i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))))
  | existsObject p hp =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      apply exists_congr
      intro x
      apply hp _ _ _ _ _ _ _ rel
      intro i
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [pushObject, liftTerm, ArithmeticLanguage.renameTerm_value] using obj i
  | forallObject p hp =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      apply forall_congr'
      intro x
      apply hp _ _ _ _ _ _ _ rel
      intro i
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [pushObject, liftTerm, ArithmeticLanguage.renameTerm_value] using obj i
  | existsPredicate arity p hp =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      simp only [translate, truth, saturatedFormula_truth, pushObject, Presentation.codeTruth]
      constructor
      · rintro ⟨X, guard, h⟩
        refine ⟨⟨X, guard⟩, ?_⟩
        exact (hp _ _ _ _ _ _ obj (bindRelationMap_assigned_below _ _ _ _ rel arity ⟨X, guard⟩)).mp h
      · rintro ⟨X, h⟩
        refine ⟨X.val, X.property, ?_⟩
        exact (hp _ _ _ _ _ _ obj (bindRelationMap_assigned_below _ _ _ _ rel arity X)).mpr h
  | forallPredicate arity p hp =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      simp only [translate, truth, saturatedFormula_truth, pushObject, Presentation.codeTruth]
      constructor
      · intro h X
        exact (hp _ _ _ _ _ _ obj (bindRelationMap_assigned_below _ _ _ _ rel arity X)).mp
          (h X.val X.property)
      · intro h X guard
        exact (hp _ _ _ _ _ _ obj (bindRelationMap_assigned_below _ _ _ _ rel arity ⟨X, guard⟩)).mpr
          (h ⟨X, guard⟩)



def guards (p : Applicative.Formula) : NFormula :=
  andFin (predicateBound p) (fun arity => andFin (predicateBound p) (fun i =>
    saturatedFormula atoms arity.val (Nat.pair arity.val i.val)))

theorem guards_truth (p : Applicative.Formula) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (guards atoms p) ↔
      ∀ arity i : Fin (predicateBound p),
        coding.Saturated (membership A) arity.val (sets (Nat.pair arity.val i.val)) := by
  simp only [guards, andFin_truth, saturatedFormula_truth]

def guarded (p : Applicative.Formula) : NFormula :=
  .implies (guards atoms p) (translate atoms SecondOrderArithmetic.Term.var Nat.pair p)

/-- Exact validity equivalence, including arbitrary free relation assignments. -/
theorem guarded_validity_iff (p : Applicative.Formula)
    (defaults : PredicateAssignment (coding.Relation (membership A))) :
    (∀ numbers sets, truth A numbers sets (guarded atoms p)) ↔
      ∀ objects predicates,
        p.truth (coding.interpretation (membership A) application k s) objects predicates := by
  constructor
  · intro holds objects predicates
    let numbers := fun i => coding.representative (objects i)
    let sets := ComprehensionTransfer.sourceSets predicates
    have guard : truth A numbers sets (guards atoms p) := by
      apply (guards_truth atoms p numbers sets).mpr
      intro arity i
      rw [show sets (Nat.pair arity.val i.val) = (predicates arity.val i.val).val from
        ComprehensionTransfer.sourceSets_assigned predicates arity.val i.val]
      exact (predicates arity.val i.val).property
    have code := (FormulaTranslation.Definitions.translate_truth atoms p SecondOrderArithmetic.Term.var Nat.pair
      numbers numbers sets predicates (fun _ => rfl)
      (ComprehensionTransfer.sourceSets_assigned predicates)).mp (holds numbers sets guard)
    have actual := (coding.codeTruth_iff_truth (membership A) application k s operations p
      numbers predicates).mp code
    simpa only [numbers, Presentation.decode_representative] using actual
  · intro holds numbers sets guard
    have saturation := (guards_truth atoms p numbers sets).mp guard
    let predicates : PredicateAssignment (coding.Relation (membership A)) := fun arity i =>
      if h : arity < predicateBound p ∧ i < predicateBound p then
        ⟨sets (Nat.pair arity i), saturation ⟨arity, h.1⟩ ⟨i, h.2⟩⟩
      else defaults arity i
    apply (translate_truth_bounded atoms p SecondOrderArithmetic.Term.var Nat.pair numbers numbers sets predicates
      (fun _ => rfl) ?_).mpr
    · exact (coding.codeTruth_iff_truth (membership A) application k s operations p
        numbers predicates).mpr (holds _ _)
    · intro arity ha i hi
      simp [predicates, ha, hi]

end Definitions

/-- The fixed arithmetic sentence body, with all free relation parameters guarded. -/
noncomputable def translate (p : Applicative.Formula) : NFormula :=
  .implies
    (andFin (predicateBound p) (fun arity => andFin (predicateBound p) (fun i =>
      UniformFormulaTranslation.fixedAtoms.saturatedFormula arity.val (Nat.pair arity.val i.val))))
    (UniformFormulaTranslation.rawTranslate SecondOrderArithmetic.Term.var Nat.pair p)

@[simp] theorem translate_eq (A : ArithmeticStructure N S) (model : ModelsZ2 A)
    (sets : Nat → S) (p : Applicative.Formula) :
    translate p = Definitions.guarded (InternalConversionFormula.definitions A model sets) p := by
  let atoms := InternalConversionFormula.definitions A model sets
  have same := UniformFormulaTranslation.ofDefinitions_fixed A model sets
  unfold translate UniformFormulaTranslation.rawTranslate Definitions.guarded Definitions.guards
  rw [← same]
  simp only [UniformFormulaTranslation.translate_eq, UniformFormulaTranslation.saturatedFormula_eq]

/-- False remains false; the empty guard does not weaken consistency transfer. -/
theorem falsum_truth (A : ArithmeticStructure N S) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (translate .falsum) ↔ False := by
  simp [translate, predicateBound, andFin, UniformFormulaTranslation.rawTranslate,
    UniformFormulaTranslation.Atoms.translate, truth]

end FregeanECA.Research.Z2Reverse.GuardedFormulaTranslation
