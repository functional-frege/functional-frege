import FregeanECA.Research.Z2Reverse.ArithmeticCodeAtoms

/-! A compositional translation of the entire applicative formula language
into native second-order arithmetic, conditional on the five finite atomic
coding definitions. Quantifiers use the source's available sets, guarded by
an arithmetic saturation formula. -/

namespace FregeanECA.Research.Z2Reverse.FormulaTranslation
open Part2 ArithmeticModel NativeFormulaTools Positive RelationCoding ArithmeticCodeAtoms
universe u v w
variable {N : Type u} {S : Type v} {D : Type w}
  {A : ArithmeticStructure N S} {coding : Presentation D N}
  {application : D → D → D} {k s : D}
  {operations : coding.CodeOperations application k s}

abbrev membership (A : ArithmeticStructure N S) : RelationCoding.Membership N S := fun X x => A.member x X

def bindRelationMap (map : Nat → Nat → Nat) (arity : Nat) : Nat → Nat → Nat :=
  fun other i => if other = arity then Functional.bindMap (map other) i else map other i + 1

theorem bindRelationMap_assigned (map : Nat → Nat → Nat) (sets : Nat → S)
    (predicates : PredicateAssignment (coding.Relation (membership A)))
    (assigned : ∀ arity i, sets (map arity i) = (predicates arity i).val)
    (arity : Nat) (X : coding.Relation (membership A) arity) :
    ∀ other i, pushObject sets X.val (bindRelationMap map arity other i) =
      (pushPredicate predicates arity X other i).val := by
  intro other i
  by_cases same : other = arity
  · subst other
    cases i <;> simp [bindRelationMap, Functional.bindMap, pushObject, pushPredicate, assigned]
  · simp [bindRelationMap, same, pushObject, pushPredicate, assigned]

namespace Definitions
variable (atoms : ArithmeticCodeAtoms.Definitions A coding operations)

def saturatedFormula (arity setIndex : Nat) : NFormula :=
  forallNumbers (arity + 1) (forallNumbers (arity + 1) (.implies
    (andFin (arity + 1) (fun i => atoms.equalFormula (.var (arity + 1 + i.val)) (.var i.val)))
    (SecondOrderArithmetic.iffF
      (atoms.tupleMember arity setIndex (fun i => .var (arity + 1 + i.val)))
      (atoms.tupleMember arity setIndex (fun i => .var i.val)))))

theorem saturatedFormula_truth (arity setIndex : Nat) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (saturatedFormula atoms arity setIndex) ↔
      coding.Saturated (membership A) arity (sets setIndex) := by
  simp only [saturatedFormula, forallNumbers_truth, truth, andFin_truth,
    atoms.equal_truth, SecondOrderArithmetic.iffF, atoms.tupleMember_truth,
    termValue, assignTuple_at, assignTuple_after]
  constructor
  · intro h xs ys same
    exact ⟨(h xs ys (fun i => congrFun same i)).1, (h xs ys (fun i => congrFun same i)).2⟩
  · intro h xs ys same
    exact ⟨(h xs ys (funext same)).1, (h xs ys (funext same)).2⟩

def equalFormula (varTerms : Nat → NTerm) (left right : Positive.Term) : NFormula :=
  .existsNumber (.existsNumber (.conjunction
    (atoms.termGraph (fun i => liftTerm 2 (varTerms i)) (.var 1) left)
    (.conjunction (atoms.termGraph (fun i => liftTerm 2 (varTerms i)) (.var 0) right)
      (atoms.equalFormula (.var 1) (.var 0)))))

theorem equalFormula_truth (varTerms : Nat → NTerm) (left right : Positive.Term)
    (objects numbers : Nat → N) (sets : Nat → S)
    (assigned : ∀ i, termValue A numbers (varTerms i) = objects i) :
    truth A numbers sets (equalFormula atoms varTerms left right) ↔
      coding.decode (coding.termCode operations objects left) =
        coding.decode (coding.termCode operations objects right) := by
  have terms (t : Positive.Term) (out : NTerm) (a b : N) :=
    atoms.termGraph_truth t objects (fun i => liftTerm 2 (varTerms i)) out
      (pushObject (pushObject numbers a) b) sets (by
        intro i
        simpa only [liftTerm, ArithmeticLanguage.renameTerm_value, pushObject] using assigned i)
  simp only [equalFormula, truth]
  simp only [terms, atoms.equal_truth, termValue, pushObject]
  constructor
  · rintro ⟨a, b, rfl, rfl, h⟩; exact h
  · intro h; exact ⟨_, _, rfl, rfl, h⟩

def relationFormula (varTerms : Nat → NTerm) (arity setIndex : Nat)
    (args : Fin (arity + 1) → Positive.Term) : NFormula :=
  existsNumbers (arity + 1) (.conjunction
    (andFin (arity + 1) (fun i => atoms.termGraph
      (fun j => liftTerm (arity + 1) (varTerms j)) (.var i.val) (args i)))
    (atoms.tupleMember arity setIndex (fun i => .var i.val)))

theorem relationFormula_truth (varTerms : Nat → NTerm) (arity setIndex : Nat)
    (args : Fin (arity + 1) → Positive.Term) (objects numbers : Nat → N) (sets : Nat → S)
    (assigned : ∀ i, termValue A numbers (varTerms i) = objects i) :
    truth A numbers sets (relationFormula atoms varTerms arity setIndex args) ↔
      A.member (coding.tuple arity (fun i => coding.termCode operations objects (args i)))
        (sets setIndex) := by
  have terms (t : Positive.Term) (out : NTerm) (xs : Fin (arity + 1) → N) :=
    atoms.termGraph_truth t objects (fun i => liftTerm (arity + 1) (varTerms i)) out
      (assignTuple (arity + 1) xs numbers) sets (by
        intro i
        simpa only [liftTerm_value] using assigned i)
  simp only [relationFormula, existsNumbers_truth, truth, andFin_truth]
  simp only [terms, atoms.tupleMember_truth, termValue, assignTuple_at]
  constructor
  · rintro ⟨xs, hxs, h⟩
    have same : xs = fun i => coding.termCode operations objects (args i) := funext hxs
    simpa only [same] using h
  · intro h; exact ⟨_, fun _ => rfl, h⟩

def translate (atoms : ArithmeticCodeAtoms.Definitions A coding operations)
    (varTerms : Nat → NTerm) (relationMap : Nat → Nat → Nat) : Applicative.Formula → NFormula
  | .equal a b => equalFormula atoms varTerms a b
  | .relation arity i args => relationFormula atoms varTerms arity (relationMap arity i) args
  | .relationEqual arity i j => .setEqual (relationMap arity i) (relationMap arity j)
  | .falsum => .falsum
  | .implies p q => .implies (translate atoms varTerms relationMap p) (translate atoms varTerms relationMap q)
  | .conjunction p q => .conjunction (translate atoms varTerms relationMap p) (translate atoms varTerms relationMap q)
  | .disjunction p q => .disjunction (translate atoms varTerms relationMap p) (translate atoms varTerms relationMap q)
  | .existsObject p => .existsNumber
      (translate atoms (pushObject (fun i => liftTerm 1 (varTerms i)) (.var 0)) relationMap p)
  | .forallObject p => .forallNumber
      (translate atoms (pushObject (fun i => liftTerm 1 (varTerms i)) (.var 0)) relationMap p)
  | .existsPredicate arity p => .existsSet (.conjunction (saturatedFormula atoms arity 0)
      (translate atoms varTerms (bindRelationMap relationMap arity) p))
  | .forallPredicate arity p => .forallSet (.implies (saturatedFormula atoms arity 0)
      (translate atoms varTerms (bindRelationMap relationMap arity) p))

theorem translate_truth (formula : Applicative.Formula) :
    ∀ (varTerms : Nat → NTerm) (relationMap : Nat → Nat → Nat)
      (objects numbers : Nat → N) (sets : Nat → S)
      (predicates : PredicateAssignment (coding.Relation (membership A))),
    (∀ i, termValue A numbers (varTerms i) = objects i) →
    (∀ arity i, sets (relationMap arity i) = (predicates arity i).val) →
    (truth A numbers sets (translate atoms varTerms relationMap formula) ↔
      coding.codeTruth (membership A) operations objects predicates formula) := by
  induction formula with
  | equal a b =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      exact equalFormula_truth atoms _ _ _ _ _ _ obj
  | relation arity i args =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      simpa only [translate, Presentation.codeTruth, membership, rel] using
        relationFormula_truth atoms varTerms arity (relationMap arity i) args objects numbers sets obj
  | relationEqual arity i j =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      simp only [translate, truth, Presentation.codeTruth, rel]
  | falsum => intros; exact Iff.rfl
  | implies p q hp hq =>
      intros; exact imp_congr (hp _ _ _ _ _ _ ‹_› ‹_›) (hq _ _ _ _ _ _ ‹_› ‹_›)
  | conjunction p q hp hq =>
      intros; exact and_congr (hp _ _ _ _ _ _ ‹_› ‹_›) (hq _ _ _ _ _ _ ‹_› ‹_›)
  | disjunction p q hp hq =>
      intros; exact or_congr (hp _ _ _ _ _ _ ‹_› ‹_›) (hq _ _ _ _ _ _ ‹_› ‹_›)
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
        exact (hp _ _ _ _ _ _ obj (bindRelationMap_assigned _ _ _ rel arity ⟨X, guard⟩)).mp h
      · rintro ⟨X, h⟩
        refine ⟨X.val, X.property, ?_⟩
        exact (hp _ _ _ _ _ _ obj (bindRelationMap_assigned _ _ _ rel arity X)).mpr h
  | forallPredicate arity p hp =>
      intro varTerms relationMap objects numbers sets predicates obj rel
      simp only [translate, truth, saturatedFormula_truth, pushObject, Presentation.codeTruth]
      constructor
      · intro h X
        exact (hp _ _ _ _ _ _ obj (bindRelationMap_assigned _ _ _ rel arity X)).mp
          (h X.val X.property)
      · intro h X guard
        exact (hp _ _ _ _ _ _ obj (bindRelationMap_assigned _ _ _ rel arity ⟨X, guard⟩)).mpr
          (h ⟨X, guard⟩)

end Definitions
end FregeanECA.Research.Z2Reverse.FormulaTranslation
