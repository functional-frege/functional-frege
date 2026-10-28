import FregeanECA.Syntax
import FregeanECA.Comprehension

/-! Actual first-order axiom schemes. Universal closure of the remaining
parameters is performed by the guarded encoding, not by semantic definition.
-/
namespace FregeanECA.Axioms
open Functional

def iffF (p q : Formula) : Formula := .conjunction (.implies p q) (.implies q p)
def notF (p : Formula) : Formula := .implies p .falsum

def allObjects : Nat → Formula → Formula
  | 0, p => p
  | n + 1, p => allObjects n (.forallObject p)

def allFunctions : Nat → Formula → Formula
  | 0, p => p
  | n + 1, p => allFunctions n (.forallFunction p)

def relationAtom (arity index : Nat) : Formula :=
  .relation arity index (fun i => .var i.val)

def kLaw : Formula := allObjects 2
  (.equal (.app (.app .constantK (.var 0)) (.var 1)) (.var 0))
def sLaw : Formula := allObjects 3
  (.equal (.app (.app (.app .constantS (.var 0)) (.var 1)) (.var 2))
    (.app (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2))))
def extensionality : Formula := allObjects 2
  (.implies (.forallObject (.equal (.app (.var 1) (.var 0)) (.app (.var 2) (.var 0))))
    (.equal (.var 0) (.var 1)))
def nontriviality : Formula := .existsObject (.existsObject (notF (.equal (.var 0) (.var 1))))

def lawV : Formula := allFunctions 2
  (iffF (.equal (.delta 0) (.delta 1))
    (.forallObject (.equal (.eval 0 (.var 0)) (.eval 1 (.var 0)))))
def coverage : Formula := .forallObject (.existsFunction (.equal (.delta 0) (.var 0)))
def evaluation : Formula := .forallFunction (.forallObject
  (.equal (.eval 0 (.var 0)) (.app (.delta 0) (.var 0))))
def functionExtensionality : Formula := allFunctions 2
  (.implies (.forallObject (.equal (.eval 0 (.var 0)) (.eval 1 (.var 0))))
    (.functionEqual 0 1))

/-- Apply a function representative to the displayed arguments in tuple order. -/
def applyVariables : Nat → Term → Term
  | 0, code => code
  | n + 1, code => .app (applyVariables n code) (.var n)

/-- Syntax for f(x-vector), with arity+1 displayed arguments. This is an
abbreviation in the existing signature, not a new term constructor. -/
abbrev functionValue (arity function : Nat) : Term :=
  applyVariables (arity + 1) (.delta function)

def functionalComprehension (arity : Nat) (body : Positive.Term) : Formula :=
  .existsFunction (allObjects (arity + 1)
    (.equal (functionValue arity 0) body.functional))

/-- Expanding the new presentation gives literally the old A2 instance. -/
theorem functionalComprehension_expansion (arity : Nat) (body : Positive.Term) :
    functionalComprehension arity body =
      .existsFunction (allObjects (arity + 1)
        (.equal (applyVariables (arity + 1) (.delta 0)) body.functional)) := rfl

/-- The relation-variable map lifted through a binder of one given arity. -/
def bindPredicateMap (m : Nat → Nat → Nat) (bound : Nat) : Nat → Nat → Nat :=
  fun arity index => if arity = bound then bindMap (m arity) index else m arity index

def renamePositivePredicates (m : Nat → Nat → Nat) : PositiveFormula → PositiveFormula
  | .equal a b => .equal a b
  | .relation arity index arguments => .relation arity (m arity index) arguments
  | .conjunction a b => .conjunction (renamePositivePredicates m a) (renamePositivePredicates m b)
  | .disjunction a b => .disjunction (renamePositivePredicates m a) (renamePositivePredicates m b)
  | .existsObject body => .existsObject (renamePositivePredicates m body)
  | .forallObject body => .forallObject (renamePositivePredicates m body)
  | .existsFunction body => .existsFunction (renamePositivePredicates m body)
  | .forallFunction body => .forallFunction (renamePositivePredicates m body)
  | .existsPredicate arity body => .existsPredicate arity (renamePositivePredicates (bindPredicateMap m arity) body)
  | .forallPredicate arity body => .forallPredicate arity (renamePositivePredicates (bindPredicateMap m arity) body)

def embedPositive : PositiveFormula → Formula
  | .equal a b => .equal a b
  | .relation arity index arguments => .relation arity index arguments
  | .conjunction a b => .conjunction (embedPositive a) (embedPositive b)
  | .disjunction a b => .disjunction (embedPositive a) (embedPositive b)
  | .existsObject body => .existsObject (embedPositive body)
  | .forallObject body => .forallObject (embedPositive body)
  | .existsFunction body => .existsFunction (embedPositive body)
  | .forallFunction body => .forallFunction (embedPositive body)
  | .existsPredicate arity body => .existsPredicate arity (embedPositive body)
  | .forallPredicate arity body => .forallPredicate arity (embedPositive body)

def relationalComprehension (arity : Nat) (body : PositiveFormula) : Formula :=
  .existsPredicate arity (allObjects (arity + 1)
    (iffF (relationAtom arity 0)
      (embedPositive (renamePositivePredicates
        (fun other index => if other = arity then index + 1 else index) body))))

def equalityRelation : Formula := .existsPredicate 1 (allObjects 2
  (iffF (relationAtom 1 0) (.equal (.var 0) (.var 1))))
def intersection (arity : Nat) : Formula := .existsPredicate arity (allObjects (arity + 1)
  (iffF (relationAtom arity 0) (.conjunction (relationAtom arity 1) (relationAtom arity 2))))
def union (arity : Nat) : Formula := .existsPredicate arity (allObjects (arity + 1)
  (iffF (relationAtom arity 0) (.disjunction (relationAtom arity 1) (relationAtom arity 2))))
def preimage (source target : Nat) : Formula :=
  .existsPredicate target (allObjects (target + 1)
    (iffF (relationAtom target 0)
      (.relation source (if source = target then 1 else 0)
        (fun i => applyVariables (target + 1) (.var (target + 1 + i.val))))))
def existsProjection (arity : Nat) : Formula :=
  .existsPredicate arity (allObjects (arity + 1)
    (iffF (relationAtom arity 0)
      (.existsObject (.relation (arity + 1) 0
        (Fin.lastCases (.var 0) (fun i => .var (i.val + 1)))))))
def forallProjection (arity : Nat) : Formula :=
  .existsPredicate arity (allObjects (arity + 1)
    (iffF (relationAtom arity 0)
      (.forallObject (.relation (arity + 1) 0
        (Fin.lastCases (.var 0) (fun i => .var (i.val + 1)))))))

inductive FunctionalAxiom : Formula → Prop where
  | relational (n : Nat) (p : PositiveFormula) : FunctionalAxiom (relationalComprehension n p)
  | functional (n : Nat) (t : Positive.Term) : FunctionalAxiom (functionalComprehension n t)
  | lawV : FunctionalAxiom lawV
  | coverage : FunctionalAxiom coverage
  | nontriviality : FunctionalAxiom nontriviality
  | evaluation : FunctionalAxiom evaluation
  | k : FunctionalAxiom kLaw
  | s : FunctionalAxiom sLaw

inductive SpecificationAxiom : Formula → Prop where
  | k : SpecificationAxiom kLaw
  | s : SpecificationAxiom sLaw
  | ext : SpecificationAxiom extensionality
  | nontrivial : SpecificationAxiom nontriviality
  | equality : SpecificationAxiom equalityRelation
  | intersection (n : Nat) : SpecificationAxiom (intersection n)
  | union (n : Nat) : SpecificationAxiom (union n)
  | preimage (m n : Nat) : SpecificationAxiom (preimage m n)
  | existsProjection (n : Nat) : SpecificationAxiom (existsProjection n)
  | forallProjection (n : Nat) : SpecificationAxiom (forallProjection n)

universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

theorem allObjects_truth (M : Interpretation D F R) (n : Nat) (p : Formula)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (allObjects n p).truth M o f r ↔
      ∀ xs : Fin n → D, p.truth M (Positive.assignTuple n xs o) f r := by
  induction n generalizing p with
  | zero =>
      constructor
      · intro h xs; exact h
      · intro h; exact h Fin.elim0
  | succ n ih =>
      rw [allObjects, ih]
      constructor
      · intro h xs
        exact h (fun i => xs i.succ) (xs 0)
      · intro h xs value
        exact h (Fin.cases value xs)

theorem allFunctions_truth (M : Interpretation D F R) (n : Nat) (p : Formula)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (allFunctions n p).truth M o f r ↔
      ∀ xs : Fin n → F, p.truth M o (Positive.assignTuple n xs f) r := by
  induction n generalizing p with
  | zero =>
      constructor
      · intro h xs; exact h
      · intro h; exact h Fin.elim0
  | succ n ih =>
      rw [allFunctions, ih]
      constructor
      · intro h xs
        exact h (fun i => xs i.succ) (xs 0)
      · intro h xs value
        exact h (Fin.cases value xs)

@[simp] theorem iffF_truth (M : Interpretation D F R) (p q : Formula)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (iffF p q).truth M o f r ↔ (p.truth M o f r ↔ q.truth M o f r) := Iff.intro
      (fun h => ⟨h.1,h.2⟩) (fun h => ⟨h.mp,h.mpr⟩)

theorem applyVariables_value (M : Interpretation D F R) (n : Nat) (code : Term)
    (o : Nat → D) (f : Nat → F) :
    (applyVariables n code).value M o f =
      Positive.applyArguments M.applicative (code.value M o f) (fun i : Fin n => o i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Positive.applyArguments_append]
      change M.applicative.apply ((applyVariables n code).value M o f) (o n) = _
      rw [ih]
      rfl

theorem embedPositive_truth (M : Interpretation D F R) (p : PositiveFormula) :
    ∀ o f r, (embedPositive p).truth M o f r ↔ p.truth M o f r := by
  induction p with
  | equal _ _ => intros; exact Iff.rfl
  | relation _ _ _ => intros; exact Iff.rfl
  | conjunction _ _ ih1 ih2 => intros; exact and_congr (ih1 _ _ _) (ih2 _ _ _)
  | disjunction _ _ ih1 ih2 => intros; exact or_congr (ih1 _ _ _) (ih2 _ _ _)
  | existsObject _ ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallObject _ ih => intros; exact forall_congr' (fun _ => ih _ _ _)
  | existsFunction _ ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallFunction _ ih => intros; exact forall_congr' (fun _ => ih _ _ _)
  | existsPredicate _ _ ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallPredicate _ _ ih => intros; exact forall_congr' (fun _ => ih _ _ _)

theorem predicateMap_under_binder (m : Nat → Nat → Nat)
    (r : Positive.PredicateAssignment R) (arity : Nat) (P : R arity) :
    (fun a i => Positive.pushPredicate r arity P a (bindPredicateMap m arity a i)) =
      Positive.pushPredicate (fun a i => r a (m a i)) arity P := by
  funext a i
  by_cases h : a = arity
  · subst a
    cases i <;> simp [bindPredicateMap, bindMap, Positive.pushPredicate]
  · simp [bindPredicateMap, Positive.pushPredicate, h]

theorem renamePositivePredicates_truth (M : Interpretation D F R) (p : PositiveFormula) :
    ∀ m o f r, (renamePositivePredicates m p).truth M o f r ↔
      p.truth M o f (fun a i => r a (m a i)) := by
  induction p with
  | equal _ _ => intros; exact Iff.rfl
  | relation _ _ _ => intros; exact Iff.rfl
  | conjunction _ _ ih1 ih2 => intros; exact and_congr (ih1 _ _ _ _) (ih2 _ _ _ _)
  | disjunction _ _ ih1 ih2 => intros; exact or_congr (ih1 _ _ _ _) (ih2 _ _ _ _)
  | existsObject _ ih => intros; exact exists_congr (fun _ => ih _ _ _ _)
  | forallObject _ ih => intros; exact forall_congr' (fun _ => ih _ _ _ _)
  | existsFunction _ ih => intros; exact exists_congr (fun _ => ih _ _ _ _)
  | forallFunction _ ih => intros; exact forall_congr' (fun _ => ih _ _ _ _)
  | existsPredicate arity body ih =>
      intro m o f r
      apply exists_congr
      intro P
      exact (ih _ _ _ _).trans (by rw [predicateMap_under_binder])
  | forallPredicate arity body ih =>
      intro m o f r
      apply forall_congr'
      intro P
      exact (ih _ _ _ _).trans (by rw [predicateMap_under_binder])

theorem shiftPredicate_truth (M : Interpretation D F R) (p : PositiveFormula)
    (arity : Nat) (P : R arity) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    (renamePositivePredicates (fun a i => if a = arity then i+1 else i) p).truth
      M o f (Positive.pushPredicate r arity P) ↔ p.truth M o f r := by
  rw [renamePositivePredicates_truth]
  have h : (fun a i => Positive.pushPredicate r arity P a
      (if a = arity then i+1 else i)) = r := by
    funext a i
    by_cases same : a = arity
    · subst a; simp [Positive.pushPredicate]
    · simp [Positive.pushPredicate, same]
  rw [h]

theorem relationalComprehension_truth (M : Interpretation D F R)
    (arity : Nat) (p : PositiveFormula) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    (relationalComprehension arity p).truth M o f r ↔
      ∃ P : R arity, ∀ xs,
        M.applicative.satisfies arity P xs ↔
          p.truth M (Positive.assignTuple (arity+1) xs o) f r := by
  change (∃ P, _) ↔ _
  apply exists_congr
  intro P
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  rw [iffF_truth, embedPositive_truth, shiftPredicate_truth]
  simp [relationAtom, Formula.truth, Term.value, Positive.pushPredicate]

theorem applicativeTerm_value (M : Interpretation D F R) (t : Positive.Term)
    (o : Nat → D) (f : Nat → F) : t.functional.value M o f = t.value M.applicative o := by
  induction t with
  | var _ => rfl
  | constantK => rfl
  | constantS => rfl
  | app _ _ ih1 ih2 => simp [Positive.Term.functional, Term.value, Positive.Term.value, ih1, ih2]

theorem functionalComprehension_truth (M : Interpretation D F R)
    (arity : Nat) (t : Positive.Term) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    (functionalComprehension arity t).truth M o f r ↔
      ∃ g : F, ∀ xs,
        M.evalVector g xs =
          t.value M.applicative (Positive.assignTuple (arity+1) xs o) := by
  change (∃ g, _) ↔ _
  apply exists_congr
  intro g
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  change (applyVariables (arity+1) (.delta 0)).value M _ _ = t.functional.value M _ _ ↔ _
  rw [applyVariables_value, applicativeTerm_value]
  simp [Term.value, Positive.pushObject]

end FregeanECA.Axioms
