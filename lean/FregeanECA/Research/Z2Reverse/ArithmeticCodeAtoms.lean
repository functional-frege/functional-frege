import FregeanECA.Research.Z2Reverse.NativeFormulaTools
import FregeanECA.Research.Z2Reverse.RelationCoding

/-!
The finite atomic definability interface for the reverse interpretation.
Its obligations concern only equality of decoded codes, K/S codes, binary
application and injective numeric pairing. No formula-comprehension or
arbitrary target-formula representation is assumed.
-/

namespace FregeanECA.Research.Z2Reverse.ArithmeticCodeAtoms
open Part2 ArithmeticModel NativeFormulaTools Positive RelationCoding
universe u v w
variable {N : Type u} {S : Type v} {D : Type w}

abbrev NTerm := SecondOrderArithmetic.Term
abbrev NFormula := SecondOrderArithmetic.Formula

def liftTerm (n : Nat) (t : NTerm) : NTerm :=
  ArithmeticLanguage.renameTerm (fun i => i + n) t

theorem liftTerm_value (A : ArithmeticStructure N S) (n : Nat) (xs : Fin n → N)
    (numbers : Nat → N) (t : NTerm) :
    termValue A (assignTuple n xs numbers) (liftTerm n t) = termValue A numbers t := by
  rw [liftTerm, ArithmeticLanguage.renameTerm_value, assignTuple_shift]

def tupleValue (pair : N → N → N) : (arity : Nat) → (Fin (arity + 1) → N) → N
  | 0, xs => xs 0
  | n + 1, xs => pair (xs 0) (tupleValue pair n (fun i => xs i.succ))

theorem tupleValue_injective (pair : N → N → N)
    (injective : ∀ a b c d, pair a b = pair c d → a = c ∧ b = d) (arity : Nat) :
    Function.Injective (tupleValue pair arity) := by
  induction arity with
  | zero =>
      intro xs ys h
      funext i
      exact Fin.cases h (fun j => Fin.elim0 j) i
  | succ arity ih =>
      intro xs ys h
      obtain ⟨head, tail⟩ := injective _ _ _ _ h
      have same := ih tail
      funext i
      exact Fin.cases head (fun j => congrFun same j) i

/-- Five arithmetic atomic builders and their exact truth laws. Builders
take native terms, so they support arbitrary parameters and fresh binders. -/
structure Definitions (A : ArithmeticStructure N S) (coding : Presentation D N)
    {application : D → D → D} {k s : D}
    (operations : coding.CodeOperations application k s) where
  pair : N → N → N
  pair_injective : ∀ a b c d, pair a b = pair c d → a = c ∧ b = d
  tuple_law : ∀ arity xs, coding.tuple arity xs = tupleValue pair arity xs
  equalFormula : NTerm → NTerm → NFormula
  kFormula : NTerm → NFormula
  sFormula : NTerm → NFormula
  appFormula : NTerm → NTerm → NTerm → NFormula
  pairFormula : NTerm → NTerm → NTerm → NFormula
  equal_truth : ∀ a b numbers sets,
    truth A numbers sets (equalFormula a b) ↔
      coding.decode (termValue A numbers a) = coding.decode (termValue A numbers b)
  k_truth : ∀ output numbers sets,
    truth A numbers sets (kFormula output) ↔ termValue A numbers output = operations.constantK
  s_truth : ∀ output numbers sets,
    truth A numbers sets (sFormula output) ↔ termValue A numbers output = operations.constantS
  app_truth : ∀ a b output numbers sets,
    truth A numbers sets (appFormula a b output) ↔
      termValue A numbers output = operations.apply (termValue A numbers a) (termValue A numbers b)
  pair_truth : ∀ a b output numbers sets,
    truth A numbers sets (pairFormula a b output) ↔
      termValue A numbers output = pair (termValue A numbers a) (termValue A numbers b)

namespace Definitions
variable {A : ArithmeticStructure N S} {coding : Presentation D N}
  {application : D → D → D} {k s : D} {operations : coding.CodeOperations application k s}
  (atoms : Definitions A coding operations)

include atoms in
theorem tuple_injective (arity : Nat) : Function.Injective (coding.tuple arity) := by
  intro xs ys same
  apply tupleValue_injective atoms.pair atoms.pair_injective arity
  simpa only [atoms.tuple_law] using same

def tupleGraph (atoms : Definitions A coding operations) : (arity : Nat) → (Fin (arity + 1) → NTerm) → NTerm → NFormula
  | 0, args, output => .equal output (args 0)
  | n + 1, args, output => .existsNumber (.conjunction
      (atoms.tupleGraph n (fun i => liftTerm 1 (args i.succ)) (.var 0))
      (atoms.pairFormula (liftTerm 1 (args 0)) (.var 0) (liftTerm 1 output)))

theorem tupleGraph_truth (arity : Nat) (args : Fin (arity + 1) → NTerm) (output : NTerm)
    (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (atoms.tupleGraph arity args output) ↔
      termValue A numbers output = coding.tuple arity (fun i => termValue A numbers (args i)) := by
  rw [atoms.tuple_law]
  induction arity generalizing output numbers with
  | zero => rfl
  | succ n ih =>
      simp only [tupleGraph, truth, ih, atoms.pair_truth, liftTerm,
        ArithmeticLanguage.renameTerm_value, pushObject, termValue, tupleValue]
      constructor
      · rintro ⟨x, rfl, h⟩; exact h
      · intro h; exact ⟨_, rfl, h⟩

def termGraph (atoms : Definitions A coding operations) (varTerms : Nat → NTerm) (output : NTerm) : Positive.Term → NFormula
  | .var i => .equal output (varTerms i)
  | .constantK => atoms.kFormula output
  | .constantS => atoms.sFormula output
  | .app f x => .existsNumber (.existsNumber (.conjunction
      (atoms.termGraph (fun i => liftTerm 2 (varTerms i)) (.var 1) f)
      (.conjunction (atoms.termGraph (fun i => liftTerm 2 (varTerms i)) (.var 0) x)
        (atoms.appFormula (.var 1) (.var 0) (liftTerm 2 output)))))

theorem termGraph_truth (term : Positive.Term) (objects : Nat → N) :
    ∀ (varTerms : Nat → NTerm) (output : NTerm) (numbers : Nat → N) (sets : Nat → S),
      (∀ i, termValue A numbers (varTerms i) = objects i) →
      (truth A numbers sets (atoms.termGraph varTerms output term) ↔
        termValue A numbers output = coding.termCode operations objects term) := by
  induction term with
  | var i =>
      intro varTerms output numbers sets assigned
      simp only [termGraph, truth, assigned, Presentation.termCode]
  | constantK => intro varTerms output numbers sets assigned; exact atoms.k_truth _ _ _
  | constantS => intro varTerms output numbers sets assigned; exact atoms.s_truth _ _ _
  | app f x hf hx =>
      intro varTerms output numbers sets assigned
      have left (a b : N) := hf (fun i => liftTerm 2 (varTerms i)) (.var 1)
        (pushObject (pushObject numbers a) b) sets (by
          intro i
          simpa only [liftTerm, ArithmeticLanguage.renameTerm_value, pushObject] using assigned i)
      have right (a b : N) := hx (fun i => liftTerm 2 (varTerms i)) (.var 0)
        (pushObject (pushObject numbers a) b) sets (by
          intro i
          simpa only [liftTerm, ArithmeticLanguage.renameTerm_value, pushObject] using assigned i)
      simp only [termGraph, truth]
      simp only [left, right, atoms.app_truth]
      simp only [liftTerm,
        ArithmeticLanguage.renameTerm_value, termValue, pushObject, Presentation.termCode]
      constructor
      · rintro ⟨a, b, rfl, rfl, h⟩; exact h
      · intro h; exact ⟨_, _, rfl, rfl, h⟩

/-- Membership of a tuple in an available source set is a genuine arithmetic
formula, with its tuple-code witness introduced locally. -/
def tupleMember (arity : Nat) (setIndex : Nat) (args : Fin (arity + 1) → NTerm) : NFormula :=
  .existsNumber (.conjunction
    (atoms.tupleGraph arity (fun i => liftTerm 1 (args i)) (.var 0)) (.member (.var 0) setIndex))

theorem tupleMember_truth (arity : Nat) (setIndex : Nat)
    (args : Fin (arity + 1) → NTerm) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (atoms.tupleMember arity setIndex args) ↔
      A.member (coding.tuple arity (fun i => termValue A numbers (args i))) (sets setIndex) := by
  simp only [tupleMember, truth, atoms.tupleGraph_truth, liftTerm,
    ArithmeticLanguage.renameTerm_value, termValue, pushObject]
  constructor
  · rintro ⟨x, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

end Definitions
end FregeanECA.Research.Z2Reverse.ArithmeticCodeAtoms


