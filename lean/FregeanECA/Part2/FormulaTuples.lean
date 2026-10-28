import FregeanECA.Syntax
import FregeanECA.Comprehension

/-! Finite tuple binders and conjunctions for relational formula translations.
These are purely logical utilities and have no arithmetic or comprehension
assumptions. Tuple entries occupy the initial variable indices in order. -/
namespace FregeanECA.Part2.FormulaTuples

open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

/-- Existentially bind the initial `n` object variables, in `assignTuple` order. -/
def existsTuple : Nat → Applicative.Formula → Applicative.Formula
  | 0, body => body
  | n + 1, body => existsTuple n (.existsObject body)

theorem existsTuple_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (n : Nat) (p : Applicative.Formula) :
    (existsTuple n p).truth M o r ↔
      ∃ xs : Fin n → D, p.truth M (assignTuple n xs o) r := by
  induction n generalizing p with
  | zero =>
    exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩
  | succ n ih =>
    rw [existsTuple, ih]
    constructor
    · rintro ⟨xs, x, h⟩
      exact ⟨Fin.cases (motive := fun _ => D) x xs, h⟩
    · rintro ⟨xs, h⟩
      exact ⟨fun i => xs i.succ, xs 0, h⟩

/-- Conjoin a finite indexed family; the empty conjunction is truth. -/
def conjunctionTuple : (n : Nat) → (Fin n → Applicative.Formula) → Applicative.Formula
  | 0, _ => .implies .falsum .falsum
  | n + 1, fs => .conjunction (fs 0) (conjunctionTuple n (fun i => fs i.succ))

theorem conjunctionTuple_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (n : Nat) (fs : Fin n → Applicative.Formula) :
    (conjunctionTuple n fs).truth M o r ↔ ∀ i, (fs i).truth M o r := by
  induction n with
  | zero => simp [conjunctionTuple, Applicative.Formula.truth]
  | succ n ih =>
    simp only [conjunctionTuple, Applicative.Formula.truth, ih]
    exact ⟨fun h i => Fin.cases h.1 h.2 i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

/-- Variables beyond the bound tuple retain their original parameter values. -/
@[simp] theorem var_after_assignTuple (M : Interpretation D R) (o : ObjectAssignment D)
    (k : Nat) (xs : Fin k → D) (i : Nat) :
    (Positive.Term.var (i + k)).value M (assignTuple k xs o) = o i := by
  simpa only [Positive.Term.value, Nat.add_comm i k] using assignTuple_after k xs o i

end FregeanECA.Part2.FormulaTuples
