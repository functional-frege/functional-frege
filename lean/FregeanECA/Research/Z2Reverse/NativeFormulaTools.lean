import FregeanECA.Research.Z2Reverse.ArithmeticLanguage

/-! Finite syntactic binders and capture-avoiding renaming in native Z2.
Inductions here are on external finite formulas and arities, never arbitrary
predicates on the source number carrier. -/

namespace FregeanECA.Research.Z2Reverse.NativeFormulaTools
open Part2 SecondOrderArithmetic ArithmeticModel Positive
universe u v
variable {N : Type u} {S : Type v}

def renameNumbers (map : Nat → Nat) : SecondOrderArithmetic.Formula → SecondOrderArithmetic.Formula
  | .equal a b => .equal (ArithmeticLanguage.renameTerm map a) (ArithmeticLanguage.renameTerm map b)
  | .member t i => .member (ArithmeticLanguage.renameTerm map t) i
  | .setEqual i j => .setEqual i j
  | .falsum => .falsum
  | .implies p q => .implies (renameNumbers map p) (renameNumbers map q)
  | .conjunction p q => .conjunction (renameNumbers map p) (renameNumbers map q)
  | .disjunction p q => .disjunction (renameNumbers map p) (renameNumbers map q)
  | .existsNumber p => .existsNumber (renameNumbers (Functional.bindMap map) p)
  | .forallNumber p => .forallNumber (renameNumbers (Functional.bindMap map) p)
  | .existsSet p => .existsSet (renameNumbers map p)
  | .forallSet p => .forallSet (renameNumbers map p)

theorem renameNumbers_truth (A : ArithmeticStructure N S) (p : SecondOrderArithmetic.Formula) :
    ∀ map numbers sets, truth A numbers sets (renameNumbers map p) ↔
      truth A (fun i => numbers (map i)) sets p := by
  induction p with
  | equal a b => intros; simp only [renameNumbers, truth, ArithmeticLanguage.renameTerm_value]
  | member t i => intros; simp only [renameNumbers, truth, ArithmeticLanguage.renameTerm_value]
  | setEqual i j => intros; exact Iff.rfl
  | falsum => intros; exact Iff.rfl
  | implies p q hp hq => intros; exact imp_congr (hp _ _ _) (hq _ _ _)
  | conjunction p q hp hq => intros; exact and_congr (hp _ _ _) (hq _ _ _)
  | disjunction p q hp hq => intros; exact or_congr (hp _ _ _) (hq _ _ _)
  | existsNumber p ih =>
      intro map numbers sets
      apply exists_congr
      intro x
      refine (ih _ _ _).trans ?_
      have same : (fun i => pushObject numbers x (Functional.bindMap map i)) =
          pushObject (fun i => numbers (map i)) x := by funext i; cases i <;> rfl
      rw [same]
  | forallNumber p ih =>
      intro map numbers sets
      apply forall_congr'
      intro x
      refine (ih _ _ _).trans ?_
      have same : (fun i => pushObject numbers x (Functional.bindMap map i)) =
          pushObject (fun i => numbers (map i)) x := by funext i; cases i <;> rfl
      rw [same]
  | existsSet p ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallSet p ih => intros; exact forall_congr' (fun _ => ih _ _ _)

def existsNumbers : Nat → SecondOrderArithmetic.Formula → SecondOrderArithmetic.Formula
  | 0, p => p
  | n + 1, p => existsNumbers n (.existsNumber p)

def forallNumbers : Nat → SecondOrderArithmetic.Formula → SecondOrderArithmetic.Formula
  | 0, p => p
  | n + 1, p => forallNumbers n (.forallNumber p)

theorem existsNumbers_truth (A : ArithmeticStructure N S) (n : Nat)
    (p : SecondOrderArithmetic.Formula) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (existsNumbers n p) ↔
      ∃ xs : Fin n → N, truth A (assignTuple n xs numbers) sets p := by
  induction n generalizing p with
  | zero =>
      constructor
      · intro h; exact ⟨Fin.elim0, h⟩
      · rintro ⟨_, h⟩; exact h
  | succ n ih =>
      rw [existsNumbers, ih]
      change (∃ xs : Fin n → N, ∃ x : N,
        truth A (pushObject (assignTuple n xs numbers) x) sets p) ↔ _
      constructor
      · rintro ⟨xs, x, h⟩
        refine ⟨Fin.cases x xs, ?_⟩
        simpa only [assignTuple_cons] using h
      · rintro ⟨xs, h⟩; exact ⟨fun i => xs i.succ, xs 0, h⟩

theorem forallNumbers_truth (A : ArithmeticStructure N S) (n : Nat)
    (p : SecondOrderArithmetic.Formula) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (forallNumbers n p) ↔
      ∀ xs : Fin n → N, truth A (assignTuple n xs numbers) sets p := by
  induction n generalizing p with
  | zero =>
      constructor
      · intro h _; exact h
      · intro h; exact h Fin.elim0
  | succ n ih =>
      rw [forallNumbers, ih]
      change (∀ xs : Fin n → N, ∀ x : N,
        truth A (pushObject (assignTuple n xs numbers) x) sets p) ↔ _
      constructor
      · intro h xs; exact h (fun i => xs i.succ) (xs 0)
      · intro h xs x; exact h (Fin.cases x xs)

def andFin : (n : Nat) → (Fin n → SecondOrderArithmetic.Formula) → SecondOrderArithmetic.Formula
  | 0, _ => .implies .falsum .falsum
  | n + 1, p => .conjunction (p 0) (andFin n (fun i => p i.succ))

theorem andFin_truth (A : ArithmeticStructure N S) (n : Nat)
    (p : Fin n → SecondOrderArithmetic.Formula) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (andFin n p) ↔ ∀ i, truth A numbers sets (p i) := by
  induction n with
  | zero =>
      constructor
      · intro _ i; exact Fin.elim0 i
      · intro _ h; exact h
  | succ n ih =>
      change (truth A numbers sets (p 0) ∧ truth A numbers sets (andFin n _)) ↔ _
      rw [ih]
      constructor
      · rintro ⟨hzero, hsucc⟩ i; exact Fin.cases hzero hsucc i
      · intro h; exact ⟨h 0, fun i => h i.succ⟩

theorem assignTuple_map {X : Type u} {Y : Type v} (f : X → Y) (n : Nat)
    (xs : Fin n → X) (numbers : Nat → X) :
    (fun i => f (assignTuple n xs numbers i)) =
      assignTuple n (fun i => f (xs i)) (fun i => f (numbers i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext i
      cases i with
      | zero => rfl
      | succ i => exact congrFun (ih (fun j => xs j.succ)) i

theorem assignTuple_shift (n : Nat) (xs : Fin n → N) (numbers : Nat → N) :
    (fun i => assignTuple n xs numbers (i + n)) = numbers := by
  funext i
  simpa only [Nat.add_comm] using assignTuple_after n xs numbers i

end FregeanECA.Research.Z2Reverse.NativeFormulaTools
