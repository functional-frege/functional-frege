import FregeanECA.Research.Z2Reverse.NativeFormulaTools
import FregeanECA.Research.Z2Reverse.NativePA
import Foundation.FirstOrder.Arithmetic.IOpen.Basic

/-!
Uniform translation of fixed parameter-free arithmetic formulas, instantiated
at native arithmetic terms. The construction depends only on syntax; it does
not choose a defining formula from any particular model.
-/

namespace FregeanECA.Research.Z2Reverse.NativeAtomTranslation

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic ArithmeticModel
open Part2 Positive
universe u v

abbrev NTerm := SecondOrderArithmetic.Term
abbrev NFormula := SecondOrderArithmetic.Formula

def translateTerm (args : Fin n → NTerm) : Semiterm ℒₒᵣ Empty n → NTerm
  | .bvar i => args i
  | .fvar i => Empty.elim i
  | .func .zero _ => .zero
  | .func .one _ => .successor .zero
  | .func .add terms => .add (translateTerm args (terms 0)) (translateTerm args (terms 1))
  | .func .mul terms => .multiply (translateTerm args (terms 0)) (translateTerm args (terms 1))

def bindTerms (args : Fin n → NTerm) : Fin (n + 1) → NTerm :=
  Fin.cases (.var 0) (fun i => ArithmeticLanguage.renameTerm Nat.succ (args i))

def instantiate : {n : Nat} → Semisentence ℒₒᵣ n → (Fin n → NTerm) → NFormula
  | _, .verum, _ => .implies .falsum .falsum
  | _, .falsum, _ => .falsum
  | _, .rel .eq terms, args => .equal (translateTerm args (terms 0)) (translateTerm args (terms 1))
  | _, .rel .lt terms, args => ArithmeticLanguage.lessFormula
      (translateTerm args (terms 0)) (translateTerm args (terms 1))
  | _, .nrel .eq terms, args => .implies
      (.equal (translateTerm args (terms 0)) (translateTerm args (terms 1))) .falsum
  | _, .nrel .lt terms, args => .implies (ArithmeticLanguage.lessFormula
      (translateTerm args (terms 0)) (translateTerm args (terms 1))) .falsum
  | _, .and p q, args => .conjunction (instantiate p args) (instantiate q args)
  | _, .or p q, args => .disjunction (instantiate p args) (instantiate q args)
  | _, .all p, args => .forallNumber (instantiate p (bindTerms args))
  | _, .exs p, args => .existsNumber (instantiate p (bindTerms args))

variable {N : Type u} {S : Type v} (A : ArithmeticStructure N S)

theorem term_truth (t : Semiterm ℒₒᵣ Empty n) (args : Fin n → NTerm) (numbers : Nat → N) :
    termValue A numbers (translateTerm args t) =
      t.val (s := ArithmeticLanguage.oRingModel A) (fun i => termValue A numbers (args i)) Empty.elim := by
  induction t with
  | bvar i => rfl
  | fvar i => exact Empty.elim i
  | func f terms ih =>
      cases f with
      | zero => rfl
      | one => rfl
      | add => exact congrArg₂ A.add (ih 0) (ih 1)
      | mul => exact congrArg₂ A.multiply (ih 0) (ih 1)

theorem bindTerms_value (args : Fin n → NTerm) (numbers : Nat → N) (x : N) :
    (fun i => termValue A (pushObject numbers x) (bindTerms args i)) =
      (x :> fun i => termValue A numbers (args i)) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [bindTerms, Fin.cases_succ, ArithmeticLanguage.renameTerm_value, pushObject]
  rfl

theorem instantiate_truth (p : Semisentence ℒₒᵣ n) :
    ∀ (args : Fin n → NTerm) (numbers : Nat → N) (sets : Nat → S),
      truth A numbers sets (instantiate p args) ↔
        p.Eval (s := ArithmeticLanguage.oRingModel A)
          (fun i => termValue A numbers (args i)) Empty.elim := by
  induction p with
  | verum => intros; exact iff_of_true (fun h => h) trivial
  | falsum => intros; exact Iff.rfl
  | rel r terms =>
      intro args numbers sets
      cases r with
      | eq =>
          change (termValue A numbers (translateTerm args (terms 0)) =
            termValue A numbers (translateTerm args (terms 1))) ↔ _
          rw [term_truth, term_truth]
          rfl
      | lt =>
          change truth A numbers sets (ArithmeticLanguage.lessFormula _ _) ↔
            ∃ z, (terms 1).val (s := ArithmeticLanguage.oRingModel A)
                (fun i => termValue A numbers (args i)) Empty.elim =
              A.add ((terms 0).val (s := ArithmeticLanguage.oRingModel A)
                (fun i => termValue A numbers (args i)) Empty.elim) (A.successor z)
          rw [ArithmeticLanguage.lessFormula_truth, term_truth, term_truth]
  | nrel r terms =>
      intro args numbers sets
      cases r with
      | eq =>
          change (termValue A numbers (translateTerm args (terms 0)) =
            termValue A numbers (translateTerm args (terms 1)) → False) ↔ _
          rw [term_truth, term_truth]
          rfl
      | lt =>
          change (truth A numbers sets (ArithmeticLanguage.lessFormula _ _) → False) ↔
            ¬ ∃ z, (terms 1).val (s := ArithmeticLanguage.oRingModel A)
                (fun i => termValue A numbers (args i)) Empty.elim =
              A.add ((terms 0).val (s := ArithmeticLanguage.oRingModel A)
                (fun i => termValue A numbers (args i)) Empty.elim) (A.successor z)
          rw [ArithmeticLanguage.lessFormula_truth, term_truth, term_truth]
  | and p q hp hq => intros; exact and_congr (hp _ _ _) (hq _ _ _)
  | or p q hp hq => intros; exact or_congr (hp _ _ _) (hq _ _ _)
  | all p ih =>
      intro args numbers sets
      change (∀ x, truth A (pushObject numbers x) sets (instantiate p (bindTerms args))) ↔
        ∀ x, p.Eval (s := ArithmeticLanguage.oRingModel A)
          (x :> fun i => termValue A numbers (args i)) Empty.elim
      apply forall_congr'
      intro x
      simpa only [bindTerms_value] using ih (bindTerms args) (pushObject numbers x) sets
  | exs p ih =>
      intro args numbers sets
      change (∃ x, truth A (pushObject numbers x) sets (instantiate p (bindTerms args))) ↔
        ∃ x, p.Eval (s := ArithmeticLanguage.oRingModel A)
          (x :> fun i => termValue A numbers (args i)) Empty.elim
      apply exists_congr
      intro x
      simpa only [bindTerms_value] using ih (bindTerms args) (pushObject numbers x) sets

/-- The arithmetic pairing builder is one fixed native formula construction. -/
def pairFormula (a b output : NTerm) : NFormula :=
  instantiate Arithmetic.pairDef.val ![output, a, b]

open Classical in
noncomputable def pair (a b : N) : N :=
  if ∃ z, b = A.add a (A.successor z) then A.add (A.multiply b b) a
  else A.add (A.add (A.multiply a a) a) b

theorem pair_eq_arithmetic (model : ModelsZ2 A) (sets : Nat → S) (a b : N) :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model sets
    pair A a b = Arithmetic.pair a b := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model sets
  have add_def : ∀ x y : N, x + y = A.add x y := fun _ _ => rfl
  have mul_def : ∀ x y : N, x * y = A.multiply x y := fun _ _ => rfl
  have lt_def : ∀ x y : N, (x < y) ↔ ∃ z, y = A.add x (A.successor z) := fun _ _ => Iff.rfl
  by_cases h : a < b
  · have hn := (lt_def a b).mp h
    simp only [pair, Arithmetic.pair, if_pos h, if_pos hn, add_def, mul_def]
  · have hn : ¬∃ z, b = A.add a (A.successor z) := fun hz => h ((lt_def a b).mpr hz)
    simp only [pair, Arithmetic.pair, if_neg h, if_neg hn, add_def, mul_def]

theorem pairFormula_truth (model : ModelsZ2 A) (a b output : NTerm)
    (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (pairFormula a b output) ↔
      termValue A numbers output = pair A (termValue A numbers a) (termValue A numbers b) := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model sets
  rw [pairFormula, instantiate_truth]
  have hv : (fun i => termValue A numbers (![output, a, b] i)) =
      ![termValue A numbers output, termValue A numbers a, termValue A numbers b] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases rfl (fun z => Fin.elim0 z) k
  rw [hv]
  rw [pair_eq_arithmetic A model sets]
  simp

theorem pair_injective (model : ModelsZ2 A) (sets : Nat → S) (a b c d : N)
    (h : pair A a b = pair A c d) : a = c ∧ b = d := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model sets
  have h' : Arithmetic.pair a b = Arithmetic.pair c d := by
    simpa only [pair_eq_arithmetic A model sets] using h
  exact ⟨by simpa using congrArg Arithmetic.pi₁ h', by simpa using congrArg Arithmetic.pi₂ h'⟩

end FregeanECA.Research.Z2Reverse.NativeAtomTranslation
