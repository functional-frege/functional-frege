import FregeanECA.Research.Z2Reverse.NativeInduction
import Foundation.FirstOrder.Arithmetic.Schemata

/-!
An explicit translation of Foundation's ordered arithmetic syntax into the
native second-order arithmetic syntax. Strict order is defined by a positive
additive difference. This lets native Z2 formula induction apply to every
actual Foundation arithmetic formula on an arbitrary number carrier.
-/

namespace FregeanECA.Research.Z2Reverse.ArithmeticLanguage

open FFL FFL.FirstOrder ArithmeticModel
open Part2
open Positive (pushObject)
universe u v

variable {N : Type u} {S : Type v}

/-- The arithmetic language uses only the source's operations. This is a
definition, not a global competing instance or a semiring assumption. -/
@[instance_reducible] def oRingStructure (A : ArithmeticStructure N S) : ORingStructure N where
  zero := A.zero
  one := A.successor A.zero
  add := A.add
  mul := A.multiply
  lt x y := ∃ z, y = A.add x (A.successor z)

@[instance_reducible] def oRingModel (A : ArithmeticStructure N S) : Structure ℒₒᵣ N :=
  @Arithmetic.standardModel N (oRingStructure A)

def renameTerm (map : Nat → Nat) : SecondOrderArithmetic.Term → SecondOrderArithmetic.Term
  | .var i => .var (map i)
  | .zero => .zero
  | .successor t => .successor (renameTerm map t)
  | .add a b => .add (renameTerm map a) (renameTerm map b)
  | .multiply a b => .multiply (renameTerm map a) (renameTerm map b)

theorem renameTerm_value (A : ArithmeticStructure N S) (map : Nat → Nat)
    (numbers : Nat → N) (t : SecondOrderArithmetic.Term) :
    termValue A numbers (renameTerm map t) = termValue A (fun i => numbers (map i)) t := by
  induction t with
  | var i => rfl
  | zero => rfl
  | successor t ih => exact congrArg A.successor ih
  | add a b ha hb => exact congrArg₂ A.add ha hb
  | multiply a b ha hb => exact congrArg₂ A.multiply ha hb

def lessFormula (a b : SecondOrderArithmetic.Term) : SecondOrderArithmetic.Formula :=
  .existsNumber (.equal (renameTerm Nat.succ b)
    (.add (renameTerm Nat.succ a) (.successor (.var 0))))

theorem lessFormula_truth (A : ArithmeticStructure N S) (numbers : Nat → N)
    (sets : Nat → S) (a b : SecondOrderArithmetic.Term) :
    truth A numbers sets (lessFormula a b) ↔
      ∃ z, termValue A numbers b = A.add (termValue A numbers a) (A.successor z) := by
  simp only [lessFormula, truth, termValue, renameTerm_value, pushObject]

def translateTerm (bound : Fin n → Nat) (free : Nat → Nat) :
    Semiterm ℒₒᵣ Nat n → SecondOrderArithmetic.Term
  | .bvar i => .var (bound i)
  | .fvar i => .var (free i)
  | .func .zero _ => .zero
  | .func .one _ => .successor .zero
  | .func .add args => .add (translateTerm bound free (args 0))
      (translateTerm bound free (args 1))
  | .func .mul args => .multiply (translateTerm bound free (args 0))
      (translateTerm bound free (args 1))

def bindBound (bound : Fin n → Nat) : Fin (n + 1) → Nat :=
  Fin.cases 0 (fun i => bound i + 1)

def translateFormula : {n : Nat} → (Fin n → Nat) → (Nat → Nat) →
    Semiformula ℒₒᵣ Nat n → SecondOrderArithmetic.Formula
  | _, _, _, .verum => .implies .falsum .falsum
  | _, _, _, .falsum => .falsum
  | _, bound, free, .rel .eq args =>
      .equal (translateTerm bound free (args 0)) (translateTerm bound free (args 1))
  | _, bound, free, .rel .lt args =>
      lessFormula (translateTerm bound free (args 0)) (translateTerm bound free (args 1))
  | _, bound, free, .nrel .eq args => .implies
      (.equal (translateTerm bound free (args 0)) (translateTerm bound free (args 1))) .falsum
  | _, bound, free, .nrel .lt args => .implies
      (lessFormula (translateTerm bound free (args 0)) (translateTerm bound free (args 1))) .falsum
  | _, bound, free, .and p q =>
      .conjunction (translateFormula bound free p) (translateFormula bound free q)
  | _, bound, free, .or p q =>
      .disjunction (translateFormula bound free p) (translateFormula bound free q)
  | _, bound, free, .all p =>
      .forallNumber (translateFormula (bindBound bound) (fun i => free i + 1) p)
  | _, bound, free, .exs p =>
      .existsNumber (translateFormula (bindBound bound) (fun i => free i + 1) p)

structure Bindings (boundMap : Fin n → Nat) (freeMap : Nat → Nat) (numbers : Nat → N)
    (bound : Fin n → N) (free : Nat → N) : Prop where
  bound : ∀ i, numbers (boundMap i) = bound i
  free : ∀ i, numbers (freeMap i) = free i

theorem Bindings.underBinder {boundMap : Fin n → Nat} {freeMap : Nat → Nat}
    {numbers : Nat → N} {bound : Fin n → N} {free : Nat → N}
    (h : Bindings boundMap freeMap numbers bound free) (x : N) :
    Bindings (bindBound boundMap) (fun i => freeMap i + 1) (pushObject numbers x)
      (x :> bound) free := by
  constructor
  · intro i
    refine Fin.cases rfl (fun j => ?_) i
    exact h.bound j
  · exact h.free

section Semantics
variable (A : ArithmeticStructure N S)

theorem term_truth (t : Semiterm ℒₒᵣ Nat n)
    {boundMap : Fin n → Nat} {freeMap : Nat → Nat} {numbers : Nat → N}
    {bound : Fin n → N} {free : Nat → N}
    (h : Bindings boundMap freeMap numbers bound free) :
    termValue A numbers (translateTerm boundMap freeMap t) =
      t.val (s := oRingModel A) bound free := by
  induction t with
  | bvar i => exact h.bound i
  | fvar i => exact h.free i
  | func f args ih =>
      cases f with
      | zero => rfl
      | one => rfl
      | add => exact congrArg₂ A.add (ih 0) (ih 1)
      | mul => exact congrArg₂ A.multiply (ih 0) (ih 1)

private theorem eval_all (p : Semiformula ℒₒᵣ Nat (n + 1))
    (bound : Fin n → N) (free : Nat → N) :
    Semiformula.Eval (s := oRingModel A) bound free (.all p) ↔
      ∀ x, Semiformula.Eval (s := oRingModel A) (x :> bound) free p := Iff.rfl

private theorem eval_exs (p : Semiformula ℒₒᵣ Nat (n + 1))
    (bound : Fin n → N) (free : Nat → N) :
    Semiformula.Eval (s := oRingModel A) bound free (.exs p) ↔
      ∃ x, Semiformula.Eval (s := oRingModel A) (x :> bound) free p := Iff.rfl

/-- Truth preservation for all actual Foundation arithmetic formulas. The
source and target formulas are finite syntactic objects. -/
theorem formula_truth (p : Semiformula ℒₒᵣ Nat n) :
    ∀ (boundMap : Fin n → Nat) (freeMap : Nat → Nat) (numbers : Nat → N)
      (bound : Fin n → N) (free : Nat → N) (sets : Nat → S),
      Bindings boundMap freeMap numbers bound free →
      (truth A numbers sets (translateFormula boundMap freeMap p) ↔
        p.Eval (s := oRingModel A) bound free) := by
  induction p with
  | verum => intros; exact iff_of_true (fun h => h) trivial
  | falsum => intros; exact Iff.rfl
  | rel r args =>
      intro boundMap freeMap numbers bound free sets h
      cases r with
      | eq =>
          change (termValue A numbers (translateTerm boundMap freeMap (args 0)) =
            termValue A numbers (translateTerm boundMap freeMap (args 1))) ↔
              (args 0).val (s := oRingModel A) bound free =
                (args 1).val (s := oRingModel A) bound free
          rw [term_truth A _ h, term_truth A _ h]
      | lt =>
          change truth A numbers sets (lessFormula _ _) ↔
            ∃ z, (args 1).val (s := oRingModel A) bound free =
              A.add ((args 0).val (s := oRingModel A) bound free) (A.successor z)
          rw [lessFormula_truth, term_truth A _ h, term_truth A _ h]
  | nrel r args =>
      intro boundMap freeMap numbers bound free sets h
      cases r with
      | eq =>
          change (termValue A numbers (translateTerm boundMap freeMap (args 0)) =
            termValue A numbers (translateTerm boundMap freeMap (args 1)) → False) ↔
              ¬ (args 0).val (s := oRingModel A) bound free =
                (args 1).val (s := oRingModel A) bound free
          rw [term_truth A _ h, term_truth A _ h]
      | lt =>
          change (truth A numbers sets (lessFormula _ _) → False) ↔
            ¬ ∃ z, (args 1).val (s := oRingModel A) bound free =
              A.add ((args 0).val (s := oRingModel A) bound free) (A.successor z)
          rw [lessFormula_truth, term_truth A _ h, term_truth A _ h]
  | and p q hp hq =>
      intros; exact and_congr (hp _ _ _ _ _ _ ‹_›) (hq _ _ _ _ _ _ ‹_›)
  | or p q hp hq =>
      intros; exact or_congr (hp _ _ _ _ _ _ ‹_›) (hq _ _ _ _ _ _ ‹_›)
  | all p ih =>
      intro boundMap freeMap numbers bound free sets h
      rw [eval_all]
      exact forall_congr' (fun x => ih _ _ _ _ _ _ (h.underBinder x))
  | exs p ih =>
      intro boundMap freeMap numbers bound free sets h
      rw [eval_exs]
      exact exists_congr (fun x => ih _ _ _ _ _ _ (h.underBinder x))

theorem unary_truth (p : Semiformula ℒₒᵣ Nat 1) (free : Nat → N)
    (sets : Nat → S) (x : N) :
    truth A (pushObject free x) sets (translateFormula Fin.val Nat.succ p) ↔
      p.Eval (s := oRingModel A) ![x] free := by
  apply formula_truth
  constructor
  · intro i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  · intro i; rfl

/-- Native Z2 induction yields induction for every Foundation ordered
arithmetic formula; no induction for arbitrary external predicates is used. -/
theorem formula_induction_lor (model : ModelsZ2 A)
    (sets : Nat → S) (p : Semiformula ℒₒᵣ Nat 1) (free : Nat → N)
    (base : p.Eval (s := oRingModel A) ![A.zero] free)
    (step : ∀ x, p.Eval (s := oRingModel A) ![x] free →
      p.Eval (s := oRingModel A) ![A.successor x] free) :
    ∀ x, p.Eval (s := oRingModel A) ![x] free := by
  have all := ArithmeticModel.formula_induction A model
    (translateFormula Fin.val Nat.succ p) free sets
    ((unary_truth A p free sets A.zero).mpr base)
    (fun x hx => (unary_truth A p free sets (A.successor x)).mpr
      (step x ((unary_truth A p free sets x).mp hx)))
  exact fun x => (unary_truth A p free sets x).mp (all x)

theorem add_one_eq_successor (model : ModelsZ2 A) (sets : Nat → S) (x : N) :
    A.add x (A.successor A.zero) = A.successor x := by
  let body : SecondOrderArithmetic.Formula :=
    .equal (.add (.var 0) (.successor .zero)) (.successor (.var 0))
  have all := ArithmeticModel.formula_induction A model body (fun _ => A.zero) sets
    (ArithmeticModel.add_zero_left A model sets (A.successor A.zero))
    (fun y hy => ?_)
  · exact all x
  · change A.add (A.successor y) (A.successor A.zero) = A.successor (A.successor y)
    change A.add y (A.successor A.zero) = A.successor y at hy
    rw [ArithmeticModel.add_successor_left A model sets, hy]

/-- The literal Foundation successor-induction sentence, with universal
closure over every free parameter, holds in the source arithmetic reduct. -/
theorem models_succInd (model : ModelsZ2 A) (sets : Nat → S)
    (p : Semiformula ℒₒᵣ Nat 1) :
    letI := oRingStructure A
    N↓[ℒₒᵣ] ⊧ (Arithmetic.succInd p).univCl := by
  let := oRingStructure A
  suffices ∀ free : Nat → N,
      p.Eval ![0] free →
      (∀ x, p.Eval ![x] free → p.Eval ![x + 1] free) →
      ∀ x, p.Eval ![x] free by
    simpa [Semiformula.eval_univCl, Arithmetic.succInd, models_iff,
      Matrix.constant_eq_singleton, Semiformula.eval_substs] using this
  intro free base step
  apply formula_induction_lor A model sets p free base
  intro x hx
  have next := step x hx
  change p.Eval (s := oRingModel A) ![A.add x (A.successor A.zero)] free at next
  rw [add_one_eq_successor A model sets] at next
  exact next

/-- All Foundation arithmetic formulas satisfy induction, not just a fixed
complexity fragment. The only premise is native Z2 on the same carriers. -/
theorem models_inductionScheme (model : ModelsZ2 A) (sets : Nat → S) :
    letI := oRingStructure A
    N↓[ℒₒᵣ] ⊧* Arithmetic.InductionScheme ℒₒᵣ Set.univ := by
  let := oRingStructure A
  apply Semantics.ModelsSet.setOf_iff.mpr
  rintro sentence ⟨p, _, rfl⟩
  exact models_succInd A model sets p

end Semantics
end FregeanECA.Research.Z2Reverse.ArithmeticLanguage
