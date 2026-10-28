import FregeanECA.Part2.ArithmeticFreeVariables

/-! Universal closure of the free number-variable prefix. Set parameters
remain free and are subsequently universally closed by the target sentence
encoding. These facts are purely about the source arithmetic syntax. -/
namespace FregeanECA.Part2.SecondOrderArithmetic
open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

def closeNumbers : Nat → Formula → Formula
  | 0, p => p
  | n + 1, p => .forallNumber (closeNumbers n p)

theorem closeNumbers_numberBound (n : Nat) (p : Formula) :
    (closeNumbers n p).numberBound = p.numberBound - n := by
  induction n with
  | zero => simp [closeNumbers]
  | succ n ih => simp [closeNumbers, Formula.numberBound, ih, Nat.sub_sub]

theorem closeNumbers_valid_iff {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (n : Nat) (p : Formula) :
    Valid A (closeNumbers n p) ↔ Valid A p := by
  induction n with
  | zero => exact Iff.rfl
  | succ n ih =>
    constructor
    · intro closed
      apply ih.mp
      intro numbers sets
      have same : pushObject (fun i => numbers (i + 1)) (numbers 0) = numbers := by
        funext i
        cases i <;> rfl
      have holds := closed (fun i => numbers (i + 1)) sets (numbers 0)
      simpa only [same] using holds
    · intro valid numbers sets x
      exact ih.mpr valid (pushObject numbers x) sets

def closeAllNumbers (p : Formula) : Formula := closeNumbers p.numberBound p

@[simp] theorem closeAllNumbers_numberBound (p : Formula) :
    (closeAllNumbers p).numberBound = 0 := by
  simp [closeAllNumbers, closeNumbers_numberBound]

theorem closeAllNumbers_valid_iff {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (p : Formula) :
    Valid A (closeAllNumbers p) ↔ Valid A p :=
  closeNumbers_valid_iff A p.numberBound p

theorem closeAllNumbers_valid {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (p : Formula) (valid : Valid A p) :
    Valid A (closeAllNumbers p) :=
  (closeAllNumbers_valid_iff A p).mpr valid

end FregeanECA.Part2.SecondOrderArithmetic
