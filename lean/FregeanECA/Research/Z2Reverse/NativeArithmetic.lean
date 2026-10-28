import FregeanECA.Research.Z2Reverse.NativeInduction

/-! Elementary arithmetic laws in an arbitrary source Z2 model.
Each induction below names its actual arithmetic formula. No induction over
all external predicates, standardness, or external set domain is assumed.
-/

namespace FregeanECA.Research.Z2Reverse.ArithmeticModel

open Part2 SecondOrderArithmetic
open Positive (pushObject)

universe u v
variable {N : Type u} {S : Type v}
variable (A : ArithmeticStructure N S) (model : ModelsZ2 A) (sets : Nat → S)

include model sets

theorem equation_induction (left right : Term) (numbers : Nat → N)
    (base : termValue A (pushObject numbers A.zero) left =
      termValue A (pushObject numbers A.zero) right)
    (step : ∀ x, termValue A (pushObject numbers x) left =
        termValue A (pushObject numbers x) right →
      termValue A (pushObject numbers (A.successor x)) left =
        termValue A (pushObject numbers (A.successor x)) right) :
    ∀ x, termValue A (pushObject numbers x) left =
      termValue A (pushObject numbers x) right :=
  formula_induction A model (.equal left right) numbers sets base step

theorem add_zero_right (x : N) : A.add x A.zero = x := by
  have all := equation_induction A model sets (.add (.var 0) .zero) (.var 0)
    (fun _ => A.zero) (add_zero_left A model sets A.zero) (by
      intro y hy
      change A.add (A.successor y) A.zero = A.successor y
      rw [add_successor_left A model sets]
      exact congrArg A.successor hy)
  exact all x

theorem add_successor_right (x y : N) :
    A.add x (A.successor y) = A.successor (A.add x y) := by
  have all := equation_induction A model sets
    (.add (.var 0) (.successor (.var 1))) (.successor (.add (.var 0) (.var 1)))
    (fun _ => y) (by
      change A.add A.zero (A.successor y) = A.successor (A.add A.zero y)
      rw [add_zero_left A model sets, add_zero_left A model sets]) (by
      intro z hz
      change A.add z (A.successor y) = A.successor (A.add z y) at hz
      change A.add (A.successor z) (A.successor y) = A.successor (A.add (A.successor z) y)
      rw [add_successor_left A model sets, add_successor_left A model sets, hz])
  exact all x

theorem add_comm (x y : N) : A.add x y = A.add y x := by
  have all := equation_induction A model sets (.add (.var 0) (.var 1))
    (.add (.var 1) (.var 0)) (fun _ => y) (by
      change A.add A.zero y = A.add y A.zero
      rw [add_zero_left A model sets, add_zero_right A model sets]) (by
      intro z hz
      change A.add (A.successor z) y = A.add y (A.successor z)
      rw [add_successor_left A model sets, add_successor_right A model sets]
      exact congrArg A.successor hz)
  exact all x

theorem add_assoc (x y z : N) : A.add (A.add x y) z = A.add x (A.add y z) := by
  have all := equation_induction A model sets
    (.add (.add (.var 0) (.var 1)) (.var 2))
    (.add (.var 0) (.add (.var 1) (.var 2)))
    (pushObject (fun _ => z) y) (by
      change A.add (A.add A.zero y) z = A.add A.zero (A.add y z)
      rw [add_zero_left A model sets, add_zero_left A model sets]) (by
      intro w hw
      change A.add (A.add (A.successor w) y) z = A.add (A.successor w) (A.add y z)
      rw [add_successor_left A model sets, add_successor_left A model sets,
        add_successor_left A model sets]
      exact congrArg A.successor hw)
  exact all x

theorem multiply_zero_right (x : N) : A.multiply x A.zero = A.zero := by
  have all := equation_induction A model sets (.multiply (.var 0) .zero) .zero
    (fun _ => A.zero) (multiply_zero_left A model sets A.zero) (by
      intro y hy
      change A.multiply (A.successor y) A.zero = A.zero
      rw [multiply_successor_left A model sets, add_zero_right A model sets]
      exact hy)
  exact all x

theorem multiply_one_right (x : N) : A.multiply x (A.successor A.zero) = x := by
  have all := equation_induction A model sets (.multiply (.var 0) (.successor .zero))
    (.var 0) (fun _ => A.zero) (multiply_zero_left A model sets _) (by
      intro y hy
      change A.multiply (A.successor y) (A.successor A.zero) = A.successor y
      rw [multiply_successor_left A model sets, add_successor_right A model sets,
        add_zero_right A model sets]
      exact congrArg A.successor hy)
  exact all x

theorem add_left_comm (x y z : N) : A.add x (A.add y z) = A.add y (A.add x z) := by
  rw [← add_assoc A model sets, add_comm A model sets x y, add_assoc A model sets]

theorem add_interchange (a b c d : N) :
    A.add (A.add a b) (A.add c d) = A.add (A.add a c) (A.add b d) := by
  rw [add_assoc A model sets, add_left_comm A model sets b c, add_assoc A model sets]

theorem multiply_successor_right (x y : N) :
    A.multiply x (A.successor y) = A.add (A.multiply x y) x := by
  have all := equation_induction A model sets
    (.multiply (.var 0) (.successor (.var 1)))
    (.add (.multiply (.var 0) (.var 1)) (.var 0)) (fun _ => y) (by
      change A.multiply A.zero (A.successor y) = A.add (A.multiply A.zero y) A.zero
      rw [multiply_zero_left A model sets, multiply_zero_left A model sets,
        add_zero_right A model sets]) (by
      intro z hz
      change A.multiply z (A.successor y) = A.add (A.multiply z y) z at hz
      change A.multiply (A.successor z) (A.successor y) =
        A.add (A.multiply (A.successor z) y) (A.successor z)
      rw [multiply_successor_left A model sets, hz, multiply_successor_left A model sets,
        add_successor_right A model sets, add_successor_right A model sets,
        add_assoc A model sets, add_assoc A model sets, add_comm A model sets z y])
  exact all x

theorem multiply_comm (x y : N) : A.multiply x y = A.multiply y x := by
  have all := equation_induction A model sets (.multiply (.var 0) (.var 1))
    (.multiply (.var 1) (.var 0)) (fun _ => y) (by
      change A.multiply A.zero y = A.multiply y A.zero
      rw [multiply_zero_left A model sets, multiply_zero_right A model sets]) (by
      intro z hz
      change A.multiply (A.successor z) y = A.multiply y (A.successor z)
      rw [multiply_successor_left A model sets, multiply_successor_right A model sets]
      exact congrArg (fun t => A.add t y) hz)
  exact all x

theorem multiply_add_right (x y z : N) :
    A.multiply x (A.add y z) = A.add (A.multiply x y) (A.multiply x z) := by
  have all := equation_induction A model sets
    (.multiply (.var 0) (.add (.var 1) (.var 2)))
    (.add (.multiply (.var 0) (.var 1)) (.multiply (.var 0) (.var 2)))
    (pushObject (fun _ => z) y) (by
      change A.multiply A.zero (A.add y z) =
        A.add (A.multiply A.zero y) (A.multiply A.zero z)
      rw [multiply_zero_left A model sets, multiply_zero_left A model sets,
        multiply_zero_left A model sets, add_zero_right A model sets]) (by
      intro w hw
      change A.multiply w (A.add y z) = A.add (A.multiply w y) (A.multiply w z) at hw
      change A.multiply (A.successor w) (A.add y z) =
        A.add (A.multiply (A.successor w) y) (A.multiply (A.successor w) z)
      rw [multiply_successor_left A model sets, hw,
        multiply_successor_left A model sets, multiply_successor_left A model sets]
      exact add_interchange A model sets _ _ _ _)
  exact all x

theorem multiply_add_left (x y z : N) :
    A.multiply (A.add x y) z = A.add (A.multiply x z) (A.multiply y z) := by
  rw [multiply_comm A model sets (A.add x y) z, multiply_add_right A model sets,
    multiply_comm A model sets z x, multiply_comm A model sets z y]

theorem multiply_assoc (x y z : N) :
    A.multiply (A.multiply x y) z = A.multiply x (A.multiply y z) := by
  have all := equation_induction A model sets
    (.multiply (.multiply (.var 0) (.var 1)) (.var 2))
    (.multiply (.var 0) (.multiply (.var 1) (.var 2)))
    (pushObject (fun _ => z) y) (by
      change A.multiply (A.multiply A.zero y) z = A.multiply A.zero (A.multiply y z)
      rw [multiply_zero_left A model sets, multiply_zero_left A model sets,
        multiply_zero_left A model sets]) (by
      intro w hw
      change A.multiply (A.multiply w y) z = A.multiply w (A.multiply y z) at hw
      change A.multiply (A.multiply (A.successor w) y) z =
        A.multiply (A.successor w) (A.multiply y z)
      rw [multiply_successor_left A model sets, multiply_add_left A model sets,
        multiply_successor_left A model sets, hw])
  exact all x

end FregeanECA.Research.Z2Reverse.ArithmeticModel
