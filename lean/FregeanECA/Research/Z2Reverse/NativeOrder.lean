import FregeanECA.Research.Z2Reverse.NativeArithmetic

/-! Definable discrete order on arbitrary native Z2 number carriers.
Only explicitly displayed finite native formulas are used for induction. -/

namespace FregeanECA.Research.Z2Reverse.ArithmeticModel

open Part2 SecondOrderArithmetic
open Positive (pushObject)

universe u v
variable {N : Type u} {S : Type v}
variable (A : ArithmeticStructure N S) (model : ModelsZ2 A) (sets : Nat → S)

def strictOrder (x y : N) : Prop := ∃ z, y = A.add x (A.successor z)

include model sets

theorem successor_cases (x : N) : x = A.zero ∨ ∃ y, x = A.successor y := by
  have all := formula_induction A model
    (.disjunction (.equal (.var 0) .zero)
      (.existsNumber (.equal (.var 1) (.successor (.var 0)))))
    (fun _ => A.zero) sets (Or.inl rfl) (by
      intro y _
      exact Or.inr ⟨y, rfl⟩)
  exact all x

theorem add_left_cancel (x y z : N) (same : A.add x y = A.add x z) : y = z := by
  have all := formula_induction A model
    (.forallNumber (.forallNumber (.implies
      (.equal (.add (.var 2) (.var 1)) (.add (.var 2) (.var 0)))
      (.equal (.var 1) (.var 0))))) (fun _ => A.zero) sets (by
        change ∀ y z, A.add A.zero y = A.add A.zero z → y = z
        intro y z h
        simpa only [add_zero_left A model sets] using h) (by
        intro w hw
        change (∀ y z, A.add w y = A.add w z → y = z) at hw
        change ∀ y z, A.add (A.successor w) y = A.add (A.successor w) z → y = z
        intro y z h
        rw [add_successor_left A model sets, add_successor_left A model sets] at h
        exact hw y z (successor_injective A model sets h))
  exact all x y z same

theorem add_successor_ne_self (x z : N) : A.add x (A.successor z) ≠ x := by
  intro h
  have same : A.add x (A.successor z) = A.add x A.zero :=
    h.trans (add_zero_right A model sets x).symm
  exact zero_not_successor A model sets z
    (add_left_cancel A model sets x _ _ same).symm

theorem strictOrder_irrefl (x : N) : ¬ strictOrder A x x := by
  rintro ⟨z, h⟩
  exact add_successor_ne_self A model sets x z h.symm

theorem strictOrder_successor (x y : N) :
    strictOrder A (A.successor x) (A.successor y) ↔ strictOrder A x y := by
  constructor
  · rintro ⟨z, h⟩
    rw [add_successor_left A model sets] at h
    exact ⟨z, successor_injective A model sets h⟩
  · rintro ⟨z, h⟩
    refine ⟨z, ?_⟩
    rw [add_successor_left A model sets, h]

theorem strictOrder_zero_successor (x : N) : strictOrder A A.zero (A.successor x) :=
  ⟨x, (add_zero_left A model sets _).symm⟩

theorem strictOrder_trichotomy (x y : N) :
    strictOrder A x y ∨ x = y ∨ strictOrder A y x := by
  have all := formula_induction A model
    (.forallNumber (.disjunction
      (.existsNumber (.equal (.var 1) (.add (.var 2) (.successor (.var 0)))))
      (.disjunction (.equal (.var 1) (.var 0))
        (.existsNumber (.equal (.var 2) (.add (.var 1) (.successor (.var 0))))))))
    (fun _ => A.zero) sets (by
      change ∀ y, strictOrder A A.zero y ∨ A.zero = y ∨ strictOrder A y A.zero
      intro y
      rcases successor_cases A model sets y with h | ⟨z, rfl⟩
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl (strictOrder_zero_successor A model sets z)) (by
      intro w hw
      change (∀ y, strictOrder A w y ∨ w = y ∨ strictOrder A y w) at hw
      change ∀ y, strictOrder A (A.successor w) y ∨ A.successor w = y ∨
        strictOrder A y (A.successor w)
      intro y
      rcases successor_cases A model sets y with rfl | ⟨z, rfl⟩
      · exact Or.inr (Or.inr (strictOrder_zero_successor A model sets w))
      · rcases hw z with h | h | h
        · exact Or.inl ((strictOrder_successor A model sets w z).mpr h)
        · exact Or.inr (Or.inl (congrArg A.successor h))
        · exact Or.inr (Or.inr ((strictOrder_successor A model sets z w).mpr h)))
  exact all x y

theorem strictOrder_trans {x y z : N}
    (xy : strictOrder A x y) (yz : strictOrder A y z) : strictOrder A x z := by
  rcases xy with ⟨a, rfl⟩
  rcases yz with ⟨b, rfl⟩
  refine ⟨A.add a (A.successor b), ?_⟩
  rw [add_assoc A model sets, add_successor_left A model sets]

theorem strictOrder_add_left (x : N) {y z : N}
    (h : strictOrder A y z) : strictOrder A (A.add x y) (A.add x z) := by
  rcases h with ⟨a, rfl⟩
  exact ⟨a, (add_assoc A model sets x y _).symm⟩

theorem strictOrder_add_right {x y : N} (z : N)
    (h : strictOrder A x y) : strictOrder A (A.add x z) (A.add y z) := by
  rw [add_comm A model sets x z, add_comm A model sets y z]
  exact strictOrder_add_left A model sets z h

theorem zero_le (x : N) : A.zero = x ∨ strictOrder A A.zero x := by
  rcases successor_cases A model sets x with h | ⟨y, rfl⟩
  · exact Or.inl h.symm
  · exact Or.inr (strictOrder_zero_successor A model sets y)

theorem zero_lt_one : strictOrder A A.zero (A.successor A.zero) :=
  strictOrder_zero_successor A model sets A.zero

theorem one_le_of_zero_lt (x : N) (h : strictOrder A A.zero x) :
    A.successor A.zero = x ∨ strictOrder A (A.successor A.zero) x := by
  rcases h with ⟨a, rfl⟩
  rw [add_zero_left A model sets]
  rcases zero_le A model sets a with h | h
  · exact Or.inl (congrArg A.successor h)
  · exact Or.inr ((strictOrder_successor A model sets A.zero a).mpr h)

theorem add_eq_of_lt {x y : N} (h : strictOrder A x y) :
    ∃ z, A.add x z = y := by
  rcases h with ⟨a, ha⟩
  exact ⟨A.successor a, ha.symm⟩

theorem strictOrder_mul_right (x y z : N)
    (xy : strictOrder A x y) (positive : strictOrder A A.zero z) :
    strictOrder A (A.multiply x z) (A.multiply y z) := by
  rcases xy with ⟨a, rfl⟩
  rcases positive with ⟨b, hb⟩
  rw [add_zero_left A model sets] at hb
  subst z
  refine ⟨A.add (A.multiply a (A.successor b)) b, ?_⟩
  rw [multiply_add_left A model sets, multiply_successor_left A model sets,
    add_successor_right A model sets]

end FregeanECA.Research.Z2Reverse.ArithmeticModel
