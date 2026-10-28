import FregeanECA.Research.Z2Reverse.ArithmeticModel

/-! Formula comprehension and induction for arbitrary native Z2 models.
These statements keep both the number and available-set carriers arbitrary.
In particular, formula induction is not external induction on Lean's `Nat`.
-/

namespace FregeanECA.Research.Z2Reverse.ArithmeticModel

open Part2 SecondOrderArithmetic
open Positive (pushObject)

universe u v
variable {N : Type u} {S : Type v} (A : ArithmeticStructure N S)

theorem renameSets_truth (p : Formula) :
    ∀ map numbers sets, truth A numbers sets (p.renameSets map) ↔
      truth A numbers (fun i => sets (map i)) p := by
  induction p with
  | equal _ _ => intros; exact Iff.rfl
  | member _ _ => intros; exact Iff.rfl
  | setEqual _ _ => intros; exact Iff.rfl
  | falsum => intros; exact Iff.rfl
  | implies _ _ hp hq => intros; exact imp_congr (hp _ _ _) (hq _ _ _)
  | conjunction _ _ hp hq => intros; exact and_congr (hp _ _ _) (hq _ _ _)
  | disjunction _ _ hp hq => intros; exact or_congr (hp _ _ _) (hq _ _ _)
  | existsNumber _ ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallNumber _ ih => intros; exact forall_congr' (fun _ => ih _ _ _)
  | existsSet p ih =>
      intro map numbers sets
      apply exists_congr
      intro X
      refine (ih _ _ _).trans ?_
      have same : (fun i => pushObject sets X (Functional.bindMap map i)) =
          pushObject (fun i => sets (map i)) X := by funext i; cases i <;> rfl
      rw [same]
  | forallSet p ih =>
      intro map numbers sets
      apply forall_congr'
      intro X
      refine (ih _ _ _).trans ?_
      have same : (fun i => pushObject sets X (Functional.bindMap map i)) =
          pushObject (fun i => sets (map i)) X := by funext i; cases i <;> rfl
      rw [same]

theorem comprehension_truth (body : Formula) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (comprehension body) ↔
      ∃ X : S, ∀ x, A.member x X ↔ truth A (pushObject numbers x) sets body := by
  simp only [comprehension, truth, iffF, termValue, pushObject, renameSets_truth]
  constructor
  · rintro ⟨X, h⟩; exact ⟨X, fun x => ⟨(h x).1, (h x).2⟩⟩
  · rintro ⟨X, h⟩; exact ⟨X, fun x => ⟨(h x).mp, (h x).mpr⟩⟩

theorem formula_comprehension (model : ModelsZ2 A) (body : Formula)
    (numbers : Nat → N) (sets : Nat → S) :
    ∃ X : S, ∀ x, A.member x X ↔ truth A (pushObject numbers x) sets body :=
  (comprehension_truth A body numbers sets).mp
    (model _ (Axiom.comprehend body) numbers sets)

theorem set_induction (model : ModelsZ2 A) (sets : Nat → S) (X : S)
    (base : A.member A.zero X)
    (step : ∀ x, A.member x X → A.member (A.successor x) X) :
    ∀ x, A.member x X := by
  have h := model _ Axiom.induction (fun _ => A.zero) sets
  change ∀ Y, (A.member A.zero Y ∧
    (∀ x, A.member x Y → A.member (A.successor x) Y)) → ∀ x, A.member x Y at h
  exact h X ⟨base,step⟩

/-- Every arithmetic formula, including set quantifiers and parameters,
admits induction inside any model of the source Z2 theory. -/
theorem formula_induction (model : ModelsZ2 A) (body : Formula)
    (numbers : Nat → N) (sets : Nat → S)
    (base : truth A (pushObject numbers A.zero) sets body)
    (step : ∀ x, truth A (pushObject numbers x) sets body →
      truth A (pushObject numbers (A.successor x)) sets body) :
    ∀ x, truth A (pushObject numbers x) sets body := by
  obtain ⟨X, represents⟩ := formula_comprehension A model body numbers sets
  have all := set_induction A model sets X ((represents A.zero).mpr base)
    (fun x hx => (represents (A.successor x)).mpr (step x ((represents x).mp hx)))
  exact fun x => (represents x).mp (all x)

theorem zero_not_successor (model : ModelsZ2 A) (sets : Nat → S) (x : N) :
    A.zero ≠ A.successor x :=
  model _ Axiom.zeroNotSuccessor (fun _ => A.zero) sets x

theorem successor_injective (model : ModelsZ2 A) (sets : Nat → S) :
    Function.Injective A.successor := by
  intro x y same
  exact model _ Axiom.successorInjective (fun _ => A.zero) sets y x same

theorem add_zero_left (model : ModelsZ2 A) (sets : Nat → S) (x : N) :
    A.add A.zero x = x :=
  model _ Axiom.additionZero (fun _ => A.zero) sets x

theorem add_successor_left (model : ModelsZ2 A) (sets : Nat → S) (x y : N) :
    A.add (A.successor x) y = A.successor (A.add x y) :=
  model _ Axiom.additionSuccessor (fun _ => A.zero) sets y x

theorem multiply_zero_left (model : ModelsZ2 A) (sets : Nat → S) (x : N) :
    A.multiply A.zero x = A.zero :=
  model _ Axiom.multiplicationZero (fun _ => A.zero) sets x

theorem multiply_successor_left (model : ModelsZ2 A) (sets : Nat → S) (x y : N) :
    A.multiply (A.successor x) y = A.add (A.multiply x y) y :=
  model _ Axiom.multiplicationSuccessor (fun _ => A.zero) sets y x

theorem set_extensionality (model : ModelsZ2 A) (sets : Nat → S) (X Y : S)
    (same : ∀ x, A.member x X ↔ A.member x Y) : X = Y := by
  have h := model _ Axiom.extensionality (fun _ => A.zero) sets
  exact h Y X (fun x => ⟨(same x).mp,(same x).mpr⟩)

end FregeanECA.Research.Z2Reverse.ArithmeticModel
