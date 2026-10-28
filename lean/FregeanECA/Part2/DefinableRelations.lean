import FregeanECA.Part2.GeneratedRelations
import Foundation.FirstOrder.Basic.Definability

/-! First-order-definable relations, with actual finite formula witnesses.
These models satisfy B1--B5 and C.  Failure of Q is a separate obligation.
-/
namespace FregeanECA.Part2.FirstOrderRelations

open Frege FFL FFL.FirstOrder
universe u v
variable (L : Language.{u}) (D : Type v) [Structure L D]

def Relation (arity : Nat) :=
  {predicate : (Fin (arity + 1) → D) → Prop // L.Definable predicate}

def interpretation (A : CombinatoryAlgebra D) :
    Positive.Interpretation D (Relation L D) where
  apply := A.apply
  constantK := A.constant
  constantS := A.distribute
  satisfies := fun _ relation xs => relation.val xs

variable {L D} [L.Eq] [Structure.Eq L D]

theorem iterated_application_definable (A : CombinatoryAlgebra D)
    [L.DefinableFunction₂ A.apply] (length : Nat)
    (code : (Fin k → D) → D) (hcode : L.DefinableFunction code)
    (arguments : Fin length → (Fin k → D) → D)
    (harguments : ∀ i, L.DefinableFunction (arguments i)) :
    L.DefinableFunction (fun values => Positive.applyArguments
      (interpretation L D A) (code values) (fun i => arguments i values)) := by
  induction length generalizing code with
  | zero => exact hcode
  | succ n ih =>
      exact ih (fun values => A.apply (code values) (arguments 0 values))
        (Language.DefinableFunction₂.comp hcode (harguments 0))
        (fun i => arguments i.succ) (fun i => harguments i.succ)

/-- Move the last argument to the front, matching the library's bound-variable
convention for first-order quantification. -/
theorem last_argument_definable {arity : Nat}
    (predicate : (Fin (arity + 2) → D) → Prop) (h : L.Definable predicate) :
    L.Definable (fun values : Fin (arity + 2) → D =>
      predicate (Positive.appendLast (fun i => values i.succ) (values 0))) := by
  apply Language.Definable.of_iff
    (h.retraction (Fin.lastCases 0 (fun i => i.succ)))
  intro values
  apply iff_of_eq
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem positive_closure (A : CombinatoryAlgebra D)
    [L.DefinableFunction₂ A.apply] :
    Positive.PositiveClosure (interpretation L D A) where
  equality := ⟨⟨fun xs => xs 0 = xs 1, inferInstance⟩, fun _ => Iff.rfl⟩
  preimage := by
    intro source target relation programs
    refine ⟨⟨_, Language.Definable.substitution relation.property ?_⟩, fun _ => Iff.rfl⟩
    intro i
    exact iterated_application_definable A (target+1) (fun _ => programs i)
      (Language.DefinableFunction.const _) (fun j xs => xs j)
      (fun j => Language.DefinableFunction.projection j)
  intersection := fun _ left right =>
    ⟨⟨_, left.property.and right.property⟩, fun _ => Iff.rfl⟩
  union := fun _ left right =>
    ⟨⟨_, left.property.or right.property⟩, fun _ => Iff.rfl⟩
  existsProjection := fun _ relation =>
    ⟨⟨_, Language.Definable.exs (last_argument_definable _ relation.property)⟩,
      fun _ => Iff.rfl⟩
  forallProjection := fun _ relation =>
    ⟨⟨_, Language.Definable.all (last_argument_definable _ relation.property)⟩,
      fun _ => Iff.rfl⟩

theorem complemented (A : CombinatoryAlgebra D) :
    ComplementClosure (interpretation L D A) where
  complement := fun _ relation => ⟨⟨_, relation.property.not⟩, fun _ => Iff.rfl⟩

theorem specification_with_complements (A : CombinatoryAlgebra D)
    [L.DefinableFunction₂ A.apply] (ext : A.IsExtensional)
    (nontrivial : ∃ a b : D, a ≠ b) :
    TSConditions (interpretation L D A) ∧
      ComplementClosure (interpretation L D A) :=
  ⟨{combinatory := ⟨A.constant_returns_first_argument, A.distribute_applies_the_same_argument⟩
    extensional := ext
    nontrivial := nontrivial
    closure := positive_closure A}, complemented A⟩

/-- Every actual first-order formula, including parameters, has its relation.
No impredicative comprehension is being assumed here. -/
theorem formula_relation (A : CombinatoryAlgebra D)
    (formula : Semiformula L D (arity+1)) :
    ∃ relation : Relation L D arity, ∀ values,
      (interpretation L D A).satisfies arity relation values ↔
        formula.Eval values id := by
  exact ⟨⟨fun values => formula.Eval values id, ⟨formula, fun _ => Iff.rfl⟩⟩,
    fun _ => Iff.rfl⟩

end FregeanECA.Part2.FirstOrderRelations


