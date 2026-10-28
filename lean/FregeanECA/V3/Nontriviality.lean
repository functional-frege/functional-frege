import FregeanECA.V3.Cleaner

/-! The paper's one-object countermodel, including actual nonderivability of
A5 from A1--A4 and the separately recorded definitional equations. -/
namespace FregeanECA.V3.Nontriviality
open FFL FFL.FirstOrder Functional Axioms Guarded Encoded
open scoped FFL.FirstOrder

inductive FirstFour : Formula → Prop where
  | a1 (n : Nat) (p : Formula) : FirstFour (Cleaner.A1 n p)
  | a2 (n : Nat) (t : Cleaner.ApplicationTerm) : FirstFour (Cleaner.A2 n t)
  | a3 : FirstFour Cleaner.A3
  | a4 : FirstFour Cleaner.A4

def Axiom (p : Formula) : Prop := FirstFour p ∨ Cleaner.DefinitionAxiom p
abbrev theory := Encoded.theory Axiom

def singletonAlgebra : Frege.CombinatoryAlgebra Unit where
  apply := fun _ _ => ()
  constant := ()
  distribute := ()
  constant_returns_first_argument := fun _ _ => Subsingleton.elim _ _
  distribute_applies_the_same_argument := fun _ _ _ => rfl

abbrev Relation (n : Nat) := (Fin (n + 1) → Unit) → Prop

def model : Interpretation Unit Unit Relation :=
  copyExpansion (fullRelations singletonAlgebra)

theorem singleton_satisfies_first_four :
    ∀ p, Axiom p → Valid model p := by
  intro p hp o f r
  rcases hp with hp | hp
  · cases hp with
    | a1 n body =>
        exact (Part2.fullRelationalComprehension_truth model n body o f r).mpr
          ((Part2.copyExpansion_comprehends_all_functional_formulas
            singletonAlgebra).comprehend n body o f r)
    | a2 n t =>
        apply (Cleaner.A2_truth model n t o f r).mpr
        exact ⟨(), fun _ => Subsingleton.elim _ _⟩
    | a3 =>
        apply (Cleaner.A3_truth model o f r).mpr
        exact fun _ _ => ⟨fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
    | a4 =>
        apply (functionExtensionality_truth model o f r).mpr
        exact fun _ _ _ => Subsingleton.elim _ _
  · cases hp with
    | evaluation => exact fun _ _ => rfl
    | k =>
        apply (kLaw_truth model o f r).mpr
        exact fun _ _ => Subsingleton.elim _ _
    | s =>
        apply (sLaw_truth model o f r).mpr
        exact fun _ _ _ => rfl

theorem singleton_refutes_A5 : ¬ Valid model Cleaner.A5 := by
  intro h
  obtain ⟨x, y, hxy⟩ :=
    (nontriviality_truth model (fun _ => ()) (fun _ => ())
      (fun _ _ _ => False)).mp (h _ _ _)
  exact hxy (Subsingleton.elim x y)

/-- This checks the countermodel against the literal remaining schemas. -/
theorem countermodel :
    (∀ p, Axiom p → Valid model p) ∧ ¬ Valid model Cleaner.A5 :=
  ⟨singleton_satisfies_first_four, singleton_refutes_A5⟩

/-- The actual first-order theory with A5 removed cannot derive A5. -/
theorem A5_not_provable : ¬ (theory ⊢ sentence Cleaner.A5) := by
  intro proof
  have satisfies := taggedModel_valid model Axiom singleton_satisfies_first_four
  have truth := Theory.Proof.sound proof satisfies
  exact singleton_refutes_A5 ((taggedModel_truth model Cleaner.A5).mp truth)

end FregeanECA.V3.Nontriviality

#print axioms FregeanECA.V3.Nontriviality.A5_not_provable
