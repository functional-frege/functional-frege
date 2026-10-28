import FregeanECA.Concrete
import Mathlib.Logic.Denumerable

/-! Transport the already constructed open lambda algebra to the natural
numbers.  The bijection is a cardinality construction, not a decision procedure
for beta-eta equality. -/
namespace FregeanECA.Part2.NaturalECA

open Frege

private def termCode : OpenLambda.Term n → Nat
  | .var i => Nat.pair 0 i.val
  | .coeff a => Nat.pair 1 a
  | .app f x => Nat.pair 2 (Nat.pair (termCode f) (termCode x))
  | .lam body => Nat.pair 3 (termCode body)

private theorem termCode_injective {n : Nat} :
    Function.Injective (termCode (n := n)) := by
  intro left right same
  induction left with
  | var i =>
      cases right <;> simp only [termCode, Nat.pair_eq_pair] at same <;> try omega
      exact congrArg Program.var (Fin.ext same.2)
  | coeff a =>
      cases right <;> simp only [termCode, Nat.pair_eq_pair] at same <;> try omega
      exact congrArg Program.coeff same.2
  | app f x ihf ihx =>
      cases right <;> simp only [termCode, Nat.pair_eq_pair] at same <;> try omega
      exact congr (congrArg Program.app (ihf same.2.1)) (ihx same.2.2)
  | lam body ih =>
      cases right <;> simp only [termCode, Nat.pair_eq_pair] at same <;> try omega
      exact congrArg Program.lam (ih same.2)

private instance termCountable (n : Nat) : Countable (OpenLambda.Term n) :=
  ⟨⟨termCode, termCode_injective⟩⟩

instance objectCountable : Countable OpenObject := by
  change Countable (Quotient (OpenLambda.equalitySetoid 0))
  infer_instance

instance objectInfinite : Infinite OpenObject :=
  Infinite.of_injective (fun n : Nat => OpenLambda.termClass (.coeff n))
    (fun _ _ h => OpenLambda.the_free_name_classes_form_an_injection _ _ h)

noncomputable def objectEquivalence : OpenObject ≃ Nat :=
  Classical.choice (inferInstance : Nonempty (OpenObject ≃ Nat))

noncomputable def algebra : CombinatoryAlgebra Nat where
  apply := fun f x => objectEquivalence (OpenLambda.algebra.apply
    (objectEquivalence.symm f) (objectEquivalence.symm x))
  constant := objectEquivalence OpenLambda.algebra.constant
  distribute := objectEquivalence OpenLambda.algebra.distribute
  constant_returns_first_argument := by
    intro x y
    simp [OpenLambda.algebra.constant_returns_first_argument]
  distribute_applies_the_same_argument := by
    intro f g x
    simp [OpenLambda.algebra.distribute_applies_the_same_argument]

theorem extensional : algebra.IsExtensional := by
  intro f g agree
  apply objectEquivalence.symm.injective
  apply OpenLambda.the_constructed_open_term_algebra_is_extensional
  intro x
  have h := congrArg objectEquivalence.symm (agree (objectEquivalence x))
  simpa only [algebra, Equiv.symm_apply_apply] using h

theorem nontrivial : ∃ a b : Nat, a ≠ b := ⟨0, 1, Nat.zero_ne_one⟩

/-- No supplied-model premise: the carrier really is Nat. -/
theorem natural_extensional_combinatory_algebra :
    algebra.IsExtensional ∧ ∃ a b : Nat, a ≠ b := ⟨extensional, nontrivial⟩

end FregeanECA.Part2.NaturalECA

