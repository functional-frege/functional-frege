import FregeanECA.Part2.FunctionExtensionality

/-! Model reconstruction for the extensional functional presentation.
The object and relation sorts are unchanged. The function sort is recovered
through delta, including its primitive identity and all quantified formulas.
These are model/semantics theorems, not a claim about categories of morphisms.
-/

namespace FregeanECA.V3.ModelReconstruction
open Functional Axioms
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

noncomputable def deltaEquiv (M : Interpretation D F R)
    (tf : Part2.FullTFConditions M) (fe : Valid M functionExtensionality) : F ≃ D :=
  Equiv.ofBijective M.delta
    ⟨(actual_FE_iff_delta_injective tf.toRawTFConditions).mp fe, tf.coverage⟩

theorem deltaEquiv_apply (M : Interpretation D F R)
    (tf : Part2.FullTFConditions M) (fe : Valid M functionExtensionality) (f : F) :
    deltaEquiv M tf fe f = M.delta f := rfl

theorem inverse_application (M : Interpretation D F R)
    (tf : Part2.FullTFConditions M) (fe : Valid M functionExtensionality) (x y : D) :
    M.eval ((deltaEquiv M tf fe).symm x) y = M.applicative.apply x y := by
  rw [tf.evaluation]
  exact congrArg (fun z => M.applicative.apply z y)
    ((deltaEquiv M tf fe).apply_symm_apply x)

theorem algebra_round_trip (M : Positive.Interpretation D R) :
    (copyExpansion M).applicative = M := rfl

theorem formula_round_trip (M : Interpretation D F R)
    (tf : Part2.FullTFConditions M) (fe : Valid M functionExtensionality)
    (p : Formula) (objects : Nat → D) (functions : Nat → F)
    (predicates : Positive.PredicateAssignment R) :
    p.truth M objects functions predicates ↔
      p.truth (copyExpansion M.applicative) objects
        (fun i => M.delta (functions i)) predicates := by
  let target := mergedParameters M objects functions
  have original : Bindings M Interpretability.objectVariables
      Interpretability.functionVariables objects functions target := {
    object := fun i => mergedParameters_even M objects functions i
    function := fun i => mergedParameters_odd M objects functions i }
  have copied : Bindings (copyExpansion M.applicative) Interpretability.objectVariables
      Interpretability.functionVariables objects (fun i => M.delta (functions i)) target := {
    object := original.object
    function := original.function }
  exact (translation_preserves_truth M tf.evaluation tf.coverage
    ((actual_FE_iff_delta_injective tf.toRawTFConditions).mp fe) p
    _ _ _ _ _ _ original).trans
      (copy_expansion_preserves_full_truth M.applicative p _ _ _ _ _ _ copied).symm

theorem reconstruction (M : Interpretation D F R)
    (tf : Part2.FullTFConditions M) (fe : Valid M functionExtensionality) :
    ∃ e : F ≃ D,
      (∀ f, e f = M.delta f) ∧
      (∀ x y, M.eval (e.symm x) y = M.applicative.apply x y) ∧
      (∀ (p : Formula) objects functions predicates,
        p.truth M objects functions predicates ↔
          p.truth (copyExpansion M.applicative) objects
            (fun i => e (functions i)) predicates) :=
  ⟨deltaEquiv M tf fe, deltaEquiv_apply M tf fe,
    inverse_application M tf fe, formula_round_trip M tf fe⟩

end FregeanECA.V3.ModelReconstruction

#print axioms FregeanECA.V3.ModelReconstruction.reconstruction
#print axioms FregeanECA.V3.ModelReconstruction.formula_round_trip
