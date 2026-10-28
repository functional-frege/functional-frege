import FregeanECA.AxiomsFunctional
import FregeanECA.Concrete

/-! Exact syntax-level semantic certificates for the paper's FE qualification.
The countermodel satisfies every actual functional axiom. Deductive
nonderivability is obtained separately through first-order soundness. -/

namespace FregeanECA.Axioms
open Functional
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

theorem functionExtensionality_truth (M : Interpretation D F R)
    (objects : Nat → D) (functions : Nat → F) (predicates : Positive.PredicateAssignment R) :
    functionExtensionality.truth M objects functions predicates ↔
      ∀ a b : F, (∀ x, M.eval a x = M.eval b x) → a = b := by
  constructor
  · intro h a b
    exact h b a
  · intro h b a
    exact h a b

/-- Nonempty sorts prevent the universal assignment quantifier from being vacuous. -/
theorem functionExtensionality_valid_iff (M : Interpretation D F R)
    (function_nonempty : Nonempty F) (relation_nonempty : ∀ n, Nonempty (R n)) :
    Valid M functionExtensionality ↔
      ∀ a b : F, (∀ x, M.eval a x = M.eval b x) → a = b := by
  classical
  constructor
  · intro valid
    exact (functionExtensionality_truth M _ _ _).mp
      (valid (fun _ => M.applicative.constantK)
        (fun _ => Classical.choice function_nonempty)
        (fun n _ => Classical.choice (relation_nonempty n)))
  · intro ext objects functions predicates
    exact (functionExtensionality_truth M objects functions predicates).mpr ext

theorem raw_tf_functionExtensionality_valid_iff {M : Interpretation D F R}
    (h : RawTFConditions M) :
    Valid M functionExtensionality ↔
      ∀ a b : F, (∀ x, M.eval a x = M.eval b x) → a = b := by
  obtain ⟨f, _⟩ := h.coverage M.applicative.constantK
  exact functionExtensionality_valid_iff M ⟨f⟩ h.comprehension.relations_nonempty

/-- Under A3--A4, actual FE is equivalent to injective representation. -/
theorem actual_FE_iff_delta_injective {M : Interpretation D F R}
    (h : RawTFConditions M) :
    Valid M functionExtensionality ↔ (∀ a b : F, M.delta a = M.delta b → a = b) :=
  (raw_tf_functionExtensionality_valid_iff h).trans
    h.representation.function_extensionality_iff_injective

/-- The actual FE sentence supplies the function-sort isomorphism, with both
inverse equations and the evaluation equation explicitly recorded. -/
theorem actual_FE_supplies_function_sort_isomorphism {M : Interpretation D F R}
    (h : RawTFConditions M) (fe : Valid M functionExtensionality) :
    ∃ inverse : D → F,
      (∀ f, inverse (M.delta f) = f) ∧
      (∀ a, M.delta (inverse a) = a) ∧
      (∀ a x, M.eval (inverse a) x = M.applicative.apply a x) :=
  function_sort_isomorphism h ((raw_tf_functionExtensionality_valid_iff h).mp fe)

/-- A left inverse of representation already implies the FE sentence. -/
theorem function_sort_inverse_supplies_actual_FE {M : Interpretation D F R}
    (h : RawTFConditions M) (inverse : D → F)
    (left : ∀ f, inverse (M.delta f) = f) :
    Valid M functionExtensionality := by
  apply (actual_FE_iff_delta_injective h).mpr
  intro a b same
  exact (left a).symm.trans ((congrArg inverse same).trans (left b))


theorem actual_FE_iff_function_sort_isomorphism {M : Interpretation D F R}
    (h : RawTFConditions M) :
    Valid M functionExtensionality ↔
      ∃ inverse : D → F,
        (∀ f, inverse (M.delta f) = f) ∧
        (∀ a, M.delta (inverse a) = a) ∧
        (∀ a x, M.eval (inverse a) x = M.applicative.apply a x) := by
  constructor
  · exact actual_FE_supplies_function_sort_isomorphism h
  · rintro ⟨inverse, left, _, _⟩
    exact function_sort_inverse_supplies_actual_FE h inverse left


theorem openDuplicate_refutes_functionExtensionality
    (objects : Nat → OpenObject) (functions : Nat → (OpenObject × Bool))
    (predicates : Positive.PredicateAssignment OpenRelation) :
    ¬ functionExtensionality.truth openDuplicate objects functions predicates := by
  intro truth
  have ext := (functionExtensionality_truth openDuplicate objects functions predicates).mp truth
  let a : OpenObject := Frege.OpenLambda.algebra.constant
  have impossible := ext (a, false) (a, true) (fun _ => rfl)
  have : false = true := congrArg Prod.snd impossible
  cases this

theorem openDuplicate_FE_is_not_valid :
    ¬ Valid openDuplicate functionExtensionality := by
  intro valid
  exact openDuplicate_refutes_functionExtensionality
    (fun _ => Frege.OpenLambda.algebra.constant)
    (fun _ => (Frege.OpenLambda.algebra.constant, false))
    (fun _ _ _ => False) (valid _ _ _)

/-- A concrete model of every actual functional axiom refutes the actual FE formula. -/
theorem actual_functional_axioms_have_an_FE_countermodel :
    (∀ p, FunctionalAxiom p → Valid openDuplicate p) ∧
      ¬ Valid openDuplicate functionExtensionality :=
  ⟨functional_axioms_of_conditions openDuplicate openDuplicate_satisfies_TF,
    openDuplicate_FE_is_not_valid⟩

end FregeanECA.Axioms
