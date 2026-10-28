import FregeanECA.Part2.Models

namespace FregeanECA.Part2
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- The full functional schema restricts to the entire shared classical language. -/
theorem full_functional_implies_full_applicative
    (M : Functional.Interpretation D F R) [Nonempty F]
    (full : HasFullFunctionalComprehension M) : HasFullComprehension M.applicative where
  relations_nonempty := full.relations_nonempty
  comprehend := by
    intro arity formula parameters predicates
    obtain ⟨relation, law⟩ := full.comprehend arity formula.functional parameters
      (fun _ => Classical.choice inferInstance) predicates
    exact ⟨relation, fun arguments => (law arguments).trans
      (shared_formula_preserves_truth M formula _ _ _)⟩

/-- Every full relational model has the canonical copy-function expansion,
including comprehension bodies with primitive function identity. -/
theorem full_applicative_implies_full_copy
    (M : Positive.Interpretation D R) (full : HasFullComprehension M) :
    HasFullFunctionalComprehension (copyExpansion M) where
  relations_nonempty := full.relations_nonempty
  comprehend := by
    intro arity formula parameters functions predicates
    obtain ⟨relation, law⟩ := full.comprehend arity
      (formula.translate (Functional.objectMap (arity+1)) (Functional.functionMap (arity+1)))
      (Functional.mergedParameters (copyExpansion M) parameters functions) predicates
    refine ⟨relation, ?_⟩
    intro arguments
    exact (law arguments).trans
      (copy_expansion_preserves_full_truth M formula _ _ _ _ _ _
        (Functional.merged_bindings (copyExpansion M) (arity+1) arguments parameters functions)).symm

theorem full_tf_reduct_satisfies_full_ts
    {M : Functional.Interpretation D F R} [Nonempty F] (h : FullTFConditions M) :
    FullTSConditions M.applicative where
  toTSConditions := tf_reduct_satisfies_ts h.toTFConditions
  full_comprehension := full_functional_implies_full_applicative M h.full_comprehension

theorem full_ts_expansion_satisfies_full_tf
    {M : Positive.Interpretation D R} (h : FullTSConditions M) :
    FullTFConditions (copyExpansion M) where
  toTFConditions := ts_expansion_satisfies_tf h.toTSConditions
  full_comprehension := full_applicative_implies_full_copy M h.full_comprehension

end FregeanECA.Part2
