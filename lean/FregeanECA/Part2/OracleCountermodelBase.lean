import FregeanECA.Part2.OracleModel

/-! The concrete definability model satisfies the literal complemented
specification axioms.  The separate finite-table theorem is needed to show
that predicate projection fails in this very model. -/
namespace FregeanECA.Part2.Oracle

/-- Every original specification axiom and every complement instance holds;
the hypothesis is membership in the actual syntactic axiom family. -/
theorem definable_model_satisfies_literal_complemented_axioms (operations) :
    ∀ formula, Generated.ComplementedAxiom formula →
      Axioms.Valid (copyExpansion (definableModel operations)) formula := by
  intro formula axiomInstance
  cases axiomInstance with
  | original old =>
      exact Axioms.specification_axioms_of_conditions _
        (definable_model_satisfies_B_and_C operations).1 formula old
  | complement n =>
      intro objects functions predicates
      obtain ⟨result, correct⟩ :=
        (definable_model_satisfies_B_and_C operations).2.complement n (predicates n 0)
      apply (shared_full_comprehension_truth (copyExpansion (definableModel operations))
        n (complementBody n) objects functions predicates).mpr
      exact ⟨result, fun arguments => (correct arguments).trans
        (complement_body_truth (definableModel operations) n arguments objects predicates).symm⟩

/-- Assembly helper. Its explicit premise is the remaining concrete finite-
table formula truth lemma, not an assumed nondefinability or failure of Q. -/
theorem predicate_projection_fails_of_truth_formula (operations)
    (formula : Applicative.Formula)
    (objects : Positive.ObjectAssignment Nat)
    (predicates : Positive.PredicateAssignment
      (@FirstOrderRelations.Relation language Nat (modelStructure operations)))
    (correct : ∀ sentence : FFL.FirstOrder.Sentence language,
      formula.truth (definableModel operations)
        (Positive.assignTuple 1 (fun _ => Encodable.encode sentence) objects) predicates ↔
      sentence.Evalb (s := modelStructure operations) Fin.elim0) :
    ¬ PredicateProjection (definableModel operations) := by
  intro projection
  have base := definable_model_satisfies_B_and_C operations
  have full := classical_closure_implies_full_comprehension (definableModel operations)
    base.1.combinatory ⟨base.1.closure, base.2, projection⟩
  obtain ⟨relation, represented⟩ := full.comprehend 0 formula objects predicates
  apply no_relation_correct_on_sentence_codes operations
  exact ⟨relation, fun sentence =>
    (represented (fun _ => Encodable.encode sentence)).trans (correct sentence)⟩

end FregeanECA.Part2.Oracle
