import FregeanECA.V2.Theorems

/-! The paper's direct algebraic theory: precisely ECA plus full relational
comprehension. The old closure algebra is only a proved library bridge. -/
namespace FregeanECA.V3.RelationalComprehension
open FFL FFL.FirstOrder Guarded Axioms Encoded

abbrev Axiom := V2.WithECA V2.FCComprehensionAxiom
abbrev theory := Encoded.theory Axiom

theorem closure_provability (σ : Sentence language) :
    (theory ⊢ σ) ↔ (V2.combinedFullTheory ⊢ σ) :=
  same_validity_same_proofs _ _ (fun M => by
    rw [V2.withECA_valid_iff, V2.withECA_valid_iff]
    exact and_congr Iff.rfl
      ((V2.fc_comprehension_axioms_iff M).trans
        ((V2.fcAlgebra_iff_fullComprehension M.applicative).symm.trans
          (V2.fc_axioms_iff_conditions M).symm))) σ

theorem consistency_iff_closure :
    Entailment.Consistent theory ↔ Entailment.Consistent V2.combinedFullTheory := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr (closure_provability (⊥ : Sentence language))

end FregeanECA.V3.RelationalComprehension

#print axioms FregeanECA.V3.RelationalComprehension.closure_provability
