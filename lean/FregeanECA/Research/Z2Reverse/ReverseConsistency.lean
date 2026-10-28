import FregeanECA.Research.Z2Reverse.InternalSourceModel
import FregeanECA.Part2.ArithmeticInterpretation
import FregeanECA.V2.Theorems

/-!
Relative consistency and equiconsistency derived from the actual source
model construction and the arithmetic proof interpretation. These proofs
do not invoke the earlier unconditional consistency certificates.
-/

namespace FregeanECA.Research.Z2Reverse.ReverseConsistency

open FFL FFL.FirstOrder
open Part2 Guarded Encoded
open scoped FFL.FirstOrder

/-- The constructed source model supplies an actual model of encoded full TF. -/
theorem source_has_functional_model (M : Type) [Nonempty M]
    [Structure ArithmeticEncoding.language M] [Structure.Eq ArithmeticEncoding.language M]
    (source : M↓[ArithmeticEncoding.language] ⊧* ArithmeticEncoding.theory) :
    ∃ target : SmallStruc Guarded.language, target ⊧* fullFunctionalTheory := by
  let native := InternalSourceModel.extractedInterpretation M source
  have full := InternalSourceModel.extracted_fullTF M source
  let : Nonempty _ := ⟨native.constantK⟩
  let := full.full_comprehension.relations_nonempty
  exact ⟨Encoded.taggedModel (copyExpansion native),
    Encoded.taggedModel_valid _ _ (full_functional_axioms_of_conditions _ full)⟩

/-- Equality-model completeness turns the actual source model lift into
relative consistency. The source consistency hypothesis is used explicitly. -/
theorem functional_consistent_of_Z2
    (consistent : Entailment.Consistent ArithmeticEncoding.theory) :
    Entailment.Consistent fullFunctionalTheory := by
  rw [Entailment.consistent_iff_unprovable_bot] at consistent ⊢
  intro proof
  apply consistent
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ source
  obtain ⟨target, satisfies⟩ := source_has_functional_model M source
  exact Theory.Proof.sound proof satisfies

/-- The existing shared-language proof equivalence specializes to consistency. -/
theorem functional_combined_consistency :
    Entailment.Consistent fullFunctionalTheory ↔
      Entailment.Consistent V2.combinedFullTheory := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr ((encoded_falsum_provability FullFunctionalAxiom).symm.trans
    ((V2.functional_combined_full_provability .falsum).trans
      (encoded_falsum_provability (V2.WithECA V2.FCAxiom))))

theorem combined_consistent_of_Z2
    (consistent : Entailment.Consistent ArithmeticEncoding.theory) :
    Entailment.Consistent V2.combinedFullTheory :=
  functional_combined_consistency.mp (functional_consistent_of_Z2 consistent)

/-- The arithmetic interpretation cannot translate a source contradiction
into a consistent full algebraic theory. -/
theorem Z2_consistent_of_algebra
    (consistent : Entailment.Consistent fullAlgebraTheory) :
    Entailment.Consistent ArithmeticEncoding.theory := by
  rw [Entailment.consistent_iff_unprovable_bot] at consistent ⊢
  intro proof
  have encodedFalse : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence .falsum :=
    Entailment.inconsistent_of_provable proof _
  have interpreted := ArithmeticInterpretation.Z2_proof_transfer .falsum encodedFalse
  apply consistent
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ source
  let := Encoded.sorts_of_model source
  let native := Guarded.extracted M
  have realized := Theory.Proof.sound interpreted source
  have valid := (Guarded.sentence_truth (Guarded.extractedRealization M)
    inferInstance (fun _ => inferInstance)
    (ArithmeticInterpretation.interpret .falsum).functional).mp realized
  let objects : Nat → Guarded.Sorted M .object := fun _ => native.applicative.constantK
  let functions : Nat → Guarded.Sorted M .function := fun _ => Classical.choice inferInstance
  let predicates : Positive.PredicateAssignment (fun n => Guarded.Sorted M (.relation n)) :=
    fun _ _ => Classical.choice inferInstance
  exact (ArithmeticInterpretation.interpretation_preserves_falsum
    native.applicative objects predicates).mp
      ((shared_formula_preserves_truth native _ objects functions predicates).mp
        (valid objects functions predicates))

theorem Z2_consistent_of_functional
    (consistent : Entailment.Consistent fullFunctionalTheory) :
    Entailment.Consistent ArithmeticEncoding.theory :=
  Z2_consistent_of_algebra (full_consistency_equivalence.mp consistent)

theorem Z2_consistent_of_combined
    (consistent : Entailment.Consistent V2.combinedFullTheory) :
    Entailment.Consistent ArithmeticEncoding.theory :=
  Z2_consistent_of_functional (functional_combined_consistency.mpr consistent)

theorem Z2_functional_equiconsistent :
    Entailment.Consistent ArithmeticEncoding.theory ↔
      Entailment.Consistent fullFunctionalTheory :=
  ⟨functional_consistent_of_Z2, Z2_consistent_of_functional⟩

theorem Z2_combined_equiconsistent :
    Entailment.Consistent ArithmeticEncoding.theory ↔
      Entailment.Consistent V2.combinedFullTheory :=
  ⟨combined_consistent_of_Z2, Z2_consistent_of_combined⟩

/-- The three active theories have equivalent actual Foundation consistency. -/
theorem three_way_equiconsistency :
    (Entailment.Consistent ArithmeticEncoding.theory ↔
      Entailment.Consistent V2.combinedFullTheory) ∧
    (Entailment.Consistent V2.combinedFullTheory ↔
      Entailment.Consistent fullFunctionalTheory) :=
  ⟨Z2_combined_equiconsistent, functional_combined_consistency.symm⟩

end FregeanECA.Research.Z2Reverse.ReverseConsistency
