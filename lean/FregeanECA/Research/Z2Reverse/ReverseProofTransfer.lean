import FregeanECA.Research.Z2Reverse.GuardedFormulaTranslation
import FregeanECA.Research.Z2Reverse.InternalSourceModel
import FregeanECA.Research.Z2Reverse.ArithmeticSentenceTruth
import FregeanECA.V2.Theorems

/-!
The fixed reverse interpretation into the actual guarded Z2 theory. Every
formula is translated by fixed syntax, with finite guards on its free
relation parameters. Soundness in the internally coded source model and
equality-model completeness transfer actual Foundation derivations.
-/
namespace FregeanECA.Research.Z2Reverse.ReverseProofTransfer
open FFL FFL.FirstOrder
open Part2 ArithmeticModel Positive
open scoped FFL.FirstOrder

/-- Fixed model-independent arithmetic translation of the complete shared language. -/
noncomputable def translate : Applicative.Formula → SecondOrderArithmetic.Formula :=
  GuardedFormulaTranslation.translate

universe u v

/-- Native validity is exactly validity in the constructed available-set model. -/
theorem native_validity_iff {N : Type u} {S : Type v} (A : ArithmeticStructure N S)
    (model : ModelsZ2 A) (witnessSets : Nat → S) (p : Applicative.Formula) :
    (∀ numbers sets, truth A numbers sets (translate p)) ↔
      ∀ objects predicates,
        p.truth (InternalSourceModel.interpretation A model witnessSets) objects predicates := by
  rw [translate, GuardedFormulaTranslation.translate_eq A model witnessSets p]
  exact GuardedFormulaTranslation.Definitions.guarded_validity_iff
    (InternalConversionFormula.definitions A model witnessSets) p
    (fun arity _ => Classical.choice
      ((InternalSourceModel.full_comprehension A model witnessSets).relations_nonempty arity))

/-- Sentence-level truth preservation in every actual source equality model. -/
theorem source_semantics (M : Type u) [Nonempty M]
    [Structure ArithmeticEncoding.language M] [Structure.Eq ArithmeticEncoding.language M]
    (source : M↓[ArithmeticEncoding.language] ⊧* ArithmeticEncoding.theory)
    (p : Applicative.Formula) :
    (ArithmeticEncoding.sentence (translate p)).Realize M ↔
      ∀ objects predicates,
        p.truth (InternalSourceModel.extractedInterpretation M source) objects predicates :=
  (ArithmeticModel.sentence_truth_iff (sortCorrect_of_model M source) (translate p)).trans
    (native_validity_iff _ (extracted_modelsZ2 source) (InternalSourceModel.extractedSets M source) p)

/-- Every actual full-algebra derivation transfers to actual encoded Z2. -/
theorem algebra_proof_transfer (p : Applicative.Formula)
    (proof : Part2.fullAlgebraTheory ⊢ Guarded.sentence p.functional) :
    ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence (translate p) := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ source
  apply (source_semantics M source p).mpr
  let native := InternalSourceModel.extractedInterpretation M source
  let : Nonempty (InternalSourceModel.Object
      (extracted M (sortCorrect_of_model M source)) (extracted_modelsZ2 source)
      (InternalSourceModel.extractedSets M source)) := ⟨native.constantK⟩
  let : ∀ arity, Nonempty (InternalSourceModel.Relation
      (extracted M (sortCorrect_of_model M source)) (extracted_modelsZ2 source)
      (InternalSourceModel.extractedSets M source) arity) :=
    (InternalSourceModel.extracted_full_comprehension M source).relations_nonempty
  let expanded := copyExpansion native
  have targetModel := Encoded.taggedModel_valid expanded AlgebraAxiom
    (algebra_axioms_of_conditions expanded (InternalSourceModel.extracted_fullTS M source))
  have holds := (Encoded.taggedModel_truth expanded p.functional).mp
    (Theory.Proof.sound_small proof targetModel)
  exact (Encoded.shared_validity expanded p).mp holds

/-- The active V2 ECAneq + FCAlgebra presentation has the same reverse translation. -/
theorem v2_proof_transfer (p : Applicative.Formula)
    (proof : V2.combinedFullTheory ⊢ Guarded.sentence p.functional) :
    ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence (translate p) :=
  algebra_proof_transfer p ((V2.combined_full_original_provability _).mp proof)

/-- The reverse interpretation sends falsity to a formula equivalent to falsity. -/
theorem translation_preserves_falsum {N : Type u} {S : Type v}
    (A : ArithmeticStructure N S) (numbers : Nat → N) (sets : Nat → S) :
    truth A numbers sets (translate .falsum) ↔ False :=
  GuardedFormulaTranslation.falsum_truth A numbers sets

end FregeanECA.Research.Z2Reverse.ReverseProofTransfer
