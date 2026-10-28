import FregeanECA.Research.Z2Reverse.InternalConversionFormula
import FregeanECA.Research.Z2Reverse.InternalExtensionality
import FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality
import FregeanECA.Research.Z2Reverse.SourceArithmetic
import FregeanECA.Research.Z2Reverse.SourceComprehension

/-!
An actual target model constructed from each source Z2 model. Objects are
classes of internally coded open terms; relations are saturated available
source sets. All atomic formulas, ECA laws, and comprehension are discharged.
The construction does not replace the source number carrier by standard Nat
or its available set carrier by a powerset.
-/

namespace FregeanECA.Research.Z2Reverse.InternalSourceModel

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open Part2 ArithmeticModel RelationCoding FormulaTranslation
open InternalConversionFormula InternalTermQuotient
open scoped FFL.FirstOrder

universe u v

section Native

variable {N : Type u} {S : Type v} (A : ArithmeticStructure N S)
  (model : ModelsZ2 A) (witnessSets : Nat → S)

abbrev Object :=
  letI := ArithmeticLanguage.oRingStructure A
  letI : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  (nativeConversion A model witnessSets).Object

noncomputable def presentation : Presentation (Object A model witnessSets) N := by
  letI := ArithmeticLanguage.oRingStructure A
  letI : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  exact (nativeConversion A model witnessSets).presentation

abbrev Relation (arity : Nat) :=
  (presentation A model witnessSets).Relation (membership A) arity

noncomputable def interpretation :
    Positive.Interpretation (Object A model witnessSets) (Relation A model witnessSets) := by
  letI := ArithmeticLanguage.oRingStructure A
  letI : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  let c := nativeConversion A model witnessSets
  exact c.presentation.interpretation (membership A) c.application
    (c.decode constantK) (c.decode constantS)

/-- The constructed object algebra satisfies all nontrivial ECA laws. -/
theorem eca : Pure.ECAConditions (interpretation A model witnessSets).pure := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := ArithmeticLanguage.models_pa A model witnessSets
  exact InternalQuotientNontriviality.eca (V := N)

/-- Every target comprehension instance comes from an available source set. -/
theorem full_comprehension : HasFullComprehension (interpretation A model witnessSets) := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  exact ComprehensionTransfer.Definitions.fullComprehension
    (InternalConversionFormula.definitions A model witnessSets) model witnessSets

theorem fcAlgebra : V2.FCAlgebra (interpretation A model witnessSets) :=
  V2.fullComprehension_implies_fcAlgebra _ (full_comprehension A model witnessSets)

/-- The concrete nontrivial ECA and the finite full relation algebra together. -/
theorem combinedFullConditions :
    Pure.ECAConditions (interpretation A model witnessSets).pure ∧
      V2.FCAlgebra (interpretation A model witnessSets) :=
  ⟨eca A model witnessSets, fcAlgebra A model witnessSets⟩

theorem fullTS : FullTSConditions (interpretation A model witnessSets) := by
  have algebra := eca A model witnessSets
  exact (V2.fullTSConditions_iff _).mpr
    ⟨⟨algebra.constant, algebra.distribute⟩, algebra.extensional,
      algebra.nontrivial, fcAlgebra A model witnessSets⟩

/-- The canonical function-copy expansion also satisfies the full TF theory. -/
theorem fullTF : FullTFConditions (copyExpansion (interpretation A model witnessSets)) :=
  full_ts_expansion_satisfies_full_tf (fullTS A model witnessSets)

end Native

section Extracted

variable (M : Type u) [Nonempty M] [Structure ArithmeticEncoding.language M]
  [Structure.Eq ArithmeticEncoding.language M]
  (source : M↓[ArithmeticEncoding.language] ⊧* ArithmeticEncoding.theory)

/-- The source's set-sort inhabitation supplies an environment of available sets. -/
noncomputable def extractedSets : Nat → SetObject M := fun _ =>
  ⟨Classical.choose ((sortCorrect_of_model M source).inhabited .set),
    Classical.choose_spec ((sortCorrect_of_model M source).inhabited .set)⟩

noncomputable def extractedInterpretation :=
  interpretation (extracted M (sortCorrect_of_model M source))
    (extracted_modelsZ2 source) (extractedSets M source)

theorem extracted_eca : Pure.ECAConditions (extractedInterpretation M source).pure :=
  eca _ (extracted_modelsZ2 source) (extractedSets M source)

theorem extracted_full_comprehension : HasFullComprehension (extractedInterpretation M source) :=
  full_comprehension _ (extracted_modelsZ2 source) (extractedSets M source)

theorem extracted_fcAlgebra : V2.FCAlgebra (extractedInterpretation M source) :=
  fcAlgebra _ (extracted_modelsZ2 source) (extractedSets M source)

/-- Every actual equality model of encoded Z2 yields ECAneq plus FCAlgebra. -/
theorem extracted_combinedFullConditions :
    Pure.ECAConditions (extractedInterpretation M source).pure ∧
      V2.FCAlgebra (extractedInterpretation M source) :=
  combinedFullConditions _ (extracted_modelsZ2 source) (extractedSets M source)

theorem extracted_fullTS : FullTSConditions (extractedInterpretation M source) :=
  fullTS _ (extracted_modelsZ2 source) (extractedSets M source)

/-- No additional arithmetic, ECA, conversion, or comprehension premise remains. -/
theorem extracted_fullTF : FullTFConditions (copyExpansion (extractedInterpretation M source)) :=
  fullTF _ (extracted_modelsZ2 source) (extractedSets M source)

end Extracted

end FregeanECA.Research.Z2Reverse.InternalSourceModel
