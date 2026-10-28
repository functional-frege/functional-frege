import FregeanECA.Research.Z2Reverse.ComprehensionTransfer
import FregeanECA.Research.Z2Reverse.ModelTruth

/-! Conditional comprehension transfer directly from an arbitrary model of
the actual source theory. The source-model assumption is genuine encoded Z2;
the remaining assumptions are exactly the finite atomic coding definitions.
No ECA laws, confluence result, or completed reverse interpretation is claimed.
-/

namespace FregeanECA.Research.Z2Reverse.SourceComprehension
open FFL FFL.FirstOrder
open Part2 ArithmeticModel RelationCoding FormulaTranslation
universe u v

variable (M : Type u) [Nonempty M] [Structure ArithmeticEncoding.language M]
  [Structure.Eq ArithmeticEncoding.language M]
  (source : M↓[ArithmeticEncoding.language] ⊧* ArithmeticEncoding.theory)
  {D : Type v} (coding : Presentation D (Number M))
  {application : D → D → D} {k s : D}
  (operations : coding.CodeOperations application k s)
  (atoms : ArithmeticCodeAtoms.Definitions
    (extracted M (sortCorrect_of_model M source)) coding operations)

include atoms

/-- Source Z2 supplies the complete target comprehension scheme, once the
five atomic code graphs have been arithmetically defined. -/
theorem extracted_fullComprehension :
    let A := extracted M (sortCorrect_of_model M source)
    HasFullComprehension (coding.interpretation (membership A) application k s) := by
  obtain ⟨X, hX⟩ := (sortCorrect_of_model M source).inhabited .set
  exact ComprehensionTransfer.Definitions.fullComprehension atoms
    (extracted_modelsZ2 source) (fun _ => ⟨X, hX⟩)

/-- This supplies the FCAlgebra component. `InternalSourceModel` combines it
with the separately proved ECAneq object-algebra construction. -/
theorem extracted_fcAlgebra :
    let A := extracted M (sortCorrect_of_model M source)
    V2.FCAlgebra (coding.interpretation (membership A) application k s) :=
  V2.fullComprehension_implies_fcAlgebra _
    (extracted_fullComprehension M source coding operations atoms)

end FregeanECA.Research.Z2Reverse.SourceComprehension
