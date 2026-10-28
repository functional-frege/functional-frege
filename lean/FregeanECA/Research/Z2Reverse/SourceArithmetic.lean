import FregeanECA.Research.Z2Reverse.ModelTruth
import FregeanECA.Research.Z2Reverse.NativePA

/-!
From an arbitrary equality model of the actual encoded Z2 theory to an
actual Foundation PA model on its own number sort. Available source sets
supply the comprehension witnesses and induction; the carrier is not Nat.

This discharges the arithmetic-model prerequisite for internal term coding.
It does not construct the target lambda quotient or the ECA interpretation.
-/

namespace FregeanECA.Research.Z2Reverse.SourceArithmetic

open FFL FFL.FirstOrder
open Part2 ArithmeticModel ArithmeticLanguage
universe u

variable (M : Type u) [Nonempty M] [Structure ArithmeticEncoding.language M]
  [Structure.Eq ArithmeticEncoding.language M]

/-- Every actual source Z2 model yields Foundation PA on its number sort,
with source successor, addition, multiplication and definable strict order. -/
theorem extracted_models_pa (source : M↓[ArithmeticEncoding.language] ⊧* ArithmeticEncoding.theory) :
    let A := extracted M (sortCorrect_of_model M source)
    letI := oRingStructure A
    (Number M)↓[ℒₒᵣ] ⊧* Arithmetic.Peano := by
  let typing := sortCorrect_of_model M source
  let A := extracted M typing
  obtain ⟨X, hX⟩ := typing.inhabited .set
  exact models_pa A (extracted_modelsZ2 source) (fun _ => ⟨X, hX⟩)

/-- Foundation's I-sigma-one prerequisite is obtained from the actual Z2
source theory, with no additional native-model or standardness premise. -/
theorem extracted_models_iSigmaOne
    (source : M↓[ArithmeticEncoding.language] ⊧* ArithmeticEncoding.theory) :
    let A := extracted M (sortCorrect_of_model M source)
    letI := oRingStructure A
    (Number M)↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := by
  let typing := sortCorrect_of_model M source
  let A := extracted M typing
  let := oRingStructure A
  let : (Number M)↓[ℒₒᵣ] ⊧* Arithmetic.Peano := extracted_models_pa M source
  infer_instance

end FregeanECA.Research.Z2Reverse.SourceArithmetic
