import FregeanECA.Research.Z2Reverse.ReverseProofTransfer
import FregeanECA.Research.Z2Reverse.ReverseConsistency
import FregeanECA.Part2.FunctionExtensionality

/-!
Three-way proof interpretations for the actual Part II Fregean theory,
the active V2 relational combinatory theory, and full second-order arithmetic.
Each arrow below transfers actual encoded derivations under a fixed formula
translation. This is mutual interpretability, not bi-interpretability or
identity of the three languages. No FE axiom is required for the main result.
-/
namespace FregeanECA.Part2.MutualInterpretability

open FFL FFL.FirstOrder Guarded
open Research.Z2Reverse
open scoped FFL.FirstOrder

noncomputable def fregeanTranslation (p : Functional.Formula) : SecondOrderArithmetic.Formula :=
  ReverseProofTransfer.translate (Interpretability.translate p)

/-- Every formula of the full Fregean language, including function identity. -/
theorem fregean_to_Z2 (p : Functional.Formula)
    (proof : fullFunctionalTheory ⊢ sentence p) :
    ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence (fregeanTranslation p) :=
  ReverseProofTransfer.algebra_proof_transfer (Interpretability.translate p)
    (full_functional_proof_interprets p proof)

/-- The active V2 algebraic presentation, with its unchanged formula language. -/
theorem algebra_to_Z2 (p : Applicative.Formula)
    (proof : V2.combinedFullTheory ⊢ sentence p.functional) :
    ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence (ReverseProofTransfer.translate p) :=
  ReverseProofTransfer.v2_proof_transfer p proof

theorem Z2_to_fregean (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    fullFunctionalTheory ⊢ sentence (ArithmeticInterpretation.interpret p).functional :=
  ArithmeticInterpretation.Z2_proof_transfer_fregean p proof

theorem Z2_to_algebra (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    V2.combinedFullTheory ⊢ sentence (ArithmeticInterpretation.interpret p).functional :=
  (V2.combined_full_original_provability _).mpr
    (ArithmeticInterpretation.Z2_proof_transfer p proof)

theorem fregean_to_algebra (p : Functional.Formula)
    (proof : fullFunctionalTheory ⊢ sentence p) :
    V2.combinedFullTheory ⊢ sentence (Interpretability.translate p).functional :=
  (V2.combined_full_original_provability _).mpr (full_functional_proof_interprets p proof)

theorem algebra_to_fregean (p : Applicative.Formula)
    (proof : V2.combinedFullTheory ⊢ sentence p.functional) :
    fullFunctionalTheory ⊢ sentence p.functional :=
  (V2.functional_combined_full_provability p).mpr proof

/-- All six directions for the complete source formula grammars. -/
theorem three_way :
    (∀ p, type_of% (fregean_to_Z2 p)) ∧
    (∀ p, type_of% (algebra_to_Z2 p)) ∧
    (∀ p, type_of% (Z2_to_fregean p)) ∧
    (∀ p, type_of% (Z2_to_algebra p)) ∧
    (∀ p, type_of% (fregean_to_algebra p)) ∧
    (∀ p, type_of% (algebra_to_fregean p)) :=
  ⟨fregean_to_Z2, algebra_to_Z2, Z2_to_fregean, Z2_to_algebra,
    fregean_to_algebra, algebra_to_fregean⟩

theorem equiconsistency :
    (Entailment.Consistent ArithmeticEncoding.theory ↔
      Entailment.Consistent V2.combinedFullTheory) ∧
    (Entailment.Consistent V2.combinedFullTheory ↔
      Entailment.Consistent fullFunctionalTheory) :=
  ReverseConsistency.three_way_equiconsistency

/-- The optional FE extension remains interpretable in Z2. -/
theorem FE_to_Z2 (p : Functional.Formula)
    (proof : FunctionExtensionality.fullFETheory ⊢ sentence p) :
    ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence (fregeanTranslation p) :=
  ReverseProofTransfer.algebra_proof_transfer (Interpretability.translate p)
    (FunctionExtensionality.proof_interprets_in_algebra p proof)

theorem Z2_to_FE (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    FunctionExtensionality.fullFETheory ⊢ sentence (ArithmeticInterpretation.interpret p).functional :=
  FunctionExtensionality.original_proof_in_extension _ (Z2_to_fregean p proof)

end FregeanECA.Part2.MutualInterpretability

#print axioms FregeanECA.Part2.MutualInterpretability.three_way
#print axioms FregeanECA.Part2.MutualInterpretability.equiconsistency
#print axioms FregeanECA.Part2.MutualInterpretability.FE_to_Z2
