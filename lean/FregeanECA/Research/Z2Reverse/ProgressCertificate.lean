import FregeanECA.Research.Z2Reverse.SourceArithmetic
import FregeanECA.Research.Z2Reverse.SourceComprehension
import FregeanECA.Research.Z2Reverse.ArithmeticSentenceTruth
import FregeanECA.Research.Z2Reverse.InternalFreeSubstitution
import FregeanECA.Research.Z2Reverse.InternalConversionFormula
import FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality
import FregeanECA.Research.Z2Reverse.TermCodes
import Lean.Util.CollectAxioms

/-!
Certificate for completed components of the Z2 reverse interpretation.
Internal syntax, capture-avoiding substitution, beta-eta Church-Rosser,
extensionality, the concrete nontrivial ECA, and the fixed arithmetic
conversion formula are checked here. The completed model-independent formula
translation, actual proof transfer, and mutual interpretability are audited
separately by FregeanECA.Certificates.ThreeWay (Certificates/ThreeWay.lean).
See Part2.MutualInterpretability for the final theorem bundle.

Generic lifting and translation theorems retain their explicit hypotheses.
The concrete InternalQuotientNontriviality.eca endpoint requires only an
arbitrary PA model; it has no supplied ECA, extensionality or separation premise.

From lean/: lake env lean --trust=0
  FregeanECA/Research/Z2Reverse/ProgressCertificate.lean
Require exit code zero. Every audited dependency must belong to the exact
standard whitelist below. This gate does not discharge conditional hypotheses.
-/

set_option warningAsError true

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``FregeanECA.Research.Z2Reverse.ArithmeticModel.extracted_modelsZ2,
    ``FregeanECA.Research.Z2Reverse.ArithmeticModel.extracted_proof_truth,
    ``FregeanECA.Research.Z2Reverse.ArithmeticModel.formula_induction,
    ``FregeanECA.Research.Z2Reverse.ArithmeticModel.guarded_assignment_recovery,
    ``FregeanECA.Research.Z2Reverse.ArithmeticModel.sentence_truth_iff,
    ``FregeanECA.Research.Z2Reverse.SourceArithmetic.extracted_models_pa,
    ``FregeanECA.Research.Z2Reverse.SourceArithmetic.extracted_models_iSigmaOne,
    ``FregeanECA.Research.Z2Reverse.InternalLambdaCode.case_iff,
    ``FregeanECA.Research.Z2Reverse.InternalLambdaScope.case_iff,
    ``FregeanECA.Research.Z2Reverse.InternalFreeSubstitution.preserves_scope,
    ``FregeanECA.Research.Z2Reverse.InternalFreeSubstitution.fresh_substitution,
    ``FregeanECA.Research.Z2Reverse.InternalBinderRecursion.Construction.result_defined,
    ``FregeanECA.Research.Z2Reverse.InternalBinderRecursion.Construction.result_lam,
    ``FregeanECA.Research.Z2Reverse.InternalPAInduction.order_induction,
    ``FregeanECA.Research.Z2Reverse.InternalPAInduction.term_induction,
    ``FregeanECA.Research.Z2Reverse.InternalPAInduction.scoped_induction,
    ``FregeanECA.Research.Z2Reverse.InternalBoundShift.preserves_scope,
    ``FregeanECA.Research.Z2Reverse.InternalBoundShift.shift_add,
    ``FregeanECA.Research.Z2Reverse.InternalBoundShift.shift_interchange,
    ``FregeanECA.Research.Z2Reverse.InternalBoundSubstitution.preserves_scope,
    ``FregeanECA.Research.Z2Reverse.InternalBoundSubstitution.substitute_shift,
    ``FregeanECA.Research.Z2Reverse.InternalBoundSubstitution.substitute_comp,
    ``FregeanECA.Research.Z2Reverse.InternalBoundSubstitution.substitute_beta,
    ``FregeanECA.Research.Z2Reverse.InternalBoundSubstitution.shift_beta,
    ``FregeanECA.Research.Z2Reverse.InternalBoundSubstitution.beta_shift_one_identity,
    ``FregeanECA.Research.Z2Reverse.InternalBindFree.preserves_scope,
    ``FregeanECA.Research.Z2Reverse.InternalBindFree.fresh_bindFree,
    ``FregeanECA.Research.Z2Reverse.InternalBindFree.abstractFree_scoped,
    ``FregeanECA.Research.Z2Reverse.InternalAbstraction.substitute_bindFree,
    ``FregeanECA.Research.Z2Reverse.InternalAbstraction.beta_bindFree,
    ``FregeanECA.Research.Z2Reverse.InternalBindFree.bindFree_shift,
    ``FregeanECA.Research.Z2Reverse.InternalBindFree.bindFree_substitute,
    ``FregeanECA.Research.Z2Reverse.InternalBindFree.bindFree_beta,
    ``FregeanECA.Research.Z2Reverse.InternalAvoidsIndex.avoids_iff_shift,
    ``FregeanECA.Research.Z2Reverse.InternalAvoidsIndex.avoids_shift_above,
    ``FregeanECA.Research.Z2Reverse.InternalAvoidsIndex.shift_substitute_of_avoids,
    ``FregeanECA.Research.Z2Reverse.InternalPaths.certificate_splice,
    ``FregeanECA.Research.Z2Reverse.InternalPaths.certificate_reverse,
    ``FregeanECA.Research.Z2Reverse.InternalPaths.reach_induction,
    ``FregeanECA.Research.Z2Reverse.InternalPaths.convert_equivalence,
    ``FregeanECA.Research.Z2Reverse.InternalConfluence.reach_confluent,
    ``FregeanECA.Research.Z2Reverse.InternalConfluence.convert_has_common_reduct,
    ``FregeanECA.Research.Z2Reverse.InternalCommutationLift.commute_of_strongFork,
    ``FregeanECA.Research.Z2Reverse.InternalCombinedConfluence.union_conversion_common,
    ``FregeanECA.Research.Z2Reverse.InternalCombinedConfluence.union_stationary_conversion_iff,
    ``FregeanECA.Research.Z2Reverse.InternalCompleteDevelopment.preserves_scope,
    ``FregeanECA.Research.Z2Reverse.InternalParallelBeta.parallel_defined,
    ``FregeanECA.Research.Z2Reverse.InternalParallelBeta.parallel_induction_pa,
    ``FregeanECA.Research.Z2Reverse.InternalParallelBeta.parallel_substitute,
    ``FregeanECA.Research.Z2Reverse.InternalParallelBeta.continues_to_complete,
    ``FregeanECA.Research.Z2Reverse.InternalParallelBeta.parallel_diamond,
    ``FregeanECA.Research.Z2Reverse.InternalEtaReduction.step_defined,
    ``FregeanECA.Research.Z2Reverse.InternalEtaReduction.step_induction,
    ``FregeanECA.Research.Z2Reverse.InternalEtaReduction.step_substitute,
    ``FregeanECA.Research.Z2Reverse.InternalEtaReduction.step_unshift,
    ``FregeanECA.Research.Z2Reverse.InternalEtaReduction.steps_substitute_replacement,
    ``FregeanECA.Research.Z2Reverse.InternalEtaReduction.step_diamond,
    ``FregeanECA.Research.Z2Reverse.InternalEtaReduction.eta_church_rosser,
    ``FregeanECA.Research.Z2Reverse.InternalBetaEtaCommutation.mixed_fork,
    ``FregeanECA.Research.Z2Reverse.InternalBetaEtaCommutation.commute,
    ``FregeanECA.Research.Z2Reverse.InternalExtensionality.parallel_bindFree,
    ``FregeanECA.Research.Z2Reverse.InternalExtensionality.extensional,
    ``FregeanECA.Research.Z2Reverse.InternalExtensionality.quotient_extensional,
    ``FregeanECA.Research.Z2Reverse.InternalCombinators.K_reduces,
    ``FregeanECA.Research.Z2Reverse.InternalCombinators.S_reduces,
    ``FregeanECA.Research.Z2Reverse.InternalConversionCongruence.convert_app_congr,
    ``FregeanECA.Research.Z2Reverse.InternalConversionCongruence.quotient_K,
    ``FregeanECA.Research.Z2Reverse.InternalConversionCongruence.quotient_S,
    ``FregeanECA.Research.Z2Reverse.InternalTermQuotient.Conversion.decode_onto,
    ``FregeanECA.Research.Z2Reverse.InternalTermQuotient.Conversion.decode_eq_iff,
    ``FregeanECA.Research.Z2Reverse.InternalTermQuotient.Conversion.application_decode,
    ``FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality.betaeta_church_rosser,
    ``FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality.free_names_convert_iff,
    ``FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality.free_name_decode_injective,
    ``FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality.eca,
    ``FregeanECA.Research.Z2Reverse.InternalConversionFormula.conversion_defined,
    ``FregeanECA.Research.Z2Reverse.InternalConversionFormula.conversion_truth,
    ``FregeanECA.Research.Z2Reverse.InternalConversionFormula.native_truth,
    ``FregeanECA.Research.Z2Reverse.InternalConversionFormula.definitions,
    ``FregeanECA.Research.Z2Reverse.RelationCoding.Presentation.codeTruth_iff_truth,
    ``FregeanECA.Research.Z2Reverse.RelationCoding.Presentation.fullComprehension_of_pullbackRepresentation,
    ``FregeanECA.Research.Z2Reverse.FormulaTranslation.Definitions.translate_truth,
    ``FregeanECA.Research.Z2Reverse.ComprehensionTransfer.Definitions.pullbackRepresentation,
    ``FregeanECA.Research.Z2Reverse.ComprehensionTransfer.Definitions.fullComprehension,
    ``FregeanECA.Research.Z2Reverse.ComprehensionTransfer.Definitions.fcAlgebra,
    ``FregeanECA.Research.Z2Reverse.SourceComprehension.extracted_fullComprehension,
    ``FregeanECA.Research.Z2Reverse.SourceComprehension.extracted_fcAlgebra,
    ``FregeanECA.Research.Z2Reverse.TermCodes.classCode_eq_iff_betaEta,
    ``FregeanECA.Research.Z2Reverse.TermCodes.application_matches_quotient]
  for endpoint in endpoints do
    for ax in ← collectAxioms endpoint do
      unless allowed.contains ax do
        throwError "Z2 reverse component certificate rejected at {endpoint}: {ax}"
  logInfo m!"Z2 REVERSE COMPONENTS PASS ({endpoints.length} endpoints; standard whitelist only). Final mutual interpretability is audited by Certificates.ThreeWay."

#print axioms FregeanECA.Research.Z2Reverse.SourceArithmetic.extracted_models_pa
#print axioms FregeanECA.Research.Z2Reverse.ArithmeticModel.sentence_truth_iff
#print axioms FregeanECA.Research.Z2Reverse.InternalBindFree.bindFree_substitute
#print axioms FregeanECA.Research.Z2Reverse.InternalExtensionality.extensional
#print axioms FregeanECA.Research.Z2Reverse.InternalQuotientNontriviality.eca
#print axioms FregeanECA.Research.Z2Reverse.InternalConversionFormula.conversion_defined
#print axioms FregeanECA.Research.Z2Reverse.InternalConversionFormula.definitions
#print axioms FregeanECA.Research.Z2Reverse.SourceComprehension.extracted_fcAlgebra
