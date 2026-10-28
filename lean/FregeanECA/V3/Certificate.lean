import FregeanECA.V3.Cleaner
import FregeanECA.V3.ModelReconstruction
import FregeanECA.V3.Specifications
import FregeanECA.V3.RelationalComprehension
import FregeanECA.V3.Nontriviality
import FregeanECA.V3.PaperResults
import FregeanECA.V3.SuccessorVerification
import FregeanECA.Part2.MutualInterpretability
import FregeanECA.Part2.ProgramEquations
import Lean.Util.CollectAxioms

/-!
Focused certificate for the actual cleaner A1--A5 theory, nontrivial
extensional combinatory algebra with full relational comprehension, and Z2.
The translations act on the complete source grammars and transfer actual
Foundation derivations. This is not a bi-interpretability claim about Z2.

Run from lean/: lake env lean --trust=0 FregeanECA/V3/Certificate.lean
The final audit rejects admissions and every extra mathematical axiom.
-/
set_option warningAsError true

namespace FregeanECA.V3.Certificate

open FFL FFL.FirstOrder Guarded Encoded Part2
open scoped FFL.FirstOrder

abbrev TF := Cleaner.theory
abbrev TR := RelationalComprehension.theory
abbrev Z2 := ArithmeticEncoding.theory

/-- The cleaner theory and the algebraic presentation agree on every sentence
expressed using objects, application and relations. -/
theorem shared_algebra_provability (p : Applicative.Formula) :
    (TF ⊢ sentence p.functional) ↔ (TR ⊢ sentence p.functional) :=
  (Cleaner.provability_iff_fullFE _).trans
    ((FunctionExtensionality.shared_v2_provability p).trans
      (RelationalComprehension.closure_provability _).symm)

theorem cleaner_to_Z2 (p : Functional.Formula)
    (proof : TF ⊢ sentence p) :
    Z2 ⊢ ArithmeticEncoding.sentence (MutualInterpretability.fregeanTranslation p) :=
  MutualInterpretability.FE_to_Z2 p ((Cleaner.provability_iff_fullFE _).mp proof)

theorem algebra_to_Z2 (p : Applicative.Formula)
    (proof : TR ⊢ sentence p.functional) :
    Z2 ⊢ ArithmeticEncoding.sentence (Research.Z2Reverse.ReverseProofTransfer.translate p) :=
  MutualInterpretability.algebra_to_Z2 p
    ((RelationalComprehension.closure_provability _).mp proof)

theorem Z2_to_cleaner (p : SecondOrderArithmetic.Formula)
    (proof : Z2 ⊢ ArithmeticEncoding.sentence p) :
    TF ⊢ sentence (ArithmeticInterpretation.interpret p).functional :=
  (Cleaner.provability_iff_fullFE _).mpr (MutualInterpretability.Z2_to_FE p proof)

theorem Z2_to_algebra (p : SecondOrderArithmetic.Formula)
    (proof : Z2 ⊢ ArithmeticEncoding.sentence p) :
    TR ⊢ sentence (ArithmeticInterpretation.interpret p).functional :=
  (RelationalComprehension.closure_provability _).mpr
    (MutualInterpretability.Z2_to_algebra p proof)

theorem cleaner_to_algebra (p : Functional.Formula)
    (proof : TF ⊢ sentence p) :
    TR ⊢ sentence (Interpretability.translate p).functional :=
  (RelationalComprehension.closure_provability _).mpr
    (FunctionExtensionality.proof_interprets_in_v2 p
      ((Cleaner.provability_iff_fullFE _).mp proof))

theorem algebra_to_cleaner (p : Applicative.Formula)
    (proof : TR ⊢ sentence p.functional) : TF ⊢ sentence p.functional :=
  (shared_algebra_provability p).mpr proof

/-- All six arrows concern the actual V3 theory, not the archived V2 Fregean
axiom set. Function identity is included in the functional source grammar. -/
theorem three_way :
    (∀ p, type_of% (cleaner_to_Z2 p)) ∧
    (∀ p, type_of% (algebra_to_Z2 p)) ∧
    (∀ p, type_of% (Z2_to_cleaner p)) ∧
    (∀ p, type_of% (Z2_to_algebra p)) ∧
    (∀ p, type_of% (cleaner_to_algebra p)) ∧
    (∀ p, type_of% (algebra_to_cleaner p)) :=
  ⟨cleaner_to_Z2, algebra_to_Z2, Z2_to_cleaner, Z2_to_algebra,
    cleaner_to_algebra, algebra_to_cleaner⟩

theorem consistency_iff_fullFE :
    Entailment.Consistent TF ↔ Entailment.Consistent FunctionExtensionality.fullFETheory := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr (Cleaner.provability_iff_fullFE (⊥ : Sentence language))

theorem consistency_iff_algebra :
    Entailment.Consistent TF ↔ Entailment.Consistent TR := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr ((encoded_falsum_provability Cleaner.Axiom).symm.trans
    ((shared_algebra_provability .falsum).trans
      (encoded_falsum_provability RelationalComprehension.Axiom)))

/-- This follows the checked interpretation/model-transfer consistency chain;
it does not simply pair independently known consistency theorems. -/
theorem equiconsistency :
    (Entailment.Consistent Z2 ↔ Entailment.Consistent TR) ∧
    (Entailment.Consistent TR ↔ Entailment.Consistent TF) :=
  ⟨MutualInterpretability.equiconsistency.1.trans
      RelationalComprehension.consistency_iff_closure.symm,
    consistency_iff_algebra.symm⟩

theorem consistent : Entailment.Consistent TF :=
  consistency_iff_fullFE.mpr FunctionExtensionality.consistent

/-- Relational comprehension adds no consequence anywhere in the entire pure
classical applicative language, not only equations between named programs. -/
theorem pure_conservativity (p : Pure.Formula) :
    (Bare.theory ⊢ Bare.sentence p) ↔ (TF ⊢ sentence p.functional) :=
  (FunctionExtensionality.pure_conservativity p).trans
    (Cleaner.provability_iff_fullFE _).symm

/-- Open lambda terms with arbitrary free names, under the fixed K/S
translation; the resulting equations are universally closed. -/
theorem program_equations (M N : Frege.OpenLambda.Term 0) :
    (TF ⊢ sentence (LambdaInterpretation.equation M N).functional) ↔
      Frege.OpenLambda.BetaEtaConvertible M N :=
  (pure_conservativity (LambdaInterpretation.equation M N)).symm.trans
    (ProgramEquations.bare_program_equation_iff M N)

/-- Both alternatives T in {TF, TR} in the paper's exact-equation theorem. -/
theorem program_equations_both (M N : Frege.OpenLambda.Term 0) :
    ((TF ⊢ sentence (LambdaInterpretation.equation M N).functional) ↔
      Frege.OpenLambda.BetaEtaConvertible M N) ∧
    ((TR ⊢ sentence (LambdaInterpretation.equation M N).functional) ↔
      Frege.OpenLambda.BetaEtaConvertible M N) :=
  ⟨program_equations M N,
    (shared_algebra_provability (LambdaInterpretation.equation M N).applicative).symm.trans
      (program_equations M N)⟩

/-- The entire three-theory chain printed in the conservativity corollary. -/
theorem pure_conservativity_three_way (p : Pure.Formula) :
    ((Bare.theory ⊢ Bare.sentence p) ↔ (TR ⊢ sentence p.functional)) ∧
    ((TR ⊢ sentence p.functional) ↔ (TF ⊢ sentence p.functional)) :=
  ⟨(pure_conservativity p).trans (shared_algebra_provability p.applicative),
    (shared_algebra_provability p.applicative).symm⟩

/-- Concrete encoded models and both syntactic consistency conclusions.
No encoded ZFC claim is included in this theorem. -/
theorem models_and_consistency :
    (∃ M : SmallStruc language, M ⊧* TF ∧ M ⊧* TR) ∧
      Entailment.Consistent TF ∧ Entailment.Consistent TR :=
  ⟨PaperResults.concrete_encoded_models, consistent,
    consistency_iff_algebra.mp consistent⟩

theorem checked :
    (∀ σ, type_of% (Cleaner.provability_iff_fullFE σ)) ∧
    (type_of% Cleaner.zero_instance_proves_coverage) ∧
    (type_of% three_way) ∧
    (type_of% equiconsistency) ∧
    (type_of% consistent) ∧
    (∀ p, type_of% (shared_algebra_provability p)) ∧
    (∀ p, type_of% (pure_conservativity p)) ∧
    (∀ M N, type_of% (program_equations M N)) :=
  ⟨Cleaner.provability_iff_fullFE, Cleaner.zero_instance_proves_coverage,
    three_way, equiconsistency, consistent, shared_algebra_provability,
    pure_conservativity, program_equations⟩

end FregeanECA.V3.Certificate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``FregeanECA.V3.Certificate.checked,
    ``FregeanECA.V3.Certificate.program_equations_both,
    ``FregeanECA.V3.Certificate.pure_conservativity_three_way,
    ``FregeanECA.V3.Certificate.models_and_consistency,
    ``FregeanECA.V3.Nontriviality.countermodel,
    ``FregeanECA.V3.Nontriviality.A5_not_provable,
    ``FregeanECA.V3.PaperResults.inverse,
    ``FregeanECA.V3.PaperResults.unique_preimage_provable,
    ``FregeanECA.V3.PaperResults.basic_law_V_and_extensionality_provable,
    ``FregeanECA.V3.PaperResults.specification,
    ``FregeanECA.V3.SuccessorVerification.verifies,
    ``FregeanECA.V3.SuccessorVerification.available_domain,
    ``FregeanECA.V3.SuccessorVerification.code_identity_provable,
    ``FregeanECA.V3.SuccessorVerification.specification_provable,
    ``FregeanECA.V3.PaperResults.concrete_models,
    ``FregeanECA.V3.PaperResults.concrete_encoded_models,
    ``FregeanECA.V3.Cleaner.axioms_iff_fullFE,
    ``FregeanECA.V3.Cleaner.inverse_application,
    ``FregeanECA.V3.Cleaner.core_combinators_unique,
    ``FregeanECA.V3.Cleaner.inverse_from_zero_and_A3,
    ``FregeanECA.V3.ModelReconstruction.reconstruction,
    ``FregeanECA.V3.Specifications.graph_specification,
    ``FregeanECA.V3.RelationalComprehension.closure_provability,
    ``FregeanECA.Research.Z2Reverse.ReverseProofTransfer.source_semantics,
    ``FregeanECA.Research.Z2Reverse.ReverseProofTransfer.translation_preserves_falsum,
    ``FregeanECA.Part2.ArithmeticInterpretation.interpretation_preserves_falsum]
  for endpoint in endpoints do
    for ax in ← collectAxioms endpoint do
      unless allowed.contains ax do
        throwError "V3 CERTIFICATE REJECTED at {endpoint}: {ax}"
  logInfo "V3 CERTIFICATE PASS: literal cleaner A1--A5 bridge, zero-input coverage, six proof-transfer directions, equiconsistency, consistency, pure conservativity, and exact beta-eta equations; standard Lean axioms only."

#print axioms FregeanECA.V3.Certificate.checked
