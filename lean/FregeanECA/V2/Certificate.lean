import FregeanECA.V2.Theorems
import FregeanECA.Part2.Consequences
import FregeanECA.Part2.ProgramEquations
import FregeanECA.Part2.Conservativity
import FregeanECA.Certificates.ThreeWay
import FregeanECA.Certificates.HumeRoute
import Lean.Util.CollectAxioms

/-! v2 certificate: new literal algebra axioms, standalone PC/FC equivalence,
combined equivalence and consistency, exact computation, internal HP and Z2.
This is a focused entry file with pinned imported proof dependencies.
Run `lake env lean --trust=0 FregeanECA/V2/Certificate.lean` and require exit 0. -/
set_option warningAsError true

namespace FregeanECA.V2.Certificate
open FFL FFL.FirstOrder Guarded Axioms Encoded

abbrev PCAlgebraTheory := V2.pcAlgebraTheory
abbrev PC := V2.positiveComprehensionTheory
abbrev FCAlgebraTheory := V2.fcAlgebraTheory
abbrev FC := V2.fullComprehensionTheory
abbrev TS := V2.combinedPositiveTheory
abbrev TSfull := V2.combinedFullTheory
abbrev TF := Encoded.functionalTheory
abbrev TFfull := Part2.fullFunctionalTheory

/-- The closed, original-language HP statement on the defined number domain:
there exists its least-inductive predicate N, every P has a unique Code_N
value, and two values agree iff the restrictions of P and Q to N are in
bijection. The witnesses and all quantifiers use the existing sorts.
This does not assert cardinal abstraction on the whole object domain. -/
noncomputable abbrev HP := sentence Part2.HumeInternal.internalHumeSentence.functional

/-- The new f(x-vector) presentation expands to exactly the old A2 sentence;
it does not strengthen the functional-comprehension scheme. -/
theorem a2_presentation (arity : Nat) (body : Positive.Term) :
    Axioms.functionalComprehension arity body =
      Functional.Formula.existsFunction (Axioms.allObjects (arity + 1)
        (.equal (Axioms.applyVariables (arity + 1) (.delta 0)) body.functional)) :=
  Axioms.functionalComprehension_expansion arity body

/-- No computational equations, extensionality, or nontriviality occur in
either standalone algebra's proper axiom set. -/
theorem standalone :
    (∀ σ : Sentence language, (PCAlgebraTheory ⊢ σ) ↔ (PC ⊢ σ)) ∧
    (∀ σ : Sentence language, (FCAlgebraTheory ⊢ σ) ↔ (FC ⊢ σ)) :=
  ⟨pc_algebra_comprehension_provability, fc_algebra_comprehension_provability⟩

theorem combined :
    (∀ p : Applicative.Formula, (TF ⊢ sentence p.functional) ↔
      (TS ⊢ sentence p.functional)) ∧
    (∀ p : Applicative.Formula, (TFfull ⊢ sentence p.functional) ↔
      (TSfull ⊢ sentence p.functional)) ∧
    (TS ⊬ (⊥ : Sentence language)) ∧ (TSfull ⊬ (⊥ : Sentence language)) :=
  ⟨functional_combined_positive_provability, functional_combined_full_provability,
    combined_neither_proves_false⟩

theorem retains_part_one : ∀ p : Sentence language, (TS ⊢ p) → (TSfull ⊢ p) := by
  intro p proof
  exact (combined_full_original_provability p).mpr
    (Part2.preserves_part_one_algebraic p
      ((combined_positive_original_provability p).mp proof))

theorem program_equations : ∀ M N : Frege.OpenLambda.Term 0,
    (TSfull ⊢ sentence (LambdaInterpretation.equation M N).functional) ↔
      Frege.OpenLambda.BetaEtaConvertible M N := by
  intro M N
  exact (combined_full_original_provability _).trans
    (Part2.ProgramEquations.full_algebra_program_equation_iff M N)

/-- Part II adds no consequences expressed solely with objects, application,
K and S, even when arbitrary classical connectives and quantifiers occur. -/
theorem computational_conservativity :
    (∀ p : Pure.Formula, (Bare.theory ⊢ Bare.sentence p) ↔
      (TSfull ⊢ sentence p.functional)) ∧
    (∀ p : Pure.Formula, (Bare.theory ⊢ Bare.sentence p) ↔
      (TFfull ⊢ sentence p.functional)) := by
  constructor
  · intro p
    exact (Part2.bare_eca_full_algebra_provability p).trans
      (combined_full_original_provability _).symm
  · exact Part2.bare_eca_full_functional_provability

/-- HP is the existing interpreted-number-domain statement, not unrestricted
cardinality abstraction on every concept of the original object domain. -/
theorem internal_hume :
    TSfull ⊢ sentence Part2.HumeInternal.internalHumeSentence.functional :=
  (combined_full_original_provability _).mpr Part2.HumeInternal.internal_hume_provable

/-- The explicit HP sentence proved by both presentations of Part II.
No added number sort, abstraction axiom, or arithmetic premise is assumed. -/
theorem humes_principle : (TFfull ⊢ HP) ∧ (TSfull ⊢ HP) :=
  ⟨Part2.HumeInternal.internal_hume_provable_fregean, internal_hume⟩

/-- Every Z2 proof transfers through the existing explicit HP interpretation. -/
theorem arithmetic_transfer : ∀ p : Part2.SecondOrderArithmetic.Formula,
    (Part2.ArithmeticEncoding.theory ⊢ Part2.ArithmeticEncoding.sentence p) →
      (TSfull ⊢ sentence (Part2.FregeArithmeticProofTransfer.interpret p).functional) := by
  intro p proof
  exact (combined_full_original_provability _).mpr
    (Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer p proof)

/-- Every direction between full TF, active full TS and Z2, with equiconsistency. -/
theorem three_way : type_of% Certificates.ThreeWay.checked := Certificates.ThreeWay.checked

theorem checked : (type_of% standalone) ∧ (type_of% combined) ∧
    (type_of% retains_part_one) ∧ (type_of% program_equations) ∧
    (type_of% computational_conservativity) ∧
    (type_of% internal_hume) ∧ (type_of% humes_principle) ∧ (type_of% arithmetic_transfer) ∧
    (type_of% three_way) ∧
    (∀ arity body, type_of% (a2_presentation arity body)) :=
  ⟨standalone, combined, retains_part_one, program_equations,
    computational_conservativity, internal_hume,
    humes_principle, arithmetic_transfer, three_way, a2_presentation⟩

end FregeanECA.V2.Certificate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [``FregeanECA.V2.Certificate.checked,
    ``FregeanECA.V2.fcAlgebra_iff_fullComprehension,
    ``FregeanECA.V2.fullTSConditions_iff,
    ``FregeanECA.V2.openSpecification_satisfies_fcAlgebra]
  for endpoint in endpoints do
    for ax in ← collectAxioms endpoint do
      unless allowed.contains ax do throwError "V2 certificate rejected at {endpoint}: {ax}"
  logInfo "V2 CERTIFICATE PASS: PC/FC equivalences, consistency, computation, HP over a domain of numbers, and three-way mutual interpretability with Z2; standard Lean axioms only."

#print axioms FregeanECA.V2.Certificate.checked
#print axioms FregeanECA.V2.fcAlgebra_iff_fullComprehension
#print axioms FregeanECA.V2.fullTSConditions_iff
#print axioms FregeanECA.V2.openSpecification_satisfies_fcAlgebra
