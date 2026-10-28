import FregeanECA.Part2.ArithmeticInterpretation
import FregeanECA.Part2.Consequences
import FregeanECA.Part2.OracleCountermodel
import FregeanECA.Part2.Hume
import FregeanECA.Part2.HumeInternal
import FregeanECA.Part2.FregeArithmeticZ2
import FregeanECA.Part2.FregeArithmeticProofTransfer
import FregeanECA.Part2.ProgramEquations
import FregeanECA.ComputationalAbstraction
import Lean.Util.CollectAxioms

/-!
# Retained certificate for the predecessor relational presentation

For the current manuscript, start with `FregeanECA/V2/Certificate.lean`.
The focused `FregeanECA/Certificates/ThreeWay.lean` additionally packages
the completed reverse interpretation and equiconsistency with Z2.
This retained certificate checks the earlier relational presentation;
the V2 bridges transport its results to the revised algebra.

From this project's `lean` folder, run:
    lake env lean --trust=0 FregeanECA/Certificate.lean

## What this certificate checks

| Result | Readable theorem below |
| --- | --- |
| Part I: equivalent shared consequences; both theories consistent | `part_one` |
| Part II: equivalent shared consequences; both consistent; actual Z2 proof transfer | `part_two` |
| Part II retains every Part I theorem | `retains_part_one` |
| Exact program equations and pointwise equations, at actual theory provability | `native_program_equations`, `native_pointwise_equations` |
| Actual derivation of the internal HP sentence in both Part II theories | `internal_hume` |
| Generic HP + full comprehension yields a Z2 interpretation | `standard_hume_to_Z2` |
| Actual Z2 proof transfer to both Part II theories THROUGH HP and the standard Frege theorem | `arithmetic_via_hume` |
| Countermodel for complement alone; diagonal representation obstruction | `complement_is_insufficient`, `part_three` |

`checked_certificate` packages these and the explicitly labelled supporting
model results into one proof, then runs the transitive axiom audit.
The expressions after `:` are the claims; the expressions after `:=` are
checked proof terms, referring to the proofs in the imported source files.
`T ⊢ p` means that T has a formal derivation of p. `T ⊬ ⊥` means consistency.
`∀` means for every, `↔` means if and only if, and `∧` means and.

This is one checkable entry point using the project's pinned libraries.
Imports supply definitions and proofs. They are not assumptions of our results.
The final executable audit rejects incomplete proofs and extra axioms anywhere
in the certificate's transitive proof dependencies. It permits only Lean's
standard propext, Classical.choice, and Quot.sound.

Definition map (paths relative to the lean folder; follow these to inspect details):
  FregeanECA/Syntax.lean: actual sorted languages, terms, formulas, quantifiers.
  FregeanECA/Axioms.lean: literal Part I axiom schemas.
  FregeanECA/Guarded.lean: sorted formulas -> first-order sentences.
  FregeanECA/Part2/Axioms.lean: full comprehension with a fresh witness.
  FregeanECA/Part2/AlgebraAxioms.lean: literal complement and projection schemas.

The Part I Fregean presentation uses the proved definitional expansion by
application and K/S; see FregeanECA/Equivalence.lean. Function-sort identity
extensionality is NOT added. Relation index n denotes arity n+1.
-/

set_option warningAsError true

namespace FregeanECA.Certificate
open FFL FFL.FirstOrder
universe u v

/-! ## 1. The theories and fixed translations -/

/-- A theory is a set of first-order sentences, not a semantic definition of
provability. Its background consists of equality, sort/typing axioms, and the
universally closed instances of the specified axiom family. -/
def theory (axioms : Functional.Formula → Prop) : Theory Guarded.language :=
  Theory.eqAxiom Guarded.language ∪ Guarded.sortTheory ∪
    {sentence | ∃ formula, axioms formula ∧ Guarded.sentence formula = sentence}

/-- Part I: A1--A5, in the checked defined application/K/S expansion. -/
abbrev TF := theory Axioms.FunctionalAxiom

/-- Part I: nontrivial extensional combinatory algebra plus B1--B5. -/
abbrev TS := theory Axioms.SpecificationAxiom

/-- Part II: the Fregean theory with full classical relational comprehension. -/
abbrev TFfull := theory Part2.FullFunctionalAxiom

/-- Part II: the algebraic theory with complement C and predicate projection Q. -/
abbrev TSfull := theory Part2.AlgebraAxiom

/-- Encode a shared-language formula with its free variables universally closed. -/
noncomputable abbrev shared (formula : Applicative.Formula) := Guarded.sentence formula.functional

/-- The actual source theory of second-order arithmetic and its fixed translation. -/
abbrev Z2 := Part2.ArithmeticEncoding.theory
noncomputable abbrev arithmeticSentence := Part2.ArithmeticEncoding.sentence
noncomputable abbrev arithmeticTranslation (p : Part2.SecondOrderArithmetic.Formula) :=
  shared (Part2.ArithmeticInterpretation.interpret p)

/-- The second, explicitly composed translation: target -> HP -> Frege
numbers -> arithmetic. Its witnesses satisfy the displayed source formulas. -/
noncomputable abbrev humeArithmeticTranslation (p : Part2.SecondOrderArithmetic.Formula) :=
  shared (Part2.FregeArithmeticProofTransfer.interpret p)

/-! ## 2. Equivalence, consistency, retention, and obstructions -/

/-- PART I. Equivalence on every shared sentence; neither theory proves false. -/
theorem part_one :
    (∀ p : Applicative.Formula, (TF ⊢ shared p) ↔ (TS ⊢ shared p)) ∧
    (TF ⊬ (⊥ : Sentence Guarded.language)) ∧
    (TS ⊬ (⊥ : Sentence Guarded.language)) :=
  ⟨Encoded.functional_specification_provability,
    Encoded.neither_theory_proves_false⟩

/-- PART II. The same equivalence and consistency; every actual Z2 proof
transfers to both theories under the displayed, fixed translation. -/
theorem part_two :
    (∀ p : Applicative.Formula, (TFfull ⊢ shared p) ↔ (TSfull ⊢ shared p)) ∧
    (TFfull ⊬ (⊥ : Sentence Guarded.language)) ∧
    (TSfull ⊬ (⊥ : Sentence Guarded.language)) ∧
    (∀ p : Part2.SecondOrderArithmetic.Formula,
      (Z2 ⊢ arithmeticSentence p) →
        (TFfull ⊢ arithmeticTranslation p) ∧ (TSfull ⊢ arithmeticTranslation p)) :=
  ⟨Part2.full_functional_algebra_provability,
    Part2.full_neither_theory_proves_false.2,
    Part2.full_neither_theory_proves_false.1,
    fun p proof => ⟨Part2.ArithmeticInterpretation.Z2_proof_transfer_fregean p proof,
      Part2.ArithmeticInterpretation.Z2_proof_transfer p proof⟩⟩

/-- Retention of Part I is also a statement about actual derivations. -/
theorem retains_part_one :
    (∀ p : Sentence Guarded.language, (TF ⊢ p) → (TFfull ⊢ p)) ∧
    (∀ p : Sentence Guarded.language, (TS ⊢ p) → (TSfull ⊢ p)) :=
  ⟨Part2.preserves_part_one_functional, Part2.preserves_part_one_algebraic⟩

/-- The fully specified countermodel; the zero defaults are actual data,
not an assumed model-existence or nondefinability hypothesis. -/
noncomputable abbrev countermodel := Part2.Oracle.definableModel
  (Part2.Oracle.withSyntax (fun _ _ _ => 0))

theorem complement_is_insufficient :
    TSConditions countermodel ∧ Part2.ComplementClosure countermodel ∧
    ¬ Part2.HasFullComprehension countermodel ∧ ¬ Part2.PredicateProjection countermodel :=
  Part2.Oracle.complemented_specification_without_predicate_projection (fun _ _ _ => 0)

/-- PART III. Full relation comprehension cannot also make every unary relation
representable by native application returning a fixed value. This is the exact
diagonal obstruction; no literature theorem is assumed by this proof. -/
theorem part_three {D : Type u} {R : Nat → Type v}
    (M : Positive.Interpretation D R) (full : Part2.HasFullComprehension M) (a : D) :
    ¬ (∀ relation : R 0, ∃ code : D, ∀ x : D,
      M.satisfies 0 relation (fun _ => x) ↔ M.apply code x = a) :=
  Part2.full_comprehension_excludes_unrestricted_predicate_representation M full a

/-- Exact computation in the canonical open term model. This quantifies over
open inputs and does not assert observational equivalence or a new theorem
about all equations provable in the Fregean theory. -/
theorem canonical_computation :
    ∀ M N : Frege.OpenLambda.Term 0, Frege.OpenLambda.BetaEtaConvertible M N ↔
      ∀ p : Frege.OpenLambda.Element,
        Frege.OpenLambda.apply (Frege.OpenLambda.termClass M) p =
          Frege.OpenLambda.apply (Frege.OpenLambda.termClass N) p :=
  ComputationalAbstraction.beta_eta_iff_same_values

/-! ## 3. Exact computational reasoning in the actual theories -/

/-- Actual Part II provability, not a chosen-model premise: under the literal
K/S translation, both theories prove exactly the ordinary beta-eta equations.
`Guarded.sentence` universally closes the free source-name variables. -/
theorem native_program_equations :
    ∀ M N : Frege.OpenLambda.Term 0,
      ((TFfull ⊢ Guarded.sentence (LambdaInterpretation.equation M N).functional) ↔
        Frege.OpenLambda.BetaEtaConvertible M N) ∧
      ((TSfull ⊢ Guarded.sentence (LambdaInterpretation.equation M N).functional) ↔
        Frege.OpenLambda.BetaEtaConvertible M N) :=
  fun M N => ⟨Part2.ProgramEquations.full_functional_program_equation_iff M N,
    Part2.ProgramEquations.full_algebra_program_equation_iff M N⟩

/-- The native formula says the programs agree at EVERY object input; its
bound input variable is fresh by construction. Both Part II theories prove
this exactly when the source programs are beta-eta convertible. -/
theorem native_pointwise_equations :
    ∀ M N : Frege.OpenLambda.Term 0,
      ((TFfull ⊢ Guarded.sentence (LambdaInterpretation.pointwiseEquation M N).functional) ↔
        Frege.OpenLambda.BetaEtaConvertible M N) ∧
      ((TSfull ⊢ Guarded.sentence (LambdaInterpretation.pointwiseEquation M N).functional) ↔
        Frege.OpenLambda.BetaEtaConvertible M N) :=
  fun M N => ⟨Part2.ProgramEquations.full_functional_pointwise_program_equation_iff M N,
    Part2.ProgramEquations.full_algebra_pointwise_program_equation_iff M N⟩

/-! ## 4. Hume's Principle and the standard Frege arithmetic route -/

/-- An explicit common Part II model expanded by a NEW cardinality map.
This proves joint satisfiability with Hume's Principle, not its derivability
from the unexpanded theories. Witnesses are in the actual binary relation sort. -/
theorem hume_model_expansion :
    Part2.FullTSConditions Part2.Hume.specification ∧
    Part2.FullTFConditions Part2.Hume.functional ∧
    ∀ P Q : Part2.Hume.Relation 0,
      Part2.Hume.relationNumber P = Part2.Hume.relationNumber Q ↔
        Part2.Hume.ModelEquinumerous P Q :=
  Part2.Hume.part_two_has_hume_expansion

/-- Both Part II theories actually derive the closed HP assertion: a least
inductive number domain exists, every available predicate on that domain has
a unique defined abstract, and equality of abstracts is equinumerosity there.
This is a formal sequent-calculus proof, with no model premise. -/
theorem internal_hume :
    (TFfull ⊢ shared Part2.HumeInternal.internalHumeSentence) ∧
    (TSfull ⊢ shared Part2.HumeInternal.internalHumeSentence) :=
  ⟨Part2.HumeInternal.internal_hume_provable_fregean,
    Part2.HumeInternal.internal_hume_provable⟩

/-- The defined abstraction graph is total and single-valued on every
represented Peano domain. Its values obey HP for the available relations;
equinumerosity and predicate extensions are restricted to that domain. -/
theorem internal_hume_semantics {D : Type u} {R : Nat → Type v}
    (M : Positive.Interpretation D R) (full : Part2.HasFullComprehension M)
    {N : R 0} (domain : Part2.Arithmetic.PeanoDomain M N) :
    (∀ P : R 0, ∃! a, Part2.HumeInternal.Code M N P a) ∧
    (∀ (P Q : R 0) (a b : D), Part2.HumeInternal.Code M N P a →
      Part2.HumeInternal.Code M N Q b →
      (a = b ↔ Part2.HumeBijections.Equinumerous M N P Q)) :=
  ⟨Part2.HumeInternal.code_total_unique M full domain,
    fun _ _ _ _ ha hb => Part2.HumeInternal.humes_principle M full domain ha hb⟩

/-- Full comprehension survives adding the DEFINED abstraction-graph atom,
with nested object and relation quantifiers. This covers the displayed
ExpandedFormula grammar, not proof transfer from an unspecified HP calculus. -/
theorem internal_hume_comprehension {D : Type u} {R : Nat → Type v}
    (M : Positive.Interpretation D R) (full : Part2.HasFullComprehension M)
    (arity : Nat) (p : Part2.HumeInternal.ExpandedFormula)
    (o : Positive.ObjectAssignment D) (r : Positive.PredicateAssignment R) :
    ∃ P : R arity, ∀ xs, M.satisfies arity P xs ↔
      p.truth M (Positive.assignTuple (arity + 1) xs o) r :=
  Part2.HumeInternal.expanded_comprehension M full arity p o r

/-- The standard Frege theorem route: every generic model of HP and full
comprehension contains the constructed Frege-number model of Z2, and every
actual Z2 proof is true in that interpretation. No pre-existing Peano domain,
arithmetic operations, or adapter-comprehension premise is assumed. -/
theorem standard_hume_to_Z2 {D : Type u} {R : Nat → Type v}
    (M : Part2.FregeArithmetic.Interpretation D R)
    (full : Part2.FregeArithmetic.FullConditions M) :
    (∀ p, Part2.SecondOrderArithmetic.Axiom p →
      Part2.SecondOrderArithmetic.Valid
        (Part2.SecondOrderArithmetic.arithmeticOperations (Part2.FregeArithmeticZ2.arithmetic M full)) p) ∧
    (∀ p, (Z2 ⊢ arithmeticSentence p) →
      Part2.SecondOrderArithmetic.Valid
        (Part2.SecondOrderArithmetic.arithmeticOperations (Part2.FregeArithmeticZ2.arithmetic M full)) p) :=
  ⟨Part2.FregeArithmeticZ2.hume_implies_Z2_axioms M full,
    Part2.FregeArithmeticZ2.hume_proof_truth M full⟩

/-- Actual source proofs give actual target proofs through the completed HP
route. This is a second fixed translation, with no model, graph, or assumed
arithmetic-validity premise. -/
theorem arithmetic_via_hume :
    ∀ p : Part2.SecondOrderArithmetic.Formula,
      (Z2 ⊢ arithmeticSentence p) →
      (TFfull ⊢ humeArithmeticTranslation p) ∧ (TSfull ⊢ humeArithmeticTranslation p) :=
  fun p proof =>
    ⟨Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer_fregean p proof,
      Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer p proof⟩

/-- The composed translation of contradiction is false in every target
interpretation, without assuming any target axioms. -/
theorem hume_translation_preserves_false {D : Type u} {R : Nat → Type v}
    (M : Positive.Interpretation D R) (o : Positive.ObjectAssignment D)
    (r : Positive.PredicateAssignment R) :
    ¬ (Part2.FregeArithmeticProofTransfer.interpret .falsum).truth M o r :=
  Part2.FregeArithmeticProofTransfer.interpretation_preserves_falsum M o r

/-! ## 5. One terminal certificate and its axiom check -/

/-- One terminal proof packages the readable statements above. `type_of%`
copies their exact proposition types; it does not assert their truth. -/
theorem checked_certificate :
    (type_of% part_one) ∧ (type_of% part_two) ∧
    (type_of% retains_part_one) ∧ (type_of% complement_is_insufficient) ∧
    (∀ {D : Type u} {R : Nat → Type v} (M : Positive.Interpretation D R)
      (full : Part2.HasFullComprehension M) (a : D), type_of% (part_three M full a)) ∧
    (type_of% canonical_computation) ∧ (type_of% native_program_equations) ∧
    (type_of% native_pointwise_equations) ∧ (type_of% hume_model_expansion) ∧
    (type_of% internal_hume) ∧
    (∀ {D : Type u} {R : Nat → Type v} (M : Positive.Interpretation D R)
      (full : Part2.HasFullComprehension M) {N : R 0}
      (domain : Part2.Arithmetic.PeanoDomain M N),
        type_of% (internal_hume_semantics M full domain)) ∧
    (∀ {D : Type u} {R : Nat → Type v} (M : Positive.Interpretation D R)
      (full : Part2.HasFullComprehension M) (arity : Nat)
      (p : Part2.HumeInternal.ExpandedFormula) (o : Positive.ObjectAssignment D)
      (r : Positive.PredicateAssignment R),
        type_of% (internal_hume_comprehension M full arity p o r)) ∧
    (∀ {D : Type u} {R : Nat → Type v}
      (M : Part2.FregeArithmetic.Interpretation D R)
      (full : Part2.FregeArithmetic.FullConditions M), type_of% (standard_hume_to_Z2 M full)) ∧
    (type_of% arithmetic_via_hume) ∧
    (∀ {D : Type u} {R : Nat → Type v} (M : Positive.Interpretation D R)
      (o : Positive.ObjectAssignment D) (r : Positive.PredicateAssignment R),
      type_of% (hume_translation_preserves_false M o r)) :=
  ⟨part_one, part_two, retains_part_one, complement_is_insufficient,
    (fun M full a => part_three M full a), canonical_computation,
    native_program_equations, native_pointwise_equations, hume_model_expansion,
    internal_hume, @internal_hume_semantics, @internal_hume_comprehension,
    @standard_hume_to_Z2, arithmetic_via_hume, @hume_translation_preserves_false⟩

end FregeanECA.Certificate

-- This audit fails the Lean command itself if an imported dependency contains
-- an admission or an extra mathematical assumption. It merely inspects proofs;
-- it is never used to manufacture a proof of the mathematical statement.
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let dependencies ← collectAxioms ``FregeanECA.Certificate.checked_certificate
  for dependency in dependencies do
    unless allowed.contains dependency do
      throwError "Certificate rejected: unexpected axiom {dependency}"
  logInfo "CERTIFICATE AXIOM AUDIT PASS: only standard Lean axioms occur. Require exit code 0 for a successful certificate check."

#print axioms FregeanECA.Certificate.checked_certificate
