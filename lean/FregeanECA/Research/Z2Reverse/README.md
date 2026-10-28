# Reverse interpretation in Z2

This directory proves the reverse interpretation of Part II in Z2, using a
fixed arithmetic formula translation and actual Foundation proof transfer.
Together with the existing arithmetic-to-Part-II translation,
[Part2.MutualInterpretability](../../Part2/MutualInterpretability.lean) establishes
three-way mutual interpretability and equiconsistency of the full Fregean
theory, active V2 ECAneq + FCAlgebra, and encoded Z2. The optional function
extensionality extension is also mutually interpretable with Z2. The focused
[ThreeWay certificate](../../Certificates/ThreeWay.lean) audits the final
endpoints and is included in the main V2 certificate.

The object construction is now an internally coded open lambda algebra in an
arbitrary PA model, including a nonstandard model. Its equality is internally
finite beta-eta conversion, and relations are represented using the source
Z2 model's available sets. Term codes, binder depths, proof trees, and path
lengths range over the source model's numbers, not just external Lean `Nat`.

## Checked components

| Modules | What is established |
| --- | --- |
| [ArithmeticModel](ArithmeticModel.lean), [ModelTruth](ModelTruth.lean), [ArithmeticSentenceTruth](ArithmeticSentenceTruth.lean) | Extraction of native number/set semantics from actual guarded Z2 models, source proof validity, and both directions of the guarded sentence truth lemma. |
| [NativeInduction](NativeInduction.lean), [ArithmeticLanguage](ArithmeticLanguage.lean), [NativeArithmetic](NativeArithmetic.lean), [NativeOrder](NativeOrder.lean), [NativePA](NativePA.lean), [SourceArithmetic](SourceArithmetic.lean) | Available-set comprehension gives native induction; explicit arithmetic translation yields Foundation PA and IΣ1 on each extracted number carrier. |
| [InternalLambdaCode](InternalLambdaCode.lean), [InternalLambdaScope](InternalLambdaScope.lean), [InternalLambdaEmbedding](InternalLambdaEmbedding.lean) | Definable raw terms, free-name bounds, binder-depth requirements, scope, and internal formula encoding. |
| [InternalBinderRecursion](InternalBinderRecursion.lean), [InternalPAInduction](InternalPAInduction.lean) | Recursion whose numeric parameter changes beneath binders, and term/scoped-term induction for first-order definable predicates. |
| [InternalFreeSubstitution](InternalFreeSubstitution.lean), [InternalBoundShift](InternalBoundShift.lean), [InternalBoundSubstitution](InternalBoundSubstitution.lean), [InternalShiftLaws](InternalShiftLaws.lean), [InternalSubstitutionLaws](InternalSubstitutionLaws.lean), [InternalIdentitySubstitution](InternalIdentitySubstitution.lean) | Free-name substitution, capture-avoiding bound substitution and shift, scope preservation, composition, and beta/shift identities. |
| [InternalBindFree](InternalBindFree.lean), [InternalAbstraction](InternalAbstraction.lean), [InternalBindFreeLaws](InternalBindFreeLaws.lean), [InternalAvoidsIndex](InternalAvoidsIndex.lean) | Free-name abstraction, freshness, substitution/shift compatibility, bound-index avoidance, and unshifting. |
| [InternalPaths](InternalPaths.lean), [InternalConfluence](InternalConfluence.lean), [InternalCommutationLift](InternalCommutationLift.lean), [InternalCombinedConfluence](InternalCombinedConfluence.lean) | Definable numeric path certificates with concatenation, reversal, induction, and conversion equivalence. Generic diamond/confluence/commutation results retain their explicit relation hypotheses. |
| [InternalParallelBeta](InternalParallelBeta.lean), [InternalCompleteDevelopment](InternalCompleteDevelopment.lean), [InternalParallelBetaConfluence](InternalParallelBetaConfluence.lean) | Numeric parallel-beta certificates, internal complete development, shift/substitution preservation, and the concrete parallel-beta diamond. |
| [InternalEtaReduction](InternalEtaReduction.lean), [InternalEtaLaws](InternalEtaLaws.lean), [InternalEtaPaths](InternalEtaPaths.lean), [InternalEtaConfluence](InternalEtaConfluence.lean) | Numeric eta certificates, structural and substitution laws, coded context transport, optional diamond, and eta Church-Rosser. |
| [InternalBetaEtaCommutation](InternalBetaEtaCommutation.lean), [InternalQuotientNontriviality](InternalQuotientNontriviality.lean) | Concrete beta-eta commutation and combined Church-Rosser; distinct source-model free names remain distinct in the quotient. |
| [InternalTermQuotient](InternalTermQuotient.lean), [InternalCombinators](InternalCombinators.lean), [InternalConversionCongruence](InternalConversionCongruence.lean) | A total numeric quotient presentation, application congruence, and explicit K/S reduction paths and quotient equations. |
| [InternalExtensionality](InternalExtensionality.lean), [InternalQuotientAlgebra](InternalQuotientAlgebra.lean), [InternalQuotientNontriviality](InternalQuotientNontriviality.lean) | Fresh-name abstraction proves extensionality. The final `InternalQuotientNontriviality.eca` supplies all four ECA conditions from an arbitrary PA model, with no supplied algebra, extensionality, or separation premise. |
| [NativeAtomTranslation](NativeAtomTranslation.lean), [InternalAtomicDefinitions](InternalAtomicDefinitions.lean), [InternalConversionFormula](InternalConversionFormula.lean) | One fixed parameter-free arithmetic formula for numeric conversion, its exact truth theorem, and concrete arithmetic definitions for quotient equality, K, S, application, and pairing. |
| [RelationCoding](RelationCoding.lean), [NativeFormulaTools](NativeFormulaTools.lean), [ArithmeticCodeAtoms](ArithmeticCodeAtoms.lean), [FormulaTranslation](FormulaTranslation.lean) | Compositional translation of full target formulas, including relation identity and quantifiers, from the finite atomic interface. The general theorems retain that interface as a hypothesis. |
| [ComprehensionTransfer](ComprehensionTransfer.lean), [SourceComprehension](SourceComprehension.lean) | Source Z2 comprehension supplies pullback representation, full target comprehension, and FCAlgebra from a numeric object presentation and its atomic definitions. |
| [InternalSourceModel](InternalSourceModel.lean) | Every actual encoded Z2 equality model yields the concrete nontrivial ECA, full comprehension, FCAlgebra, and the full functional copy expansion, with no remaining coding or algebra premises. |
| [UniformFormulaTranslation](UniformFormulaTranslation.lean), [GuardedFormulaTranslation](GuardedFormulaTranslation.lean), [ReverseProofTransfer](ReverseProofTransfer.lean) | Fixed model-independent syntax, finite saturation guards for free relation parameters, exact source-model sentence semantics, falsum preservation, and actual full-algebra/V2-to-Z2 proof transfer. |
| [ReverseConsistency](ReverseConsistency.lean), [Part2.MutualInterpretability](../../Part2/MutualInterpretability.lean) | Relative consistency from the source-model construction, all six proof-transfer directions among the three theories, equiconsistency, and the optional FE extension. |
| [TermCodes](TermCodes.lean) | Separate external syntax coding, least beta-eta class representatives, and canonical application. These external `Nat` results are not used as a substitute for the internal construction above. |

Every internal induction has a definability witness. No module assumes
induction for arbitrary external predicates on a nonstandard carrier. The
source set sort is not replaced by an external powerset. Generic conditional
lemmas remain conditional; the concrete ECA endpoint discharges the algebraic
hypotheses by the actual internal lambda construction.

## Final endpoints

`ReverseProofTransfer.translate` is one fixed translation of the complete
applicative formula grammar. `source_semantics` proves its sentence truth
law in every actual source Z2 equality model. `algebra_proof_transfer` and
`v2_proof_transfer` transfer actual target derivations to
`ArithmeticEncoding.theory`; `translation_preserves_falsum` verifies that
falsity remains false. Free relation parameters are guarded by a finite
saturation condition, whose exact validity equivalence is proved.

`Part2.MutualInterpretability.three_way` packages all six proof-transfer
directions, including the full functional grammar and primitive function
identity. `equiconsistency` packages the corresponding consistency
equivalences. These results establish mutual interpretability. They do not
assert bi-interpretability, identity of the languages, or arithmetic
conservativity under a fixed embedding.

## Rechecking

From the project `lean/` directory with the pinned Lean 4.33.1 toolchain:

```text
lake build FregeanECA.Certificates.ThreeWay FregeanECA.Research.Z2Reverse.ProgressCertificate
lake env lean --trust=0 FregeanECA/Certificates/ThreeWay.lean
lake env lean --trust=0 FregeanECA/Research/Z2Reverse/ProgressCertificate.lean
```

Require exit code zero. [ThreeWay.lean](../../Certificates/ThreeWay.lean)
audits the final theorem bundle, source-model semantics, and falsum
preservation. [ProgressCertificate.lean](ProgressCertificate.lean) remains a
separate audit of the underlying components. Both reject every endpoint
dependency outside the exact whitelist `propext`, `Classical.choice`, and
`Quot.sound`. No admissions or new mathematical axioms are permitted.
