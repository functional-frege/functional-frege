# Version 4 Lean companion

Start with [V4/Certificate.lean](FregeanECA/V4/Certificate.lean). It restates
every endpoint of [V3/Certificate.lean](FregeanECA/V3/Certificate.lean) and
adds the bi-interpretability theorem of Section 3 and the results printed in
Sections 5, 6 and 7 of the manuscript: exact beta-eta equations, conservativity
over NECA, the truth-value results, Hume's Principle on the number domain, the
Hume-route Z2 transfer and the whole-domain Hume model. The new theorems live in
[V4/BiInterpretability.lean](FregeanECA/V4/BiInterpretability.lean),
[V4/HumeBridge.lean](FregeanECA/V4/HumeBridge.lean) and
[V4/TruthValues.lean](FregeanECA/V4/TruthValues.lean) (the connectives as
objects, quantification as identity, the collapse of total concepts, and the
impossibility of a truth test, a total negation and a total conditional).
[COVERAGE.md](../COVERAGE.md) maps every numbered result of the manuscript to
exact theorem types and records the scope of the mathematical and formal
claims. [FORMALISATION.md](FORMALISATION.md) is the self-contained guide to the
encoding and its limits. The manuscript contains twenty proved results and
three definitions. The companion additionally retains the Hoare-style composition
rule and the successor-composition example, which are not printed.

## Check the proofs

Use Lean 4.33.1, Python 3.9 or later, Git, and the pinned Lake dependencies.
From this directory:

```text
lake exe cache get   # prebuilt Mathlib oleans; otherwise lake build compiles Mathlib from source
lake build
lake env lean --trust=0 FregeanECA/V4/Certificate.lean
python -X utf8 verify.py --lake /absolute/path/to/lake
```

Install the toolchain with [elan](https://github.com/leanprover/elan); it reads
`lean-toolchain` and installs Lean 4.33.1. Lake then fetches the pinned
dependencies into `.lake/packages` on the first build (`lake exe cache get`
downloads prebuilt Mathlib files). Logs of the recorded audits are in `../verification/`; see
[../verification/README.md](../verification/README.md) for the current status.

`verify.py` makes a fresh source copy and builds all own and vendored modules
without copying their oleans. It reuses pinned external dependency caches
after checking revisions and tracked-source cleanliness. It then audits the
transitive axioms of every project/vendor definition and theorem and checks
all required terminal endpoints. `--preflight` checks sources/dependencies
without compiling. No `sorry`, `admit`, custom Lean mathematical axiom,
unexpected dependency, modified vendor file, missing endpoint, or source
edit during the audit is accepted. Permitted Lean foundations are
`propext`, `Classical.choice`, and `Quot.sound`.

## Read the certificate

The statement follows `:` and its proof follows `:=` or `by`. Imports supply
proved dependencies, not unproved assumptions. `T ⊢ p` uses Foundation's
actual classical derivability relation; consistency means no proof of false.

| Certificate endpoint | Statement |
| --- | --- |
| `shared_algebra_provability` | Same theorems in the entire shared object/application/relation language |
| `three_way` | All six proof transfers among actual cleaner TF, ECA plus RC, and Z2 |
| `equiconsistency` | Consistency equivalences through the checked interpretations |
| `consistent` | No derivation of contradiction in the cleaner theory |
| `pure_conservativity` | Exactly the pure classical ECA consequences, not just program equations |
| `program_equations_both` | Both paper theories prove precisely the beta–eta equations between translated untyped terms |
| `pure_conservativity_three_way` | Same pure applicative consequences for NECA, NECA + RC and FF |
| `models_and_consistency` | The concrete model and consistency of both exact V3 presentations |
| `checked` | The principal V3 proof endpoints together |
| `V4.Certificate.printed_theory` | The printed axiom set has the models and theorems of the encoding (`def:tf`) |
| `V4.Certificate.bi_interpretable` | Proof transfer both ways, K∘M the identity up to provable equivalence on the algebraic language, and the isomorphism sentences for f ↦ δf derivable in FF, with the translation lemma in every model (`thm:bi-interpretability`) |
| `V4.Certificate.exact_equations` | Both theories prove precisely the beta–eta equations between translated open terms (`thm:equations`) |
| `V4.Certificate.conservativity` | Same pure applicative consequences for NECA, NECA + RC and FF (`thm:conservativity`) |
| `V4.Certificate.hume_on_number_domain` | Both theories derive the closed sentence `exists N (Nat(N) and UC_N and HP_N)` (`thm:hume`) |
| `V4.Certificate.arithmetic_through_hume` | Every Z2 proof transfers into both theories through the fixed Hume-route translation (`cor:frege-theorem`) |
| `V4.Certificate.whole_domain_hume` | A full-relation model of both literal theories with a whole-domain cardinality map satisfying HP (`prop:hume-expansion`) |
| `V4.Certificate.concepts` | The connectives as objects and quantification over a concept as identity with `K·T`, in both theories (`prop:concepts`) |
| `V4.Certificate.collapse` | Every object bivalent on the whole domain is constant, in both theories (`thm:collapse`) |
| `V4.Certificate.no_horizontal` | No object is a truth test (Frege's horizontal), a total negation, a total conditional, an equality test, a bivalent quantifier object or a whole-domain case operator (`thm:collapse`, consequences) |
| `V4.Certificate.checked` | All of the above together with `V3.Certificate.checked` |

This table inventories the certificate, whose checked scope is broader than
the current manuscript. The `program_equations_both`, `pure_conservativity`
and `pure_conservativity_three_way` endpoints are companion results.

The terminal audit also includes model reconstruction, inverse laws, unique
K/S derivation and the exact successor-composition example. The latter has
explicit Foundation derivability endpoints for its translated code identity
and its specification, as well as the native worked derivation. The certificate is a
small checking entry point with included proof sources and pinned dependencies,
not a dependency-free one-file proof. Compilation is not a truth decision procedure.

## Sources specific to the printed theory

| File | Role |
| --- | --- |
| [V3/Cleaner.lean](FregeanECA/V3/Cleaner.lean) | Literal A1–A5 and proof of equivalence with the previous full theory plus FE |
| [V3/ModelReconstruction.lean](FregeanECA/V3/ModelReconstruction.lean) | Delta bijection, structure recovery and all functional formulas |
| [V3/Specifications.lean](FregeanECA/V3/Specifications.lean) | Composition equation, specification rule and available binary graph |
| [V3/RelationalComprehension.lean](FregeanECA/V3/RelationalComprehension.lean) | Exactly ECA plus RC; the old closure algebra is a proved library bridge |
| [V3/Nontriviality.lean](FregeanECA/V3/Nontriviality.lean) | Singleton countermodel and actual A5 nonderivability from A1–A4 |
| [V3/PaperResults.lean](FregeanECA/V3/PaperResults.lean) | Printed inverse, BLV and model statements; the retained companion specification bundle |
| [V3/SuccessorVerification.lean](FregeanECA/V3/SuccessorVerification.lean) | Literal lambda translation with K substitution; code identity and successor-domain specification, including actual derivability |
| [V3/Certificate.lean](FregeanECA/V3/Certificate.lean) | Actual V3 theorem package and rejecting axiom audit |
| [V4/BiInterpretability.lean](FregeanECA/V4/BiInterpretability.lean) | The components of bi-interpretability: double-translation interderivability, the isomorphism sentences for f ↦ δf, and the translation lemma |
| [V4/PrintedTheory.lean](FregeanECA/V4/PrintedTheory.lean) | The theory exactly as printed (A3 = functional Basic Law V); proof that it has the same models and theorems as the older encoding with injective A3; the one-object countermodel for the independence of A5 |
| [V4/HumeBridge.lean](FregeanECA/V4/HumeBridge.lean) | Hume's Principle on the number domain, the Hume-route Z2 transfer and the whole-domain Hume model, transferred to the literal A1–A5 and NECA + RC theories through the certified provability bridges |
| [V4/TruthValues.lean](FregeanECA/V4/TruthValues.lean) | Church truth values: the connectives as objects, quantification as identity, the collapse of total concepts and the impossibility of a truth test, a total negation and a total conditional, as pure applicative sentences transferred to both theories |
| [V4/Certificate.lean](FregeanECA/V4/Certificate.lean) | V4 theorem package: every V3 endpoint plus the applicative-fragment, truth-value and Hume results, with a rejecting axiom audit |

A2 has a variable/application-only finite term grammar and permits zero
inputs. Free parameters are universally closed. The zero-input instance
proves the entire quantified coverage sentence in Foundation's calculus.
A3 is functional Basic Law V in `V4.Printed` and injectivity of delta in the
older `V3.Cleaner` encoding; the two are proved interderivable given A4. A4 is
function extensionality. Application and
K/S equations are separated as `DefinitionAxiom`; inverse existence and
unique K/S witnesses are proved from the appropriate core clauses.

Some inherited files index relation arity n+1 by n, so Lean `R 0` denotes
unary relations and `R 1` denotes binary relations. This is an implementation
index shift, not an additional hierarchy. D and F remain different sorts;
delta identifies them by a bijection, and its inverse is a cross-sort map.

## Included dependencies and boundaries

The old `V2/` and `Part2/` modules remain as a proved library. The V3 bridge
is applied before old results are transferred. The reverse interpretation
under `Research/Z2Reverse/` is completed code despite its historical path.
It works in arbitrary models of the encoded arithmetic, with internally
coded terms and available sets, rather than assuming standard numbers or
external powersets.

Mutual interpretability with Z2 does not assert bi-interpretability or
arithmetic conservativity. The function/algebra reconstruction is a separate,
stronger relationship between those two presentations. Inherited HP results
concern a defined number domain; whole-D HP has only a separate model
expansion result and is not asserted in the active V3 manuscript.

The model construction and consistency are checked in Lean's metatheory.
COVERAGE.md matches all twenty printed proved results, three definitions and
auxiliary arguments to their formal statements and methods, and separately
indexes the additional companion results. The printed
name FF (Functional Frege) corresponds to the certificate's abbreviation TF,
which is `V4.Printed.theory`; `TFenc` is the older encoding `V3.Cleaner.theory`.

`vendor/PROVENANCE.json` records reused term-algebra source hashes.
Foundation is pinned to `81810b9f22c49fbb32bd89c1e9737059d83a37e6`;
mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. Other revisions
are in `lake-manifest.json`. Lake fetches them into `.lake/packages` at
these pins; the sources do not depend on any other checkout.
