# Functional Frege: Lean formalisation (anonymised artefact)

Supporting material for the manuscript *Functional Frege: a foundation for
computation and arithmetic*, submitted for review. Every numbered result of
the paper is proved in Lean 4 and checked by the Lean kernel. This repository
contains the proofs, a certificate that names the theorem behind each printed
result and audits its axioms, the machine-readable record of a fresh-source
verification, and an index from each printed result to its Lean theorem.
Nothing here identifies the authors.

You do not need to know Lean to check the certificate: see
[Section 1](#1-check-the-certificate-in-one-click).

## Contents

- [1. Check the certificate in one click](#1-check-the-certificate-in-one-click)
- [2. What is being certified](#2-what-is-being-certified)
- [3. The results and where they are proved](#3-the-results-and-where-they-are-proved)
- [4. Three levels of checking](#4-three-levels-of-checking)
  - [4.1 Offline: the recorded verification (seconds, no Lean)](#41-offline-the-recorded-verification-seconds-no-lean)
  - [4.2 Kernel check (minutes, installs Lean on request)](#42-kernel-check-minutes-installs-lean-on-request)
  - [4.3 Full fresh-source verification (about an hour)](#43-full-fresh-source-verification-about-an-hour)
- [5. Layout of the repository](#5-layout-of-the-repository)
- [6. How the Lean development is organised](#6-how-the-lean-development-is-organised)
- [7. How to read the proofs](#7-how-to-read-the-proofs)
  - [7.1 Start from the certificate](#71-start-from-the-certificate)
  - [7.2 Reading a statement](#72-reading-a-statement)
  - [7.3 The pattern every derivability proof follows](#73-the-pattern-every-derivability-proof-follows)
  - [7.4 A worked example: Proposition 6.3](#74-a-worked-example-proposition-63)
  - [7.5 Following a longer proof](#75-following-a-longer-proof)
  - [7.6 Tools that help](#76-tools-that-help)
- [8. The verification record](#8-the-verification-record)
- [9. What the certificate does and does not establish](#9-what-the-certificate-does-and-does-not-establish)
- [10. Reproducibility: versions and pins](#10-reproducibility-versions-and-pins)
- [11. For readers new to Lean](#11-for-readers-new-to-lean)
- [12. Licence and anonymity](#12-licence-and-anonymity)

## 1. Check the certificate in one click

1. Download the repository: the green **Code** button, then **Download ZIP**
   (or `git clone https://github.com/functional-frege/functional-frege`), and unpack it.
2. **Windows:** double-click [`check-certificate.cmd`](check-certificate.cmd).
   **macOS or Linux:** open a terminal in the unpacked folder and run
   `python3 check_certificate.py`.
3. Read the report. It ends with `CERTIFICATE PASS`, and above that lists
   every printed result of the paper with the Lean theorem that proves it and
   the axioms that theorem depends on:

   ```text
   Functional Frege: certificate check (offline)
   ========================================================================
   Verified run:    2026-10-28T15:54:42 UTC
   Toolchain:       leanprover/lean4:v4.33.1
   Recorded result: PASS
   Modules audited: 179 project, 19 vendored; 7831 declarations; 297 required endpoints

   Source hashes:   205 files recorded; 205 match, 0 differ, 0 missing
   Endpoints:       297 required; 294 audited with standard axioms only

   Certificate: printed result -> Lean theorem [axioms]
   ------------------------------------------------------------------------
   Definition 2.1 (def:tf): the printed axioms have the models and theorems of the encoding
      FregeanECA.V4.Certificate.printed_theory
         ok [Classical.choice, Quot.sound, propext]
   ...
   CERTIFICATE PASS (offline check of the recorded verification)
   ```

The only requirement is Python 3.9 or later. If the window says Python is
missing, install it from <https://www.python.org/downloads/> (on Windows tick
"Add python.exe to PATH" in the installer) and double-click again.

What this one click establishes, and what it does not, is explained in
[Section 4.1](#41-offline-the-recorded-verification-seconds-no-lean). To have
the Lean kernel itself re-check every proof on your own computer, double-click
[`check-certificate-with-lean.cmd`](check-certificate-with-lean.cmd) instead
([Section 4.2](#42-kernel-check-minutes-installs-lean-on-request)); it installs
Lean for you if you say yes.

## 2. What is being certified

The paper presents **Functional Frege (FF)**, a many-sorted first-order theory
with three kinds of sort: objects, functions from objects to objects, and
relations on objects. An operator δ assigns to each function *f* an object
δ*f*, its abstract (Frege's value-range). The five axioms are

| | Axiom | In words | In Lean |
| --- | --- | --- | --- |
| A1 | Relational comprehension | every formula defines a relation | `V3.Cleaner.A1` |
| A2 | Functional comprehension | a function for every term built by application (f(x̄) = t); in particular every object is an abstract | `V3.Cleaner.A2` |
| A3 | Functional Basic Law V | two functions have the same abstract exactly when they agree at every argument | `V4.Printed.A3` (= `lawV`) |
| A4 | Functional extensionality | functions that agree everywhere are equal | `V3.Cleaner.A4` |
| A5 | Nontriviality | T ≠ F, the abstracts of the two projections (Church's truth values); equivalent over A1–A4 to the existence of two distinct objects | `V3.Cleaner.A5` (encoded as ∃x,y x ≠ y; the printed form is `V4.Printed.A5`) |

The theory exactly as printed is `FregeanECA.V4.Printed.theory`
([`lean/FregeanECA/V4/PrintedTheory.lean`](lean/FregeanECA/V4/PrintedTheory.lean)).
An older encoding, `FregeanECA.V3.Cleaner.theory`, states A3 as injectivity of
δ; the module proves that the two presentations have the same models and the
same theorems (`axioms_iff_cleaner`, `provability_iff`), and the certificate
states every result for the printed theory. The comparison theories are
**NECA + RC**, nontrivial extensional combinatory algebra with full relational
comprehension (`FregeanECA.V3.RelationalComprehension.theory`), and **Z₂**,
full second-order arithmetic as a two-sorted first-order theory
(`FregeanECA.Part2.ArithmeticEncoding.theory`).

"FF proves σ" means, in Lean, `FF ⊢ σ`: derivability of the encoded sentence
σ from the encoded axiom set in the classical first-order sequent calculus of
the [Foundation](https://github.com/FormalizedFormalLogic/Foundation) library.
Consistency means that `⊥` is not derivable. The encoding is explained in
[`lean/FORMALISATION.md`](lean/FORMALISATION.md).

## 3. The results and where they are proved

The certificate is [`lean/FregeanECA/V4/Certificate.lean`](lean/FregeanECA/V4/Certificate.lean).
Each theorem in it is named after the printed result it states (the label in
backticks is the paper's LaTeX label). The last column names the module where
the underlying proof is developed; [`COVERAGE.md`](COVERAGE.md) gives, for
every row, the exact Lean statement and the proof method.

| Printed result | Certificate theorem | Proof developed in |
| --- | --- | --- |
| Definition 2.1 `def:tf`: printed axioms ≡ encoding | `printed_theory` | [`V4/PrintedTheory.lean`](lean/FregeanECA/V4/PrintedTheory.lean) |
| Proposition 2.2 `prop:inverse`: δ bijective, application defined | `inverse`, `unique_preimage_provable` | [`V3/PaperResults.lean`](lean/FregeanECA/V3/PaperResults.lean), [`V3/Cleaner.lean`](lean/FregeanECA/V3/Cleaner.lean) |
| Proposition 2.3 `prop:blv`: abstract identity and extensionality | `basic_law_V_and_extensionality_provable` | [`V3/PaperResults.lean`](lean/FregeanECA/V3/PaperResults.lean) |
| Proposition 2.4 `prop:nontriviality`: A5 independent | `nontriviality_independent` | [`V4/PrintedTheory.lean`](lean/FregeanECA/V4/PrintedTheory.lean), [`V3/Nontriviality.lean`](lean/FregeanECA/V3/Nontriviality.lean) |
| Theorem 3.4 `thm:correspondence`: FF and NECA + RC agree on the shared language | `core_combinators_unique`, `shared_algebra_provability`, `three_way` | [`V3/Certificate.lean`](lean/FregeanECA/V3/Certificate.lean), [`V3/Cleaner.lean`](lean/FregeanECA/V3/Cleaner.lean) |
| Proposition 3.5 `prop:reconstruction`: recovery of the structures | `V3.ModelReconstruction.reconstruction` | [`V3/ModelReconstruction.lean`](lean/FregeanECA/V3/ModelReconstruction.lean) |
| Theorem 3.6 `thm:bi-interpretability` | `bi_interpretable` | [`V4/BiInterpretability.lean`](lean/FregeanECA/V4/BiInterpretability.lean) |
| Theorem 4.2 `thm:arithmetic`: NECA + RC interprets Z₂ | `three_way` (arrows 3 and 4) | [`Part2/ArithmeticInterpretation.lean`](lean/FregeanECA/Part2/ArithmeticInterpretation.lean) |
| Theorem 4.3 `thm:reverse`: Z₂ interprets NECA + RC | `three_way` (arrows 1 and 2) | [`Research/Z2Reverse/`](lean/FregeanECA/Research/Z2Reverse/) |
| Corollary 4.4 `thm:three-way`: mutual interpretability, equiconsistency | `three_way`, `equiconsistency` | [`V3/Certificate.lean`](lean/FregeanECA/V3/Certificate.lean) |
| Theorem 4.5 `thm:consistency`: the open-term model | `models_and_consistency` | [`Concrete.lean`](lean/FregeanECA/Concrete.lean), [`V3/PaperResults.lean`](lean/FregeanECA/V3/PaperResults.lean) |
| Theorem 5.1 `thm:equations`: exactly the βη-equations | `exact_equations` | [`Part2/ProgramEquations.lean`](lean/FregeanECA/Part2/ProgramEquations.lean) |
| Theorem 5.2 `thm:conservativity`: conservative over NECA | `conservativity` | [`V3/Certificate.lean`](lean/FregeanECA/V3/Certificate.lean) |
| Proposition 6.1 `prop:concepts`: truth values and connectives | `concepts` | [`V4/TruthValues.lean`](lean/FregeanECA/V4/TruthValues.lean) |
| Theorem 6.2 `thm:collapse`: bivalent objects are constant | `collapse`, `no_horizontal` | [`V4/TruthValues.lean`](lean/FregeanECA/V4/TruthValues.lean) |
| Proposition 6.3 `prop:choice`: no object is a choice function | `no_choice_function` | [`V4/Choice.lean`](lean/FregeanECA/V4/Choice.lean) |
| Theorem 7.1 `thm:hume`: Hume's Principle on the number domain | `hume_on_number_domain` | [`V4/HumeBridge.lean`](lean/FregeanECA/V4/HumeBridge.lean), [`Part2/HumeInternal.lean`](lean/FregeanECA/Part2/HumeInternal.lean) |
| Corollary 7.2 `cor:frege-theorem`: Z₂ through Hume's Principle | `arithmetic_through_hume` | [`V4/HumeBridge.lean`](lean/FregeanECA/V4/HumeBridge.lean) |
| Proposition 7.3 `prop:hume-expansion`: whole-domain Hume model | `whole_domain_hume` | [`V4/HumeBridge.lean`](lean/FregeanECA/V4/HumeBridge.lean), [`Part2/Hume.lean`](lean/FregeanECA/Part2/Hume.lean) |
| Everything above together | `checked` | [`V4/Certificate.lean`](lean/FregeanECA/V4/Certificate.lean) |

Lemma 3.3 (bracket abstraction) and Lemma 4.1 (zero and successor) are
auxiliary lemmas used inside these proofs; `COVERAGE.md` names their Lean
counterparts.

## 4. Three levels of checking

### 4.1 Offline: the recorded verification (seconds, no Lean)

`check_certificate.py` (Section 1) reads
[`verification/verification.json`](verification/verification.json), the
record written by the verifier at the end of the fresh-source run reported in
the paper, and checks three things:

1. **The sources are the verified ones.** It recomputes the SHA-256 hash of
   every Lean source file under `lean/` and compares it with the hash recorded
   at verification time. Any edit to any proof file would show up here.
2. **Every endpoint was audited with standard axioms only.** For each of the
   297 required endpoints it confirms that the recorded transitive axiom
   dependencies are within `propext`, `Classical.choice` and `Quot.sound`,
   Lean's three standard axioms. No `sorry`, no `admit`, no added axiom.
3. **The certificate, result by result**, as in Section 3.

This establishes that the repository you downloaded is byte-for-byte the one
that passed the recorded verification. It does not itself re-run Lean; the
next level does.

### 4.2 Kernel check (minutes, installs Lean on request)

**Windows:** double-click [`check-certificate-with-lean.cmd`](check-certificate-with-lean.cmd).
**macOS or Linux:** `python3 check_certificate.py --run`.

If Lean is not installed, the script offers to install it: it installs
[elan](https://github.com/leanprover/elan), the Lean version manager, which
installs the pinned Lean 4.33.1 from [`lean/lean-toolchain`](lean/lean-toolchain);
it then fetches the prebuilt Mathlib library (several gigabytes, once), builds
the development, and finally runs

```text
lake env lean --trust=0 FregeanECA/V4/Certificate.lean
```

This re-elaborates the certificate file with the Lean kernel, trusting nothing
cached (`--trust=0`), and at the end runs the certificate's own audit, which
rejects any endpoint depending on an axiom outside the three standard ones. It
prints `V4 CERTIFICATE PASS` (and the script prints `KERNEL CHECK PASS`), or
`V4 CERTIFICATE REJECTED at <endpoint>: <axiom>`.

To do the same by hand:

```text
cd lean
lake exe cache get
lake build
lake env lean --trust=0 FregeanECA/V4/Certificate.lean
```

### 4.3 Full fresh-source verification (about an hour)

[`lean/verify.py`](lean/verify.py) is the verifier whose record is committed.
It copies the sources to a fresh directory, rebuilds every project and
vendored module without reusing any compiled file, checks the dependency pins
of [`lean/lake-manifest.json`](lean/lake-manifest.json) against the fetched
packages, scans for `sorry`, `admit` and `axiom`, audits the transitive axioms
of every one of the 7,831 declarations, checks all required endpoints, runs
every certificate file, and writes `verification/verification.json` with the
source hashes. Run it with

```text
cd lean
python -X utf8 verify.py --lake /absolute/path/to/lake
```

(`lake` is in `~/.elan/bin` after installing elan). `--preflight` checks
sources and pins without compiling.

## 5. Layout of the repository

| Path | Contents |
| --- | --- |
| [`check_certificate.py`](check_certificate.py), [`check-certificate.cmd`](check-certificate.cmd), [`check-certificate-with-lean.cmd`](check-certificate-with-lean.cmd) | The one-click checks of Section 1 and Section 4.2 |
| [`COVERAGE.md`](COVERAGE.md) | Paper-to-proof index: every numbered result, its exact Lean statement, its endpoints and the proof method |
| [`lean/`](lean/) | The Lean 4 project |
| [`lean/FregeanECA/V4/Certificate.lean`](lean/FregeanECA/V4/Certificate.lean) | The certificate: one theorem per printed result, and the axiom audit |
| [`lean/FORMALISATION.md`](lean/FORMALISATION.md) | Self-contained guide to the encoding, to what derivability means in the development, and to its limits |
| [`lean/README.md`](lean/README.md) | Module-level map of the Lean sources |
| [`lean/verify.py`](lean/verify.py) | The fresh-source verifier (Section 4.3) |
| [`lean/lean-toolchain`](lean/lean-toolchain), [`lean/lake-manifest.json`](lean/lake-manifest.json) | The pinned Lean version and dependency revisions |
| [`verification/`](verification/) | The verification record and the logs of the recorded runs (Section 8) |
| [`LICENSE`](LICENSE) | MIT |

## 6. How the Lean development is organised

All sources are under [`lean/FregeanECA/`](lean/FregeanECA/), in the namespace
`FregeanECA`; the term-algebra library they build on is vendored under
[`lean/vendor/Frege/`](lean/vendor/Frege/).

| Directory | Role |
| --- | --- |
| [`V4/`](lean/FregeanECA/V4/) | The certificate, the printed theory and its equivalence with the older encoding (`PrintedTheory.lean`), bi-interpretability (`BiInterpretability.lean`), the truth-value results (`TruthValues.lean`), and Hume's Principle with the Hume-route interpretation of Z₂ (`HumeBridge.lean`) |
| [`V3/`](lean/FregeanECA/V3/) | The literal axioms A1–A5 with A3 as injectivity (`Cleaner.lean`), NECA + RC (`RelationalComprehension.lean`), the inverse and Law V results (`PaperResults.lean`), structure recovery (`ModelReconstruction.lean`), the A5 countermodel (`Nontriviality.lean`), the V3 certificate with the three-way interpretability package |
| [`Part2/`](lean/FregeanECA/Part2/) | The interpretation of Z₂ in NECA + RC (least inductive domain, addition and multiplication graphs, comprehension), the exact βη-equation theorem, Hume's Principle on the number domain, Frege's theorem, the whole-domain Hume model |
| [`Research/Z2Reverse/`](lean/FregeanECA/Research/Z2Reverse/) | The interpretation of NECA + RC in Z₂: lambda terms, substitution, parallel reduction, confluence and the truth lemma, all coded inside an arbitrary model of the encoded Z₂ (completed work; the directory name is historical) |
| [`V2/`](lean/FregeanECA/V2/), [`Certificates/`](lean/FregeanECA/Certificates/), [`Comprehension/`](lean/FregeanECA/Comprehension/) | Earlier presentations of the same theories and the proved bridges that transfer their results to the literal axioms |
| top-level files | The many-sorted encoding (`Guarded.lean`, `Syntax.lean`, `Axioms*.lean`, `TheoryEncoding.lean`), the open-term model (`Concrete.lean`), the logic bridge between semantic and derivability statements (`LogicBridge.lean`) |
| [`../vendor/Frege/`](lean/vendor/Frege/) | Combinatory algebras, bracket abstraction, open lambda terms with named free variables, and βη confluence, used for the external model constructions |

How the many-sorted languages are encoded in Foundation's one-sorted calculus
(sort predicates, relativised quantifiers, a satisfaction predicate per
relation arity), and how semantic arguments become derivability statements
through the completeness theorem, is set out in
[`lean/FORMALISATION.md`](lean/FORMALISATION.md).

## 7. How to read the proofs

You need no Lean to *check* the proofs (Section 1); this section is for
reading them. Lean files are read top to bottom; everything a file uses is
either defined above or imported at the top.

### 7.1 Start from the certificate

Open [`lean/FregeanECA/V4/Certificate.lean`](lean/FregeanECA/V4/Certificate.lean).
Each theorem there carries, in its docstring, the paper's label (for example
`` `thm:collapse` ``). Its *statement* is the text between the theorem's name
and `:=`; its *proof* is what follows `:=`. In the certificate the proofs are
one-liners that name the theorem in the module where the work is done; follow
that name (Section 3's table says which file) to read the actual argument.

### 7.2 Reading a statement

The statements use a small vocabulary:

| Notation | Meaning |
| --- | --- |
| `TF ⊢ sentence p` | the encoded sentence `p` is derivable from the printed theory in Foundation's classical sequent calculus; `TR` is NECA + RC, `Z2` second-order arithmetic |
| `p.functional` | a formula of the pure applicative or algebraic language read as a formula of the functional language (the languages are nested) |
| `Valid M p` | `p` is true in the structure `M` under every assignment of the variables |
| `Interpretation D F R` | a structure with object domain `D`, function domain `F` and relation domains `R n` (relation arity `n+1`: `R 0` are unary relations) |
| `∀ p, Printed.Axiom p → Valid M p` | `M` is a model of the printed axioms |
| `Entailment.Consistent T` | `⊥` is not derivable from `T` |
| `notF p`, `iffF p q` | ¬p (defined as p → ⊥) and p ↔ q |
| `.var 0`, `.eval 0 (.var 0)`, `.app s t`, `.delta 0` | variables are de Bruijn indices: `.var 0` is the innermost bound object variable; `.eval i t` is f_i(t) for the i-th bound function variable; `.app s t` is application s(t); `.delta i` is δf_i |

So `theorem exact_equations (M N : Frege.OpenLambda.Term 0) : ((TF ⊢ sentence (LambdaInterpretation.equation M N).functional) ↔ Frege.OpenLambda.BetaEtaConvertible M N) ∧ …`
reads: for all open λ-terms M, N, the translated equation τ(M) = τ(N) is
derivable in FF exactly when M and N are βη-convertible.

### 7.3 The pattern every derivability proof follows

The paper argues "in an arbitrary model, hence provable by completeness", and
the Lean does the same, in four steps that recur in every module:

1. **State the sentence** as a `Formula` (e.g. `collapse`, `choiceInstance`).
2. **Prove a truth lemma**, `foo_truth : foo.truth M o f r ↔ ⟨ordinary mathematical statement⟩`,
   which unfolds the encoded formula into plain Lean; usually it is `Iff.rfl`,
   i.e. true by definition.
3. **Prove the mathematics** as a statement about an arbitrary model:
   `foo_valid` or `foo_fails : Valid M foo`, assuming the model satisfies the axioms.
4. **Lift to derivability** with completeness (`Theory.Proof.complete_on_eq_models`,
   packaged as `V3.PaperResults.provable_of_valid`) and, where the result was
   proved for an older presentation of the theory, move it across with a
   proved bridge (`Printed.provability_iff`, `V3.Cleaner.provability_iff_fullFE`,
   `pure_conservativity_three_way`).

Model-existence results (Theorem 4.5, Proposition 7.3) stop after step 3,
since they are statements about models, not derivations.

### 7.4 A worked example: Proposition 6.3

[`lean/FregeanECA/V4/Choice.lean`](lean/FregeanECA/V4/Choice.lean) is forty
lines and shows the whole pattern.

- `total` is the formula ∀x ∃y (y ≠ x(x)); `chooser` is ∃f ∀x (f(x) ≠ x(x));
  `choiceInstance` is `total → chooser`, the instance of functional choice for
  the relation y ≠ x(x). (Step 1.)
- `total_truth` and `chooser_truth` say what these mean in a model, and both
  are `Iff.rfl`. (Step 2.)
- `choice_fails` is the mathematics: in any model of the printed axioms,
  assume the instance holds; A5 gives two distinct objects `a ≠ b`, so for each
  `x` one of them differs from `x(x)`, which makes `total` true; the instance
  then yields a function `g` with `g(x) ≠ x(x)` for all `x`; the evaluation
  law `ev` says `g(δg) = (δg)(δg)`; taking `x := δg` contradicts the previous
  line. (Step 3.) Compare the paper's proof of Proposition 6.3: it is the same
  argument sentence for sentence.
- `no_choice_provable` lifts this to `Printed.theory ⊢ sentence (notF choiceInstance)`
  by `provable_of_valid` and the bridge `Printed.provability_iff`. (Step 4.)
- The certificate's `no_choice_function` restates it under the paper's label.

### 7.5 Following a longer proof

For Theorem 6.2, start at `V4.Certificate.collapse`, follow it to
`TruthValues.collapse_provable`, then to `collapse_valid` (the fixed-point
argument, with the fixed point built explicitly as `S·(K·g)·(S·I·I)`) and
`bare_of_valid` / `both_of_bare` (completeness and the conservativity bridge).
For the arithmetic (Theorem 4.2), [`COVERAGE.md`](COVERAGE.md) lists the
individual lemmas in the order the paper's proof uses them, from the least
inductive domain to the recursion equations. Whenever a name is unfamiliar,
search the `lean/` folder for `theorem <name>` or `def <name>`; every name is
defined exactly once.

### 7.6 Tools that help

- [VS Code](https://code.visualstudio.com/) with the
  [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4),
  after the build of Section 4.2: hover shows types, F12 jumps to definitions,
  and placing the cursor inside a proof shows the goal at that point.
- `#check name` prints a statement; `#print axioms name` prints what it
  depends on.
- [`lean/FORMALISATION.md`](lean/FORMALISATION.md) explains the encoding of the
  many-sorted languages in one-sorted first-order logic, which is the one
  place where the Lean text and the paper's notation differ systematically.

## 8. The verification record

[`verification/verification.json`](verification/verification.json) is written
by `verify.py` at the end of a run. Its main fields:

| Field | Meaning |
| --- | --- |
| `timestamp_utc`, `toolchain`, `success` | When the run finished, with which Lean, and whether every check passed |
| `commands` | Every command executed, its exit code, duration and log file |
| `source_sha256` | SHA-256 of every source and configuration file (205 files); what Section 4.1 recomputes |
| `source_modules`, `vendor_source_modules` | The 179 project and 19 vendored modules rebuilt from scratch |
| `declaration_axioms`, `audited_declaration_count` | The transitive axiom dependencies of all 7,831 declarations |
| `required_terminal_declarations`, `missing_audits` | The 297 endpoints that must be present, and which were not (none) |
| `unexpected_axioms`, `admission_scan` | Any axiom outside the standard three, any `sorry`/`admit` (none) |
| `external_dependencies`, `dependency_failures` | The pinned packages and pin mismatches (none) |
| `source_changes_during_verification` | Source drift during the run (none) |

The live logs of the same run are beside it: `verify-run.log` (the driver),
`fresh-build.log` (the rebuild), `v4-certificate.log`, `v3-certificate.log`,
`v2-certificate.log`, `fe-certificate.log`, `three-way-certificate.log` (each
certificate under `--trust=0`), and `axioms.log`, `terminal-axioms.log`,
`part2-axioms.log`, `research-axioms.log` (the axiom audits).
`build.log` and `v4-certificate-incremental.log` record the incremental
build and certificate check made before the fresh run. Local paths in the
logs are replaced by `<repo>`, `<toolchain>`, `<temp>` and `<home>`.

## 9. What the certificate does and does not establish

**Trusted base.** A passing kernel check means: the statements in
`V4/Certificate.lean` are theorems of Lean's type theory with the axioms
`propext`, `Classical.choice` and `Quot.sound`, as checked by the Lean 4
kernel. The development also relies on the correctness of the Foundation
library's definition of first-order derivability and its soundness and
completeness theorems, and of Mathlib, both as pinned.

**Correspondence with the paper.** The kernel checks Lean statements, not
LaTeX. That each Lean statement says what the printed result says is a matter
of reading the two side by side; [`COVERAGE.md`](COVERAGE.md) records that
reading for every result and names every encoding decision that bears on it
(for example that relation arity `n` is indexed as `n+1` in some inherited
modules, and that application and K, S are defined symbols with proved
unique-existence sentences).

**Not formalised.** Four unnumbered remarks of the paper are not formalised
and are identified in [`lean/FORMALISATION.md`](lean/FORMALISATION.md),
Section 7: that A5 is equivalent to K ≠ K·I; that the arithmetic
interpretations are not a bi-interpretation (the automorphism argument); that
A3 alone does not yield A4 (the two-element countermodel); and that the
Russell relation is not the membership of any object. No bi-interpretability
with Z₂, no conservativity over Z₂, and no consistency claim beyond the
open-term model are asserted anywhere.

## 10. Reproducibility: versions and pins

| Component | Version |
| --- | --- |
| Lean | 4.33.1 ([`lean/lean-toolchain`](lean/lean-toolchain)) |
| Foundation | revision `81810b9f22c49fbb32bd89c1e9737059d83a37e6` |
| Mathlib | `v4.33.1` (revision `0df444a360eaa60ab8c11dca51a86af692955474`) |
| other packages | as pinned in [`lean/lake-manifest.json`](lean/lake-manifest.json) |
| vendored term algebra | [`lean/vendor/Frege/`](lean/vendor/Frege/), hashes in [`lean/vendor/PROVENANCE.json`](lean/vendor/PROVENANCE.json) |

Lake fetches the packages at these pins into `lean/.lake/packages` on the
first build; the sources depend on no other checkout. The recorded run was
made on Windows; the same commands work on macOS and Linux.

## 11. For readers new to Lean

- A Lean theorem has the form `theorem name : statement := proof`. The
  certificate's statements are written to be read without the proofs: for
  example `TF ⊢ sentence coverage` reads "coverage is derivable from FF".
- `#print axioms name`, at the end of each certificate file, prints the
  axioms a theorem ultimately depends on; the three standard ones are
  expected, anything else is a problem, and the certificate's final audit
  rejects any other automatically.
- To browse the sources with hover information and jump-to-definition,
  install [VS Code](https://code.visualstudio.com/) with the
  [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
  and open the `lean/` folder after the build of Section 4.2.
- `lake` is Lean's build tool; `elan` installs Lean versions; `--trust=0`
  tells Lean to re-check everything rather than trust compiled files.
- [`lean/FORMALISATION.md`](lean/FORMALISATION.md) is written for a reader who
  knows first-order logic but not Lean.

## 12. Licence and anonymity

MIT; see [`LICENSE`](LICENSE). The repository is held under a throwaway
account for anonymous review and contains no author names, affiliations,
e-mail addresses or local paths. Repository: <https://github.com/functional-frege/functional-frege>.
