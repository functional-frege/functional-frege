# The Lean formalisation: a self-contained guide

This guide describes how the paper *Functional Frege: a foundation for
computation and arithmetic* (its theory is FF) is formalised in Lean 4 with
the [Foundation](https://github.com/FormalizedFormalLogic/Foundation) library,
what "the theory proves" means in the development, how each printed result
corresponds to a Lean theorem, and what the development does not claim. It is
meant to be read on its own. The paper's proofs are complete without it, with
one exception: the internal arithmetisation behind Theorem 4.3 is given in the
paper as a construction with its lemmas stated (Appendix A) and is proved in
full only here.

Companion files:

| File | Contents |
| --- | --- |
| [`../COVERAGE.md`](../COVERAGE.md) | Paper-to-proof index: every numbered result, its Lean endpoints, and the proof method |
| [`FregeanECA/V4/Certificate.lean`](FregeanECA/V4/Certificate.lean) | The certificate: states the main results, lists the required endpoints, audits their axioms |
| [`verify.py`](verify.py) | Fresh-source rebuild and transitive axiom audit; writes `../verification/verification.json` |
| [`../verification/`](../verification/) | Build, certificate and audit logs of the recorded runs |
| [`README.md`](README.md) | Module map and build notes for the Lean project |

## 1. Encoding of the languages

Foundation supplies a single-sorted first-order sequent calculus with
equality, its Tarskian semantics, and soundness and completeness. The
many-sorted languages of FF, NECA + RC and Z₂ are encoded in the standard way:

1. One first-order domain, with a unary sort predicate for each sort.
2. Quantifiers relativised to their sorts.
3. A small sort theory stating that every sort is nonempty and that every
   function symbol respects the sorts. Sorts are not required to be disjoint;
   this is harmless because every quantifier is relativised.
4. Equality is the primitive equality of the calculus on every sort. The
   equality axioms of the calculus, reflexivity and substitution of equals,
   belong to every encoded theory. These are the only logical assumptions;
   there is no rule of substitution beyond those of the sequent calculus.
5. Relation sorts are encoded by a membership predicate for each arity. The
   Lean index for arity is shifted by one; the paper's index is the arity
   itself.

The encoding lives in `FregeanECA/Guarded.lean` (sort predicates, relativised
quantifiers, the sort theory) and `FregeanECA/Syntax.lean` (the many-sorted
term and formula grammars, with `Term.eval` and `Term.delta` as the primitive
evaluation and abstraction).

## 2. Encoding of the theories

The six printed axioms A1–A6 are written out directly as formulas of the
many-sorted language (`FregeanECA/V4/PrintedTheory.lean`, `V4.Printed.A1`–`A6`),
and `V4.Printed.theory` (these six together with the defining clauses for
application and K/S) is the theory the certificate certifies:

1. A1 admits every formula of the functional language, including function and
   relation quantifiers; the fresh relation variable is index 0 of its arity and
   the other relation variables of that arity in φ are shifted past it, which is
   the proviso that φ does not mention P.
2. A2 admits terms built from variables and application only, with n ≥ 1 inputs
   and no parameters (the side condition `Closed`). Its left side f(x₁, …, xₙ) is
   literally f evaluated at the first input (`Term.eval`) and the resulting
   object applied to the remaining inputs (`Term.app`). The encoded A2 of the
   older modules (`V3.Cleaner.A2`) instead applies the abstract δf to all inputs
   and admits parameters and the empty input list, the parameters closed
   universally outside the witness; the two left sides differ by the defining
   clause (δf)(x) = f(x) at the first step (`V4.Printed.A2_iff_cleaner`), and
   `V4.Printed.parametric_comprehension` (Proposition 2.2) derives every encoded
   instance, parameters and the empty input list included, in every model of the
   printed axioms.
3. A3 (functional Basic Law V), A4 (functional extensionality), A5 (coverage)
   and A6 (T ≠ F for Church's truth values) are the closed sentences of the paper.
   The older modules encode A3 as injective abstraction and nontriviality as
   ∃x,y x ≠ y, and derive coverage from the zero-input encoded A2 instance
   (`V3.Cleaner.theory`, whose five clauses are numbered A1–A5 there);
   `V4.Printed.axioms_iff_cleaner` and `V4.Printed.provability_iff` prove that
   the printed and the encoded presentations have the same models and the same
   theorems, which includes the remark after Proposition 2.3 (injective
   abstraction in place of A3 given A4) and the remark on A6 (T ≠ F against two
   distinct objects, given the K/S clauses). Every endpoint is restated for the
   printed theory in `FregeanECA/V4/Certificate.lean`.

Two points concern the defined symbols.

1. Application and the constants K, S are symbols of the encoded signature,
   accompanied by their defining clauses (δf)·x = f(x), E1 and E2. These form
   the definitional extension described in Section 2.2 of the paper, not
   additional axioms: Lean proves from A1–A6 the closed sentence
   ∀x ∃f ∀g (g = f ↔ δg = x) that licenses the definition of application
   (`V3.PaperResults.unique_preimage_provable`), and proves that K and S are
   uniquely determined (`V3.Cleaner.core_combinators_unique`), so that
   adjoining these symbols with their equations is conservative.
2. Z₂ is encoded (`FregeanECA/Part2/ArithmeticEncoding.lean`) with the axioms
   of Section 4.1 of the paper: full comprehension for every formula,
   including formulas with set quantifiers, second-order induction, set
   extensionality, and the first-argument recursion equations.

NECA + RC is `V3.RelationalComprehension.theory`; the pure theory of E1–E4 in
the language of objects, application, K and S alone is `Bare.theory`
(`FregeanECA/Bare.lean`).

## 3. Derivability and proof transfer

Where the paper says that a theory proves a sentence, the Lean statement is
Foundation derivability (`T ⊢ σ`) of the encoded sentence from the encoded
axiom set. Semantic arguments are lifted to derivability by the completeness
theorem (`Theory.Proof.complete_on_eq_models`), and derivations are moved
between theories by the model-lift lemmas in `FregeanECA/LogicBridge.lean`.

1. **Bi-interpretability (Theorem 3.6)** is certified as the conjunction of
   its components (`V4/BiInterpretability.lean`): proof transfer in both
   directions, interderivability of every algebraic sentence with its double
   translation, derivability of coverage, A3 and the evaluation law in FF,
   and the translation lemma of Proposition 3.5 in every model. The general
   notion of an interpretation between theories is not itself formalised;
   the certificate states the specific sentences that the definition
   requires.
2. **The interpretation theorems (Theorems 3.4, 4.2 and 4.3)** are proved by
   the method their proofs describe: a fixed translation of the whole formula
   grammar, a model construction, soundness of the given derivation in the
   constructed model, and completeness for the target theory. They are
   theorems about actual derivations, but they are not implemented as
   syntactic transformations of proof trees.
3. **Proposition 3.5** is a semantic statement about interpretations of the
   encoded theories.
4. **Consistency (Theorem 4.5)** constructs a model in Lean's type theory and
   is a theorem of that metatheory.

## 4. The applicative fragment and Hume's Principle

1. **Exact equations (Theorem 5.1)** is proved for the encoded theory of
   E1–E4 in the pure language and transferred to FF and NECA + RC by
   Theorem 5.2 (`V3.Certificate.program_equations_both`). The translation τ
   is the bracket algorithm of Lemma 3.3 applied to a de Bruijn
   representation of open terms (`FregeanECA/LambdaInterpretation.lean`).
2. **Conservativity (Theorem 5.2)** is `V3.Certificate.pure_conservativity_three_way`:
   NECA, NECA + RC and FF prove the same pure applicative sentences.
3. **Hume's Principle on the number domain (Theorem 7.1)** is a closed
   sentence of the encoded shared language, proved by completeness from the
   semantic argument in every Henkin model of the axioms
   (`V4/HumeBridge.lean`). The interpretation of Corollary 7.2 is a fixed
   translation of the Z₂ grammar through the definable cardinal graph, with
   its own truth lemma and falsum preservation.
4. These results were first proved for an earlier presentation of the same
   theories (the `Part2` modules) and are transferred to the encodings of
   FF (A1–A6) and NECA + RC (E1–E4) by proved provability bridges, which are
   audited theorems of the same development.
5. **Proposition 7.4** is a model construction on the carrier ℕ.
6. **No choice functions (Proposition 6.3)** is `V4/Choice.lean`: the instance of
   functional choice for y ≠ x(x) is refuted in every model of the printed axioms
   and the negation is derived by completeness.
7. **Truth values (Proposition 6.1 and Theorem 6.2)** are pure applicative
   sentences (`V4/TruthValues.lean`): the connectives as objects and
   quantification as identity (`concepts_provable`), the collapse of
   total concepts (`collapse_provable`), and the impossibility of a truth
   test (Frege's horizontal), a total negation and a total conditional
   (`strokes_provable`). Each is proved valid
   in every structure satisfying `Pure.ECAConditions`, with an explicit
   bracket abstraction (`Poly.abs`) and the fixed-point construction
   `m := S·(K·g)·(S·I·I)` where needed, lifted to `Bare.theory` by
   completeness and transferred to both theories by Theorem 5.2. The
   bundle `concepts_provable` also certifies Law V for bivalent objects,
   the existential identity and closure under the connectives; these are
   not printed, because the collapse theorem makes them statements about
   the two objects `K·T` and `K·F`.
8. **Frege Arithmetic (Corollary 7.3)** is `V4/FregeArithmetic.lean`. Frege
   Arithmetic is represented by its Henkin models, the structures of the generic
   FA language satisfying Hume's Principle and full comprehension, and
   provability in it by validity in all of them (`FAValid`). `ff_interprets_fa`
   carries every FA-valid formula to a theorem of the printed theory along the
   Corollary 7.2 interpretation (`toFF`); `fa_interprets_ff` carries every theorem
   of the printed theory, through its Z₂ translation and the generic Frege
   theorem, to an FA-valid formula (`toFA`). The model-level halves are
   `fa_model_of_ff_model` and `ff_model_of_fa_model`. FA is not an encoded
   Foundation theory, so the completeness step for the FA language is outside the
   kernel, exactly as for the general notion of interpretation.

## 5. The reverse interpretation

For Theorem 4.3, lambda terms, binder depths, substitutions, parallel
reductions and conversion derivations are coded by numbers of an arbitrary
model of the encoded Z₂ (`FregeanECA/Research/Z2Reverse/`). Every induction
used is an instance of the encoded induction axiom on a definable predicate,
so the construction is valid when the coded lengths are nonstandard.
Confluence of beta, eta and beta–eta reduction for these coded terms is proved
internally. The external confluence results for finite open terms, used in
Theorem 4.5, come from a separately maintained library that is vendored with
the development (`vendor/Frege/`); they are not used in place of the internal
ones.

## 6. Trusted base and audit

1. Every endpoint depends only on Lean's standard axioms `propext`,
   `Classical.choice` and `Quot.sound`; there are no admitted proofs.
2. The object theories are encoded as axiom sets, not as new Lean axioms.
3. The certificate `FregeanECA/V4/Certificate.lean` states the main results,
   lists the required endpoints and rejects any endpoint whose axiom
   dependencies fall outside this list. Run it with
   `lake env lean --trust=0 FregeanECA/V4/Certificate.lean`; it prints
   `V4 CERTIFICATE PASS`.
4. `verify.py` copies the sources to a fresh directory, rebuilds every
   project and vendored module without reusing their oleans, checks the
   dependency pins, scans for `sorry`, `admit` and `axiom`, audits the axioms
   of every declaration transitively, checks all required endpoints, and
   writes `../verification/verification.json` with source hashes.
5. At the time of writing the development comprises 180 project modules and
   19 vendored modules, with 7,899 audited declarations and 297 required
   endpoints, and it builds with Lean 4.33.1 and a pinned revision of
   Foundation (see `lean-toolchain` and `lake-manifest.json`). The recorded
   fresh-source run of 28 October 2026 (`../verification/verification.json`)
   reports no admissions, no unexpected axioms and no source drift.

## 7. Limits

1. Kernel checking verifies the stated types. The correspondence between the
   printed statements and the Lean statements is recorded in
   [`../COVERAGE.md`](../COVERAGE.md) and was audited by hand.
2. Three unnumbered observations in the paper are not formalised: that the
   arithmetic interpretations are not a bi-interpretation (Section 4.2); that
   A3 alone does not give A4 (the two-element countermodel in the remark after
   Proposition 2.3; the interderivability given A4 is formalised in
   `V4.Printed`);
   and that a function-existence schema for arbitrary formulas is
   inconsistent with A1–A6 (Section 2.4, the Russell diagonal). The remark
   after Theorem 6.2 that the Russell relation is not the membership of
   any object is a one-line diagonal argument and is not formalised
   separately; nor is the remark that the collapse extends from objects
   to functions, which follows from Theorem 6.2 and Proposition 2.2 in
   one line.
3. No bi-interpretability with Z₂, no conservativity over Z₂, and no
   consistency claim beyond that of Section 4.3 is asserted.

## 8. Checking the proofs yourself

Requirements: Lean 4.33.1, Lake, Git, Python 3.9+.

```text
cd lean
lake exe cache get   # prebuilt Mathlib oleans; otherwise lake build compiles Mathlib from source
lake build
lake env lean --trust=0 FregeanECA/V4/Certificate.lean
python -X utf8 verify.py --lake /absolute/path/to/lake
```

Install the toolchain with [elan](https://github.com/leanprover/elan); it reads
`lean-toolchain` and installs Lean 4.33.1. Lake then fetches the pinned
dependencies into `.lake/packages` on the first build (`lake exe cache get`
downloads prebuilt Mathlib files). The logs of the recorded
audits are in `../verification/`.
