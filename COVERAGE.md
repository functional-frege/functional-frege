# Version 4 paper-to-proof correspondence

The active manuscript is [main.tex](paper/main.tex). It has six sections,
**twenty-one numbered results and three definitions**, three of the results
being numbered remarks (2.5, 3.9 and 3.16) with Lean proofs like the rest, and
one appendix (Appendix A), which states the internal lemmas (A.1)–(A.5) behind
Theorem 3.10 together with the Lean declaration proving each, all in
`FregeanECA/Research/Z2Reverse`. This index covers every printed result and
its explicit auxiliary arguments, recording both the statement and the method
used in Lean. Stable
TeX labels avoid dependence on pagination.

Version 4 adds the bi-interpretability theorem, the truth-value results
(the connectives as objects and the collapse of total concepts), and
reinstates, as printed results, the applicative-fragment proposition (exact
lambda equations and pure applicative conservativity), Hume's Principle on
the number domain, the Hume-route interpretation of Z2, and the whole-domain
Hume model. Section 3 of the manuscript (Interpretations) now holds every
interpretability result; Section 4 holds the truth-value results. The
Hoare-style composition rule and the successor-composition example remain
checked companion results and are not printed. No Lean source or verification
endpoint was removed.

Unless a row says otherwise, theorem names start with `FregeanECA`. The printed
functional theory is upright FF (Functional Frege); `V4.Certificate.TF` is `V4.Printed.theory`, the theory exactly as printed
(the six axioms `Printed.A1`–`A6`); `V3.Certificate.TF` is `V3.Cleaner.theory`, the
encoded presentation, in which A2 applies δf to all inputs and admits parameters
and the empty input list, A3 is injective abstraction and the nontriviality clause is ∃x,y x ≠ y. `V4.Printed.axioms_iff_cleaner`
and `V4.Printed.provability_iff` prove that the two presentations have the same
models and the same theorems, and every V4 certificate endpoint is stated for
the printed theory.
`V4.Certificate.TR` is exactly NECA plus full relational comprehension
(`V3.RelationalComprehension.theory`), not the historical closure-axiom
presentation renamed without a proof. NECA is the printed name for the
nontrivial extensional combinatory algebra encoded by the existing Lean ECA
identifiers. The main certificate is
[V4/Certificate.lean](lean/FregeanECA/V4/Certificate.lean); it restates every
endpoint of [V3/Certificate.lean](lean/FregeanECA/V3/Certificate.lean) and adds
the modules [V4/BiInterpretability.lean](lean/FregeanECA/V4/BiInterpretability.lean),
[V4/HumeBridge.lean](lean/FregeanECA/V4/HumeBridge.lean) and
[V4/TruthValues.lean](lean/FregeanECA/V4/TruthValues.lean).

## What counts as a matching proof

A native semantic result quantifies over the actual interpretations and their
axioms. A syntactic result uses Foundation's actual `Theory.Proof` derivability
or `Entailment.Consistent`, with the object theories encoded as axiom sets.
These are different statements. Where the manuscript says a theory proves a
formula, the index identifies the derivability endpoint, not just an informal
inference from semantic validity. Inverse notation is authorized by a proved
unique-preimage sentence; the cross-sort inverse is not an added function-sort
object or a new axiom. Definitional abbreviations themselves are not separate
mathematical claims requiring independent existence proofs.

Several proof transfers use source soundness, a specified model construction,
and target first-order completeness. They are actual derivability theorems,
but they are not implemented as recursive transformations of proof trees. The
paper describes that same method. Model reconstruction is a semantic
statement. The companion specification rule is also semantic and is identified
separately below.

## Definitions and exact theories

| Paper definition | Lean definition / justification | Exact scope |
| --- | --- | --- |
| `def:tf`: A1–A6 | [PrintedTheory.lean](lean/FregeanECA/V4/PrintedTheory.lean): `Printed.A1`–`Printed.A6`, `CoreAxiom`, `theory`; [Cleaner.lean](lean/FregeanECA/V3/Cleaner.lean) for the encoded presentation | The six printed axioms are written out directly: A1 full relational comprehension (|x̄| ≥ 1); A2 functional comprehension ∃f ∀x̄ (f(x̄) = θ(x̄)) for |x̄| ≥ 1, f(x̄) being f evaluated at the first input and the resulting object applied to the rest, and θ an application term whose variables are all among the inputs (a closedness side condition on the term); A3 Basic Law V (`lawV`); A4 function extensionality; A5 coverage ∀y ∃f (δf = y); A6 nontriviality, printed as T ≠ F for the abstracts of the two projections. `Printed.axioms_iff_cleaner` and `provability_iff` prove that these six have exactly the models and theorems of the encoded presentation `V3.Cleaner.theory` (whose A2 admits parameters and the empty input list, and whose A3 is injective abstraction and A5 is ∃x,y x ≠ y); the direction from the printed axioms uses `Printed.parametric_comprehension`. |
| `def:eca`: E1–E4 | `Pure.ECAConditions`; `Axioms.ECAAxiom`; `Bare.theory` | Total K/S algebra, application extensionality, and two distinct objects. No arithmetic primitives or relation comprehension are hidden in the pure theory. |
| `def:ta`: ECA + RC | [RelationalComprehension.lean](lean/FregeanECA/V3/RelationalComprehension.lean): `Axiom`, `theory` | Exactly E1–E4 and full comprehension in the applicative relational language. `closure_provability` proves the bridge to the inherited B/C/Q presentation used internally by older proofs. |

The encoded signature already carries application and K/S. `DefinitionAxiom`
separately records evaluation and their defining equations. Application is
uniquely recovered after the zero case of A2 and A3; K/S witnesses are uniquely
derived before their names are fixed. These are accounted-for defining clauses,
not additional numbered core axioms. Lean's internal relation index `R n` has
arity `n+1`; the paper's index is the actual positive arity. Neither presentation
assumes relation identity extensionality. Relation domains are Henkin domains,
not obligatorily full powersets.

## Every numbered result

| Paper result and complete statement | Lean endpoint(s) | Matching proof method |
| --- | --- | --- |
| `prop:parametric`: functional comprehension with parameters, ∀ȳ ∃f ∀x̄ (f(x̄) = θ(x̄, ȳ)) for every application term θ with |x̄| ≥ 1, and ∀ȳ ∃f (δf = θ(ȳ)) for |x̄| = 0, is a theorem of A1–A6 | `Printed.parametric_comprehension`, `Printed.parametric_comprehension_provable`; `V4.Certificate.printed_theory` (conjuncts 4 and 5) | In every model of the printed axioms: K and S exist by the closed A2 instances, the bracket lemma `Positive.terms_have_codes` represents the parametric term by an object z with z·x̄ = θ, and coverage gives h with δh = z; every V3.Cleaner A2 instance, parameters and empty input list included, is therefore valid, and the encoded A2 instances are derivable by completeness. The derived instances are stated with the encoded left side (δf)·x̄; the paper's f(x̄) agrees with it by one application of Frege's law (δf)·x₁ = f(x₁), the evaluation clause, which is `Printed.A2_iff_cleaner`. |
| `prop:inverse`: delta is bijective; inverse graph iff, two inverse laws, recovered application, and `(delta f) · x = f(x)` | [PaperResults.lean](lean/FregeanECA/V3/PaperResults.lean): `V3.PaperResults.inverse`, `unique_preimage_provable`; `V3.Cleaner.inverse_from_zero_and_A3` | Coverage (A5; in the encoded presentation the zero-input A2 instance) gives surjectivity; A3 with A4 gives injectivity. Choose the unique preimage and derive all displayed equations. `unique_preimage_provable` proves the actual closed sentence `forall x exists f forall g (g=f iff delta g=x)` by completeness, authorizing the definition. The full displayed inverse/evaluation bundle is then a native theorem about that defined map. |
| `prop:blv`: abstract identity iff function identity iff pointwise agreement, and object application extensionality | `V3.PaperResults.basicLawVAndExtensionality`, `basic_law_V_and_extensionality_valid`, `basic_law_V_and_extensionality_provable` | A3, A4, substitution of equals and the recovered evaluation equation give the semantic result; completeness gives the closed derivability statement containing both equivalences and E3. |
| `prop:nontriviality` (Remark 2.5): A6 is not derivable from A1–A5 | `V4.Certificate.nontriviality_independent`; [PrintedTheory.lean](lean/FregeanECA/V4/PrintedTheory.lean): `Printed.FirstFive`, `countermodel`, `A6_not_provable`; [Nontriviality.lean](lean/FregeanECA/V3/Nontriviality.lean): `FirstFour`, `Axiom`, `model`, `countermodel`, `A5_not_provable` (the encoded presentation, whose fifth clause is ∃x,y x ≠ y) | Use singleton objects/functions and all relations. Verify every literal remaining schema and every defining equation; refute A5. Foundation soundness gives actual nonderivability. This is no longer a written-only countermodel. |
| `lem:bracket`: every finite application term, with parameters and possibly no inputs, has a representative in every K/S algebra | `Positive.terms_have_codes`; `Frege.CombinatorTerm.applying_an_abstraction_substitutes_its_argument`; `closeTerm_spec` | The same bracket recursion and structural induction: I/K handle variables and coefficients; S handles applications; repeated abstraction closes the inputs in reverse order. Empty abstraction returns the term value. No extensionality is used. |
| `thm:correspondence`: mutual interpretations and equality of all shared-language sentence consequences | `V3.Certificate.shared_algebra_provability`, `cleaner_to_algebra`, `algebra_to_cleaner`; `V3.Cleaner.core_combinators_unique` | A2 supplies K/S, A3/A4 supply E3, and A5 supplies E4. Conversely copy the object sort into the function sort, preserve every relation sort and translate evaluation/identity/quantifiers. Full comprehension and bracket representation verify the axioms. Fixed model lifts plus soundness/completeness establish proof transfer and shared-language equivalence. |
| `prop:reconstruction`: algebra round trip is unchanged; functional round trip is isomorphic through delta with identity on objects/relations | [ModelReconstruction.lean](lean/FregeanECA/V3/ModelReconstruction.lean): `algebra_round_trip`, `reconstruction`, `formula_round_trip` | Copy expansion is definitionally unchanged on the algebraic reduct. The delta bijection preserves abstraction and evaluation; the formula truth theorem includes function identity and both function/relation quantifiers. This is model reconstruction, not a claim about a category of morphisms. |
| `thm:bi-interpretability`: FF and NECA + RC are bi-interpretable; κ∘μ is the identity on the algebraic language; f ↦ δf is provably an isomorphism from the identity to μ∘κ | `V4.Certificate.bi_interpretable`; [BiInterpretability.lean](lean/FregeanECA/V4/BiInterpretability.lean): `bi_interpretability`, `double_translation_validity`, `double_translation_provability`, `coverage_provable`, `injective_abstraction_provable`, `evaluation_provable`, `translation_lemma`; `V3.Certificate.cleaner_to_algebra`, `algebra_to_cleaner` | The certificate states the conjunction that the definition requires: proof transfer both ways (the two interpretations); interderivability in NECA + RC of every algebraic sentence with its double translation `translate (p.functional)` (κ∘μ renames variables only); derivability in FF of the isomorphism sentences for f ↦ δf, namely coverage (surjective), A3 (injective, preserves function identity) and the evaluation law f(x) = (δf)·x (commutes with evaluation), the remaining commutation sentences being syntactic identities; and the translation lemma of `prop:reconstruction` in every model. The general notion of interpretation is not formalised. |
| `lem:successor`: with zero I and successor K-application, successor is injective and never zero in a nontrivial combinatory algebra | `Part2.Arithmetic.successor_injective`, `zero_not_successor` | Apply equal successor codes to I. If a successor equals I, apply to arbitrary objects and contradict nontriviality. This proof requires K/S and nontriviality, not application extensionality. |
| `thm:arithmetic`: both NECA + RC and FF interpret all Z2 axioms and proofs | `Part2.ArithmeticInterpretation.Z2_proof_transfer`; `V3.Certificate.Z2_to_algebra`, `Z2_to_cleaner` | Least-domain induction, least addition/multiplication graphs, available-set quotient and full comprehension produce the interpreted arithmetic structure. Source soundness and target completeness yield the fixed proof transfer. Detailed steps are indexed below. |
| `thm:reverse`: one fixed interpretation translates the whole NECA + RC formula grammar and transfers all its proofs to Z2 | `Research.Z2Reverse.ReverseProofTransfer.translate`, `source_semantics`, `algebra_proof_transfer`; `V3.Certificate.algebra_to_Z2` | Internal term/conversion coding in arbitrary source arithmetic models; internally proved confluence and separation; quotient objects and saturated available source sets; truth induction and comprehension transfer; source-model semantics plus soundness/completeness. Detailed code/guard scope is below. |
| `thm:three-way`: six proof-transfer directions and three-way equiconsistency | `V3.Certificate.three_way`, `equiconsistency` | Compose the established translations. Their falsum results transfer inconsistency; the consistency proof follows these transfers rather than pairing unrelated consistency theorems. No bi-interpretability with Z2 is asserted. |
| `thm:consistency` (Remark 3.9, the open-term model): NECA + RC and FF have models and are consistent | `V3.Certificate.models_and_consistency`; `V3.PaperResults.concrete_models`, `concrete_encoded_models` | Open lambda-term quotient gives a nontrivial ECA by confluence and fresh-variable eta extensionality; powersets give full comprehension; the function copy satisfies the literal cleaner axioms. `concrete_encoded_models` gives a Foundation model of both exact V3 theories; soundness gives consistency. This theorem is in Lean's metatheory. No Con(ZFC) implication is part of its statement. |
| `prop:applicative`: (i) NECA, NECA + RC and FF prove the same pure classical applicative sentences; (ii) for NECA, NECA + RC and FF and every finite open untyped M, N, translated equation provability iff beta–eta conversion, and the pointwise form | (i) `V4.Certificate.conservativity` = `V3.Certificate.pure_conservativity_three_way`; `Part2.bare_eca_full_algebra_provability`. (ii) `V4.Certificate.exact_equations` = `V3.Certificate.program_equations_both` (NECA + RC and FF); `Part2.ProgramEquations.bare_program_equation_iff` (NECA alone), `bare_pointwise_program_equation_iff`, `full_functional_pointwise_program_equation_iff`, `full_algebra_pointwise_program_equation_iff`; translation `LambdaInterpretation.translation` via the vendored bracket algorithm `Frege.CombinatorTerm.fromProgram` | (i) Expand every ECA by all relations without changing objects or application; a pure formula keeps its truth value, then soundness/completeness and the functional/algebraic correspondence. The scope includes quantifiers and negation, not just equations. (ii) Bracket substitution and extensionality preserve conversion in every ECA, then completeness gives provability; for the converse use the open-term quotient and the assignment sending each free name to its own class. The same fixed K/S translation is used throughout; equations are universally closed and terms need not normalize. The pointwise form is transferred through the same conservativity bridge. The paper cites the NECA case to Barendregt; the development proves it (`bare_program_equation_iff`). |
| `prop:concepts`: negation, conjunction and disjunction are objects with their truth tables on {T, F}, and for every object `c`, `∀x (c·x = T) ↔ c = K·T`, in NECA + RC and FF | `V4.Certificate.concepts` = `V4.TruthValues.concepts_provable` (components `connectives_provable`, `universalIdentity_provable`); [TruthValues.lean](lean/FregeanECA/V4/TruthValues.lean): `connectives`, `universalIdentity` (sentences); `negation_sem`, `conjunction_sem`, `disjunction_sem`, `universal_sem` (semantic proofs); `bare_of_valid`, `both_of_bare` (completeness and transfer) | T := K and F := K·I. Each statement is a pure applicative sentence, proved valid in every structure satisfying `Pure.ECAConditions` (explicit bracket abstraction `Poly.abs` with `Poly.abs_apply` for the connectives; E3 for the identity), lifted to `Bare.theory` by `Theory.Proof.complete_on_eq_models`, and transferred to both literal theories by `V3.Certificate.pure_conservativity_three_way`. The bundle `concepts_provable` also contains `lawV_provable`, `existentialIdentity_provable` and `closure_provable`, checked companions that are not printed because `thm:collapse` makes them statements about the two objects `K·T` and `K·F` only. |
| `thm:collapse`: every bivalent object is constant, `∀c (∀x (c·x = T ∨ c·x = F) → ∀x (c·x = T) ∨ ∀x (c·x = F))`; consequently no object is a truth test (Frege's horizontal), a total negation, a total conditional, an equality test, a bivalent quantifier object or a whole-domain case operator, in NECA + RC and FF | `V4.Certificate.collapse` = `V4.TruthValues.collapse_provable`; `V4.Certificate.no_horizontal` = `V4.TruthValues.strokes_provable`; [TruthValues.lean](lean/FregeanECA/V4/TruthValues.lean): `collapse`, `noHorizontal`, `noNegationStroke`, `noConditionalStroke`, `noEqualityTest`, `noQuantifierObject`, `noCaseOperator` (sentences); `fixed_point`, `collapse_sem`, `no_horizontal_sem`, `no_negation_stroke_sem`, `no_conditional_stroke_sem`, `no_equality_test_sem`, `no_quantifier_object_sem`, `no_case_operator_sem` | `fixed_point` builds `m := S·(K·g)·(S·I·I)` with `m·m = g·(m·m)` from E1–E2 alone. `collapse_sem`: if `c·a = T` and `c·b = F`, the fixed point `w` of `z ↦ c·z·b·a` gives `w = b` when `c·w = T` and `w = a` when `c·w = F`, so `T = F` either way, against nontriviality. The printed consequences are certified by the separate reductions of `strokes_provable`, each of which exhibits a truth test by an explicit bracket abstraction (`n·(n·x)`, `e·x·T`, `q·(K·x)`, `d·x·T·T·F`; a total conditional gives a total negation `c·x·F`) and refutes it by `no_horizontal_sem`, the same fixed-point argument for `z ↦ h·z·F·T`. Completeness and the conservativity bridge as for `prop:concepts`. |
| `prop:choice`: FF proves the negation of the instance of functional choice for the formula y ≠ x·x; hence FF + AC_f is inconsistent | `V4.Certificate.no_choice_function`; [Choice.lean](lean/FregeanECA/V4/Choice.lean): `choiceInstance`, `choice_fails`, `no_choice_provable` | Semantic refutation in every model of the printed axioms: two distinct objects (A6) make the relation total, and a chooser g applied to its own abstract gives g(δg) ≠ (δg)(δg) = g(δg) by the evaluation law; completeness gives derivability. A2 is not used. |
| `thm:hume`: NECA + RC and FF prove the closed sentence `exists N (Nat(N) and UC_N and HP_N)` | `V4.Certificate.hume_on_number_domain`; `V4.HumeBridge.internal_hume_cleaner`, `internal_hume_algebra`; `Part2.HumeInternal.internalHumeSentence`, `internal_hume_provable`, `internal_hume_provable_fregean`, `humes_principle`, `code_total_unique` | The counting relation, rank bijection, initial-segment pigeonhole and case comparison are the semantic proof `HumeInternal.humes_principle` in every full Henkin model with the derived Peano domain; `internal_hume_sentence_valid` assembles the literal sentence; completeness gives derivability for the Part II presentations; the certified bridges `V3.Cleaner.provability_iff_fullFE`, `FunctionExtensionality.original_proof_in_extension`, `V3.RelationalComprehension.closure_provability` and `V2.combined_full_original_provability` transfer it to FF in its encoded presentation (`V3.Cleaner.theory`; the V4 certificate restates it for the printed A1–A6 through `Printed.provability_iff`) and NECA + RC. Codes: size n receives s(n); no size receives 0. |
| `cor:frege-theorem`: a fixed Hume-route interpretation carries every Z2 proof into both theories, independently of `thm:arithmetic` | `V4.Certificate.arithmetic_through_hume`; `V4.HumeBridge.via_hume_Z2_to_cleaner`, `via_hume_Z2_to_algebra`; `Part2.FregeArithmeticProofTransfer.interpret`, `via_hume_Z2_proof_transfer`, `via_hume_Z2_proof_transfer_fregean`, `interpretation_preserves_falsum`; `Part2.StandardFregeRoute.part_two_has_frege_peano` | Frege zero, predecession, the ancestral number domain, successor existence through the downset argument, and the recursion graphs on the Frege carrier are the `FregeArithmetic*` modules; the fixed translation composes them with the cardinal-code graph; soundness in the constructed structure and target completeness transfer proofs; the same bridges as `thm:hume` move the result to the literal theories. |
| `cor:fa`: Frege Arithmetic (FA) and FF are mutually interpretable, hence equiconsistent | `V4.Certificate.frege_arithmetic`; [FregeArithmetic.lean](lean/FregeanECA/V4/FregeArithmetic.lean): `FAValid`, `toFF`, `toFA`, `ff_interprets_fa`, `fa_interprets_ff`, `fa_interprets_algebra`, `fa_model_of_ff_model`, `ff_model_of_fa_model`, `printed_model_of_fa_model` | FA is rendered by its Henkin models, `Part2.FregeArithmetic.Interpretation` with `FullConditions` (Hume's Principle and full comprehension in the generic FA grammar), and FA-provability by validity in all of them (`FAValid`); the two coincide by the completeness theorem, which is not formalised for the FA language, since FA is not an encoded Foundation theory. FF to FA: `toFF` is the `cor:frege-theorem` interpretation (objects the least-inductive number domain, concepts the available relations on it, `#` the cardinal code), and every FA-valid formula is carried to a TF theorem by the same completeness bridge as `cor:frege-theorem`. FA to FF: every TF theorem is transferred to Z2 by `thm:three-way`, is valid in the Z2 model inside every FA model (`FregeArithmeticZ2.hume_proof_truth`), and so its `sourceFormula` holds in every FA model. Model level: every FF model with a number domain carries an FA model (`interpreted_full_conditions`), and every FA model carries an encoded Z2 model (`hume_constructs_Z2_model`) and, through the Z2Reverse source-model construction, a model of FF satisfying every printed axiom (`printed_model_of_fa_model`). Equiconsistency is certified through these model halves (FA has a Henkin model iff FF has a model), not through falsum preservation of `toFF`/`toFA`. FA's generic language has an identity atom on relation representatives with no extensionality axiom, and `FAValid` ranges over all Henkin models; for formulas without that atom, the second-order language of FA proper, this is immaterial. `toFF` is stated for sentences and formulas with only relation parameters, as `cor:frege-theorem` is. The general notion of interpretation is not formalised, as noted above. |
| `prop:hume-expansion` (Remark 3.16): a common full-relation model of both literal theories, on the carrier Nat, expanded by a cardinality map satisfying whole-domain HP | `V4.Certificate.whole_domain_hume`; `V4.HumeBridge.whole_domain_hume_model`; `Part2.Hume.part_two_has_hume_expansion`, `model_humes_principle`, `number`; `Part2.NaturalECA.algebra` | The open-term algebra is transported to Nat; every relation is available; `number` sends a finite predicate with n instances to n+1 and an infinite predicate to 0; finite-cardinality and countable-infinity arguments give HP. `whole_domain_hume_model` verifies the literal V3/V4 axiom sets on the copy expansion through `V3.Cleaner.axioms_iff_fullFE`. Model existence, not derivability of whole-domain HP. |

## Auxiliary derivations and definitions used in those proofs

### Coverage, definitions and representation

- `V3.Cleaner.coverage_from_zero` uses the arbitrary free object parameter in
  the empty instance, not an infinitary collection of named instances.
  `zero_instance_proves_coverage` proves the universally closed coverage
  sentence from that one closed A2 instance using validity and completeness.
- `V3.Cleaner.inverse_from_zero_and_A3` requires neither FE nor an application
  equation to obtain the inverse. `core_combinators_unique` derives unique K/S
  from the core axioms and the application definition. Their uniqueness uses
  application extensionality once per argument.
- The technical bridge to the older separate-coverage implementation is
  `V3.Cleaner.axioms_iff_fullFE` and `provability_iff_fullFE`. It covers every
  encoded sentence of the common defined signature. This is an implementation
  dependency, not a separate contribution or an additional theory advertised
  in the paper.
- The distinction between full relations and represented tests has an actual
  diagonal witness in
  `Part2.full_comprehension_excludes_unrestricted_predicate_representation`:
  for a fixed result value, not every available unary relation has a native
  characteristic test. A1 does not silently become functional-graph
  comprehension.

### Arithmetic construction: statement and method details

| Step used in `thm:arithmetic` | Checked endpoint(s), relative to `Part2` | Method / scope |
| --- | --- | --- |
| Available least inductive relation N; zero and successor closure | `Arithmetic.least_inductive_domain`, `least_zero`, `least_successor`, `full_ts_has_peano_domain` | Comprehend the actual least-inductive formula, quantifying over available unary relations. |
| Induction for every formula on N | `Arithmetic.represented_formula_induction`; `ArithmeticInterpretation.domain_of_definition` | Comprehend the formula and intersect its extension with N; leastness places N inside the inductive intersection. |
| Least addition relation A | `Arithmetic.full_has_least_addition`; `ArithmeticInterpretation.least_addition_iff_definition` | Full comprehension for the displayed intersection of addition-closed ternary relations. |
| A is supported on N cubed; the displayed one-step Q agrees with A | `Arithmetic.addition_support`, `addition_inversion` | N cubed is addition-closed. Comprehend the base-or-step relation Q; prove Q is contained in A and closed; use minimality for the reverse inclusion. |
| Addition existence, uniqueness and recursion | `Arithmetic.addition_total_unique`, `addition_zero_recursion`, `addition_successor_recursion` | Formula induction, the inversion theorem, zero-not-successor and successor injectivity. |
| Least multiplication, support and one-step inversion | `Arithmetic.full_has_least_multiplication`, `multiplication_support`, `multiplication_inversion` | The same comprehension/minimality argument, using the already established addition graph. |
| Multiplication existence, uniqueness and recursion | `Arithmetic.multiplication_total_unique`, `multiplication_zero_recursion`, `multiplication_successor_recursion` | Formula induction and addition totality/uniqueness at the successor step. Both operations recurse on the first argument, as printed. |
| Sets of numbers and extensional identity | `SecondOrderArithmetic.SetDomain`, `representedSet_surjective`, `set_identity_iff_coextension` | Represent sets by the extensions of available unary relations on N. This identifies coextensive representatives without imposing relation identity extensionality on FF or NECA + RC. |
| Arithmetic terms and formulas translate correctly | `SecondOrderArithmetic.Term.graph_truth`, `Formula.translation_preserves_truth` | Structural induction; arithmetic terms use their unique graph values and set quantifiers use available representatives. |
| All comprehension, induction and remaining Z2 axioms | `SecondOrderArithmetic.source_formula_comprehension`, `source_formula_induction`, `all_axioms_valid` | Actual translated formulas, not arbitrary external predicates. Full formula grammar and set parameters/quantifiers are included. |
| Fixed interpretation and actual proof transfer | `ArithmeticInterpretation.definitions_exist`, `interpret`, `interpreted_valid`, `interpreted_provable`, `Z2_proof_transfer` | Existentially bind N and the two graphs with their proved definitions; guard free number parameters; apply source soundness and target completeness. No syntactic induction on Foundation proof trees is claimed. |

### Reverse interpretation: internal codes, available sets and guards

All names in this paragraph are relative to `Research.Z2Reverse`.
`InternalSourceModel.eca` and `full_comprehension` discharge the actual target
conditions from `ModelsZ2`; neither assumes an externally supplied ECA or full
powerset relation domains. The proof uses the source model's own arithmetic
carrier, so terms and derivation paths may have nonstandard coded lengths.

`InternalParallelBeta.parallel_diamond`, `InternalEtaReduction.eta_confluent`,
`InternalBetaEtaCommutation.commute`, and
`InternalQuotientNontriviality.betaeta_church_rosser` establish the printed
confluence argument. `free_names_convert_iff` and `quotient_nontrivial` supply
separation. `InternalExtensionality.extensional` supplies the fresh-variable
eta argument. These are internal coded facts, not standard-Nat replacements.

The fixed decoding is total on source numbers: invalid or ill-scoped codes
map to a fixed free-variable object. Thus translated object quantifiers range
over **all source numbers**, not a silently assumed valid-code subdomain.
`RelationCoding.Saturated` and `Relation` use available source sets invariant
under equality of decoded tuples; relation-representative identity remains
source identity. `GuardedFormulaTranslation.predicateBound`, `guards`,
`translate_truth_bounded` and `guarded_validity_iff` keep the arity/free-parameter
bounds finite. `InternalConversionFormula.definitions` and
`GuardedFormulaTranslation.translate_eq` identify one fixed translation,
independent of the chosen source model.

`InternalSourceModel.full_comprehension` obtains each relation from an actual
source comprehension instance. `ReverseProofTransfer.source_semantics` gives
the exact sentence truth theorem for arbitrary source models. Its
`algebra_proof_transfer` then uses target proof soundness in that constructed
model and source completeness. The V3 certificate transfers through the proved
direct-RC bridge, so the final source theory is exactly NECA + RC.

## Checked companion results not printed in the paper

These results remain covered by the passing formal audit. Their absence from
the current manuscript is a scope decision, not a removal or weakening of
their formal statements.

| Companion result | Lean endpoint(s) | Matching proof method |
| --- | --- | --- |
| Hoare-style composition: composition equation, composition rule, available binary graph independent of pre/post hypotheses, and graph consequence | `V3.PaperResults.specification`; [Specifications.lean](lean/FregeanECA/V3/Specifications.lean): `composition_correct`, `composition_specification`, `composition_graph`, `graph_specification` | S/K equations establish composition; compose the two implication hypotheses; one actual full-comprehension instance supplies the graph; substitute its output equality. The bundle assumes the actual cleaner axioms and quantifies over available relation objects. It does not assume representation of arbitrary metatheoretic predicates. |

### Exact successor-composition example

[SuccessorVerification.lean](lean/FregeanECA/V3/SuccessorVerification.lean)
checks the retained companion example, which is no longer printed in the paper. `twiceLambda` is the open term
`lambda x. k (k x)`; `code` applies the fixed bracket translation and the
substitution `[K/k]`. `code_application` proves its second-successor output,
and `code_is_composition` identifies that actual code with `S (K K) K` by
extensionality. `verifies` derives the triple from the available number
relation's successor closure and the composition rule. `available_domain`
supplies such a relation using A1. Neither result assumes arbitrary external
predicates are available or asserts operational termination.

`code_identity_provable` and `specification_provable` additionally prove the
actual closed Foundation sentences in FF. The specification is guarded by
the exact defining formula for the available number relation. All four
terminal endpoints are required by both the V3 certificate and the full
verification script.

## Verification status and limitations

The verification record is [verification.json](verification/verification.json),
which records the actual commands, exit codes, source hashes and audit result
of the most recent fresh-source run of `lean/verify.py`. The incremental
build and the `--trust=0` check of the V4 certificate are recorded in
[build.log](verification/build.log) and
[v4-certificate-incremental.log](verification/v4-certificate-incremental.log).
The fresh-source audit of 29 October 2026 (final run, after the Lean comments
were aligned with the restructured paper; the printed-theory module
`V4/PrintedTheory.lean` states the six axioms with A3 = Basic Law V, A5 = coverage and A6 = T ≠ F, and the choice
module is `V4/Choice.lean`) **passed**: 180 project modules, 19 vendored
modules, 7,899 audited declarations, 306 required endpoints, no
admissions, unexpected axioms, missing endpoints or source drift. See
[verification/README.md](verification/README.md) for the file-by-file
description. The recorded hashes identify the verified sources; this index
additionally checks the correspondence of the printed statements and
arguments with those sources.

Permitted foundational axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`. The object theories are encoded axiom sets, not new Lean axioms.
The certificate audit rejects admissions and extra mathematical axioms. Its
small entry files import proved dependencies: they are not independent proofs
with no library or foundational assumptions. Kernel checking verifies the stated
types in this metatheory; it does not decide arbitrary truth.

The previous Con(ZFC) implication was removed from the numbered consistency
result because no encoded ZFC proof transfer was formalized. No written-only
singleton claim remains. Historical results cited in the comparison section
are attributed to their sources, not claimed as new Lean theorems in this
project. Whole-domain HP is asserted only as model existence
(`prop:hume-expansion`), never as a theorem of the axioms. No
bi-interpretability with Z2, arithmetic conservativity over Z2, or decision
procedure for arbitrary specifications is asserted.
