import FregeanECA.V3.Certificate
import FregeanECA.V4.PrintedTheory
import FregeanECA.V4.Choice
import FregeanECA.V4.HumeBridge
import FregeanECA.V4.BiInterpretability
import FregeanECA.V4.TruthValues
import Lean.Util.CollectAxioms

/-!
Certificate for the manuscript. `TF` is the theory exactly as printed
(`Printed.theory`: A1, A2, A3 = functional Basic Law V, A4, A5, with the
defining clauses for application and K/S). `TFenc` is the encoded
presentation of the same theory in which A3 is injective abstraction;
`Printed.provability_iff` shows that the two have the same theorems and
`Printed.axioms_iff_cleaner` that they have the same models. Every endpoint
below is stated for `TF` and for the literal NECA + RC theory `TR`.

Run from lean/: lake env lean --trust=0 FregeanECA/V4/Certificate.lean
The final audit rejects admissions and every extra mathematical axiom.
-/
set_option warningAsError true

namespace FregeanECA.V4.Certificate

open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2
open scoped FFL.FirstOrder

abbrev TF := Printed.theory
abbrev TFenc := V3.Cleaner.theory
abbrev TR := V3.RelationalComprehension.theory
abbrev Z2 := ArithmeticEncoding.theory

theorem tf_of_enc {σ : Sentence language} (h : TFenc ⊢ σ) : TF ⊢ σ :=
  (Printed.provability_iff σ).mpr h

theorem enc_of_tf {σ : Sentence language} (h : TF ⊢ σ) : TFenc ⊢ σ :=
  (Printed.provability_iff σ).mp h

/-- `def:tf`: the printed axiom set has exactly the models and exactly the
theorems of the encoded presentation, and is consistent exactly when it is. -/
theorem printed_theory :
    (∀ {D F : Type} {R : Nat → Type} (M : Interpretation D F R),
      (∀ p, Printed.Axiom p → Valid M p) ↔ (∀ p, V3.Cleaner.Axiom p → Valid M p)) ∧
    (∀ σ : Sentence language, (TF ⊢ σ) ↔ (TFenc ⊢ σ)) ∧
    (Entailment.Consistent TF ↔ Entailment.Consistent TFenc) :=
  ⟨fun M => Printed.axioms_iff_cleaner M, Printed.provability_iff, Printed.consistency_iff⟩

/-- `prop:inverse`: in every model of the printed axioms, δ has an inverse
with the displayed laws and application is evaluation after it. -/
theorem inverse {D F : Type} {R : Nat → Type} [Nonempty F] [∀ n, Nonempty (R n)]
    (M : Interpretation D F R) (h : ∀ p, Printed.Axiom p → Valid M p) :
    type_of% (V3.PaperResults.inverse M ((Printed.axioms_iff_cleaner M).mp h)) :=
  V3.PaperResults.inverse M ((Printed.axioms_iff_cleaner M).mp h)

/-- `prop:inverse`: the closed sentence licensing the definition of application. -/
theorem unique_preimage_provable : TF ⊢ sentence V3.PaperResults.uniquePreimage :=
  tf_of_enc V3.PaperResults.unique_preimage_provable

/-- `prop:blv`: abstract identity iff function identity iff pointwise
agreement, and extensionality of application. -/
theorem basic_law_V_and_extensionality_provable :
    TF ⊢ sentence V3.PaperResults.basicLawVAndExtensionality :=
  tf_of_enc V3.PaperResults.basic_law_V_and_extensionality_provable

/-- `prop:nontriviality`: the one-object countermodel (in which T = F) and the nonderivability
of A5 from the printed A1–A4. -/
theorem nontriviality_independent :
    type_of% Printed.countermodel ∧ type_of% Printed.A5_not_provable :=
  ⟨Printed.countermodel, Printed.A5_not_provable⟩

/-- `thm:correspondence`: K and S exist uniquely from the printed core axioms
and the definition of application. -/
theorem core_combinators_unique {D F : Type} {R : Nat → Type}
    [Nonempty F] [∀ n, Nonempty (R n)] (M : Interpretation D F R)
    (h : ∀ p, Printed.CoreAxiom p → Valid M p) (ev : Valid M evaluation) :
    type_of% (V3.Cleaner.core_combinators_unique M (Printed.core_to_cleaner M h) ev) :=
  V3.Cleaner.core_combinators_unique M (Printed.core_to_cleaner M h) ev

/-- `thm:correspondence`: the same consequences in the shared language. -/
theorem shared_algebra_provability (p : Applicative.Formula) :
    (TF ⊢ sentence p.functional) ↔ (TR ⊢ sentence p.functional) :=
  (Printed.provability_iff _).trans (V3.Certificate.shared_algebra_provability p)

/-- `thm:correspondence`, `thm:arithmetic`, `thm:reverse`, `thm:three-way`:
the six proof-transfer arrows between TF, NECA + RC and Z2. -/
theorem three_way :
    (∀ p : Functional.Formula, (TF ⊢ sentence p) →
      Z2 ⊢ ArithmeticEncoding.sentence (MutualInterpretability.fregeanTranslation p)) ∧
    (∀ p : Applicative.Formula, (TR ⊢ sentence p.functional) →
      Z2 ⊢ ArithmeticEncoding.sentence (Research.Z2Reverse.ReverseProofTransfer.translate p)) ∧
    (∀ p : SecondOrderArithmetic.Formula, (Z2 ⊢ ArithmeticEncoding.sentence p) →
      TF ⊢ sentence (ArithmeticInterpretation.interpret p).functional) ∧
    (∀ p : SecondOrderArithmetic.Formula, (Z2 ⊢ ArithmeticEncoding.sentence p) →
      TR ⊢ sentence (ArithmeticInterpretation.interpret p).functional) ∧
    (∀ p : Functional.Formula, (TF ⊢ sentence p) →
      TR ⊢ sentence (Interpretability.translate p).functional) ∧
    (∀ p : Applicative.Formula, (TR ⊢ sentence p.functional) → TF ⊢ sentence p.functional) :=
  ⟨fun p h => V3.Certificate.cleaner_to_Z2 p (enc_of_tf h),
    V3.Certificate.algebra_to_Z2,
    fun p h => tf_of_enc (V3.Certificate.Z2_to_cleaner p h),
    V3.Certificate.Z2_to_algebra,
    fun p h => V3.Certificate.cleaner_to_algebra p (enc_of_tf h),
    fun p h => tf_of_enc (V3.Certificate.algebra_to_cleaner p h)⟩

/-- `thm:three-way`: equiconsistency. -/
theorem equiconsistency :
    (Entailment.Consistent Z2 ↔ Entailment.Consistent TR) ∧
    (Entailment.Consistent TR ↔ Entailment.Consistent TF) :=
  ⟨V3.Certificate.equiconsistency.1,
    V3.Certificate.equiconsistency.2.trans Printed.consistency_iff.symm⟩

theorem consistent : Entailment.Consistent TF :=
  Printed.consistency_iff.mpr V3.Certificate.consistent

/-- `thm:consistency`: a concrete encoded model of both theories, and
consistency of both. -/
theorem models_and_consistency :
    (∃ M : SmallStruc language, M ⊧* TF ∧ M ⊧* TR) ∧
      Entailment.Consistent TF ∧ Entailment.Consistent TR :=
  ⟨⟨taggedModel openFunctional,
      taggedModel_valid openFunctional Printed.Axiom
        ((Printed.axioms_iff_cleaner _).mpr V3.PaperResults.concrete_models.1),
      taggedModel_valid openFunctional V3.RelationalComprehension.Axiom
        V3.PaperResults.concrete_models.2⟩,
    consistent, V3.Certificate.models_and_consistency.2.2⟩

/-- `thm:bi-interpretability`: proof transfer both ways, `K ∘ M` the identity
on the algebraic language, the isomorphism sentences for `f ↦ δ f` (coverage,
A3, evaluation) derivable in TF, and the translation lemma in every model of
the printed axioms. -/
theorem bi_interpretable :
    (∀ p : Functional.Formula, (TF ⊢ sentence p) →
      TR ⊢ sentence (Interpretability.translate p).functional) ∧
    (∀ p : Applicative.Formula, (TR ⊢ sentence p.functional) → TF ⊢ sentence p.functional) ∧
    (∀ p : Applicative.Formula, type_of% (BiInterpretability.double_translation_provability p)) ∧
    (TF ⊢ sentence coverage) ∧
    (TF ⊢ sentence Printed.A3) ∧
    (TF ⊢ sentence evaluation) ∧
    (∀ {D F : Type} {R : Nat → Type} [Nonempty F] [∀ n, Nonempty (R n)]
      (M : Interpretation D F R) (h : ∀ q, Printed.Axiom q → Valid M q),
      type_of% (BiInterpretability.translation_lemma M ((Printed.axioms_iff_cleaner M).mp h))) :=
  ⟨three_way.2.2.2.2.1, three_way.2.2.2.2.2,
    BiInterpretability.double_translation_provability,
    tf_of_enc BiInterpretability.coverage_provable,
    Printed.lawV_provable,
    tf_of_enc BiInterpretability.evaluation_provable,
    fun M h => BiInterpretability.translation_lemma M ((Printed.axioms_iff_cleaner M).mp h)⟩

/-- `thm:equations`: for both theories, the fixed K/S translation of two open
lambda terms is provably equal iff the terms are beta-eta convertible. -/
theorem exact_equations (M N : Frege.OpenLambda.Term 0) :
    ((TF ⊢ sentence (LambdaInterpretation.equation M N).functional) ↔
      Frege.OpenLambda.BetaEtaConvertible M N) ∧
    ((TR ⊢ sentence (LambdaInterpretation.equation M N).functional) ↔
      Frege.OpenLambda.BetaEtaConvertible M N) :=
  ⟨(Printed.provability_iff _).trans (V3.Certificate.program_equations_both M N).1,
    (V3.Certificate.program_equations_both M N).2⟩

/-- `thm:conservativity`: NECA, NECA + RC and TF prove the same pure
applicative sentences. -/
theorem conservativity (p : Pure.Formula) :
    ((Bare.theory ⊢ Bare.sentence p) ↔ (TR ⊢ sentence p.functional)) ∧
    ((TR ⊢ sentence p.functional) ↔ (TF ⊢ sentence p.functional)) :=
  ⟨(V3.Certificate.pure_conservativity_three_way p).1,
    (V3.Certificate.pure_conservativity_three_way p).2.trans (Printed.provability_iff _).symm⟩

/-- `thm:hume`: Hume's Principle for available concepts on the number domain,
as a closed derivable sentence of both theories. -/
theorem hume_on_number_domain :
    (TF ⊢ sentence HumeInternal.internalHumeSentence.functional) ∧
    (TR ⊢ sentence HumeInternal.internalHumeSentence.functional) :=
  ⟨tf_of_enc HumeBridge.internal_hume_cleaner, HumeBridge.internal_hume_algebra⟩

/-- `cor:frege-theorem`: Z2 proofs transfer to both theories through the
fixed Hume-route translation, independently of the direct interpretation. -/
theorem arithmetic_through_hume :
    (∀ p : SecondOrderArithmetic.Formula, (Z2 ⊢ ArithmeticEncoding.sentence p) →
      TF ⊢ sentence (FregeArithmeticProofTransfer.interpret p).functional) ∧
    (∀ p : SecondOrderArithmetic.Formula, (Z2 ⊢ ArithmeticEncoding.sentence p) →
      TR ⊢ sentence (FregeArithmeticProofTransfer.interpret p).functional) :=
  ⟨fun p h => tf_of_enc (HumeBridge.via_hume_Z2_to_cleaner p h),
    HumeBridge.via_hume_Z2_to_algebra⟩

/-- `prop:hume-expansion`: a common full-relation model of the printed
axioms and of NECA + RC carrying a whole-domain cardinality map that
satisfies HP. -/
theorem whole_domain_hume :
    (∀ p, Printed.Axiom p → Valid Hume.functional p) ∧
    (∀ p, V3.RelationalComprehension.Axiom p → Valid Hume.functional p) ∧
    ∀ P Q : Hume.Relation 0,
      Hume.relationNumber P = Hume.relationNumber Q ↔ Hume.ModelEquinumerous P Q :=
  ⟨(Printed.axioms_iff_cleaner _).mpr HumeBridge.whole_domain_hume_model.1,
    HumeBridge.whole_domain_hume_model.2.1, HumeBridge.whole_domain_hume_model.2.2⟩

/-- A pure applicative sentence derivable in both NECA + RC and TF. -/
abbrev Both (φ : Pure.Formula) : Prop :=
  (TR ⊢ sentence φ.functional) ∧ (TF ⊢ sentence φ.functional)

theorem both_of_enc (φ : Pure.Formula)
    (h : (TR ⊢ sentence φ.functional) ∧ (TFenc ⊢ sentence φ.functional)) : Both φ :=
  ⟨h.1, tf_of_enc h.2⟩

/-- `prop:concepts`: Law V for concepts, quantification over a concept as an
identity, the existential dually, the Boolean connectives as objects, and
closure of concepts under complement, intersection and union. -/
theorem concepts :
    Both TruthValues.lawV ∧ Both TruthValues.universalIdentity ∧
    Both TruthValues.existentialIdentity ∧ Both TruthValues.connectives ∧
    Both TruthValues.closure :=
  ⟨both_of_enc _ TruthValues.lawV_provable,
    both_of_enc _ TruthValues.universalIdentity_provable,
    both_of_enc _ TruthValues.existentialIdentity_provable,
    both_of_enc _ TruthValues.connectives_provable,
    both_of_enc _ TruthValues.closure_provable⟩

/-- `thm:collapse`: every object that is bivalent on the whole domain is
constant, in both theories. -/
theorem collapse : Both TruthValues.collapse :=
  both_of_enc _ TruthValues.collapse_provable

/-- `thm:collapse`, consequences: no object is Frege's horizontal, and hence no
negation stroke, no conditional stroke, no equality test, no bivalent
quantifier object and no whole-domain case operator, in both theories. -/
theorem no_horizontal :
    Both TruthValues.noHorizontal ∧ Both TruthValues.noNegationStroke ∧
    Both TruthValues.noConditionalStroke ∧ Both TruthValues.noEqualityTest ∧
    Both TruthValues.noQuantifierObject ∧ Both TruthValues.noCaseOperator :=
  ⟨both_of_enc _ TruthValues.strokes_provable.1,
    both_of_enc _ TruthValues.strokes_provable.2.1,
    both_of_enc _ TruthValues.strokes_provable.2.2.1,
    both_of_enc _ TruthValues.strokes_provable.2.2.2.1,
    both_of_enc _ TruthValues.strokes_provable.2.2.2.2.1,
    both_of_enc _ TruthValues.strokes_provable.2.2.2.2.2⟩

/-- `prop:choice`: no object is a choice function. FF refutes the instance of
functional choice for the relation y ≠ x(x), so FF + AC_f is inconsistent. -/
theorem no_choice_function : TF ⊢ sentence (notF Choice.choiceInstance) :=
  Choice.no_choice_provable

theorem checked :
    (type_of% V3.Certificate.checked) ∧
    (type_of% printed_theory) ∧
    (type_of% unique_preimage_provable) ∧
    (type_of% basic_law_V_and_extensionality_provable) ∧
    (type_of% nontriviality_independent) ∧
    (∀ p, type_of% (shared_algebra_provability p)) ∧
    (type_of% three_way) ∧
    (type_of% equiconsistency) ∧
    (type_of% models_and_consistency) ∧
    (type_of% bi_interpretable) ∧
    (∀ M N, type_of% (exact_equations M N)) ∧
    (∀ p, type_of% (conservativity p)) ∧
    (type_of% hume_on_number_domain) ∧
    (type_of% arithmetic_through_hume) ∧
    (type_of% whole_domain_hume) ∧
    (type_of% concepts) ∧
    (type_of% collapse) ∧
    (type_of% no_horizontal) ∧
    (type_of% no_choice_function) :=
  ⟨V3.Certificate.checked, printed_theory, unique_preimage_provable,
    basic_law_V_and_extensionality_provable, nontriviality_independent,
    shared_algebra_provability, three_way, equiconsistency, models_and_consistency,
    bi_interpretable, exact_equations, conservativity, hume_on_number_domain,
    arithmetic_through_hume, whole_domain_hume, concepts, collapse, no_horizontal,
    no_choice_function⟩

end FregeanECA.V4.Certificate

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``FregeanECA.V4.Certificate.checked,
    ``FregeanECA.V4.Certificate.printed_theory,
    ``FregeanECA.V4.Printed.axioms_iff_cleaner,
    ``FregeanECA.V4.Printed.provability_iff,
    ``FregeanECA.V4.Printed.consistency_iff,
    ``FregeanECA.V4.Printed.lawV_provable,
    ``FregeanECA.V4.Printed.countermodel,
    ``FregeanECA.V4.Printed.A5_not_provable,
    ``FregeanECA.V4.Certificate.inverse,
    ``FregeanECA.V4.Certificate.unique_preimage_provable,
    ``FregeanECA.V4.Certificate.basic_law_V_and_extensionality_provable,
    ``FregeanECA.V4.Certificate.nontriviality_independent,
    ``FregeanECA.V4.Certificate.core_combinators_unique,
    ``FregeanECA.V4.Certificate.shared_algebra_provability,
    ``FregeanECA.V4.Certificate.three_way,
    ``FregeanECA.V4.Certificate.equiconsistency,
    ``FregeanECA.V4.Certificate.consistent,
    ``FregeanECA.V4.Certificate.models_and_consistency,
    ``FregeanECA.V4.Certificate.bi_interpretable,
    ``FregeanECA.V4.BiInterpretability.bi_interpretability,
    ``FregeanECA.V4.BiInterpretability.double_translation_provability,
    ``FregeanECA.V4.BiInterpretability.translation_lemma,
    ``FregeanECA.V4.Certificate.exact_equations,
    ``FregeanECA.V4.Certificate.conservativity,
    ``FregeanECA.V4.Certificate.hume_on_number_domain,
    ``FregeanECA.V4.Certificate.arithmetic_through_hume,
    ``FregeanECA.V4.Certificate.whole_domain_hume,
    ``FregeanECA.V4.HumeBridge.internal_hume_cleaner,
    ``FregeanECA.V4.HumeBridge.internal_hume_algebra,
    ``FregeanECA.V4.HumeBridge.via_hume_Z2_to_cleaner,
    ``FregeanECA.V4.HumeBridge.via_hume_Z2_to_algebra,
    ``FregeanECA.V4.HumeBridge.whole_domain_hume_model,
    ``FregeanECA.V4.Certificate.concepts,
    ``FregeanECA.V4.Certificate.collapse,
    ``FregeanECA.V4.Certificate.no_horizontal,
    ``FregeanECA.V4.Certificate.no_choice_function,
    ``FregeanECA.V4.Choice.no_choice_provable,
    ``FregeanECA.V4.Choice.choice_fails,
    ``FregeanECA.V4.TruthValues.collapse_provable,
    ``FregeanECA.V4.TruthValues.concepts_provable,
    ``FregeanECA.V4.TruthValues.strokes_provable,
    ``FregeanECA.Part2.FregeArithmeticProofTransfer.interpretation_preserves_falsum,
    ``FregeanECA.V3.Certificate.checked,
    ``FregeanECA.V3.Certificate.program_equations_both,
    ``FregeanECA.V3.Certificate.pure_conservativity_three_way,
    ``FregeanECA.V3.Certificate.models_and_consistency,
    ``FregeanECA.V3.Nontriviality.A5_not_provable,
    ``FregeanECA.V3.PaperResults.inverse,
    ``FregeanECA.V3.PaperResults.unique_preimage_provable,
    ``FregeanECA.V3.PaperResults.basic_law_V_and_extensionality_provable,
    ``FregeanECA.V3.PaperResults.concrete_encoded_models,
    ``FregeanECA.V3.Cleaner.core_combinators_unique,
    ``FregeanECA.V3.Cleaner.inverse_from_zero_and_A3,
    ``FregeanECA.V3.ModelReconstruction.reconstruction]
  for endpoint in endpoints do
    for ax in ← collectAxioms endpoint do
      unless allowed.contains ax do
        throwError "V4 CERTIFICATE REJECTED at {endpoint}: {ax}"
  logInfo "V4 CERTIFICATE PASS: the printed theory (A3 = functional Basic Law V) has the models and theorems of the encoded presentation; every V3 endpoint, bi-interpretability, exact beta-eta equations, conservativity over NECA, Hume's Principle on the number domain, the Hume-route Z2 transfer, the whole-domain Hume model, the connectives as objects, the collapse of total concepts, and the impossibility of Frege's horizontal, all for the printed theory; standard Lean axioms only."

#print axioms FregeanECA.V4.Certificate.checked
