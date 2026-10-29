import FregeanECA.V3.Certificate
import FregeanECA.V4.PrintedTheory
import FregeanECA.Part2.FregeArithmeticProofTransfer

/-!
`cor:fa`: Frege Arithmetic and FF are mutually interpretable.

Frege Arithmetic (FA) is Hume's Principle plus full comprehension in the
generic source language `Part2.FregeArithmetic`: number abstraction on unary
predicates, relation variables of every arity, no ECA, no Peano domain and
no arithmetic interpretation assumed. FA is represented here by its Henkin
models, the interpretations satisfying `Part2.FregeArithmetic.FullConditions`,
and FA-provability by validity in all of them (`FAValid`).

Both directions are fixed formula translations.

* `toFF` is the Corollary 7.2 interpretation (`cor:frege-theorem`): the
  number domain is fixed by its least-inductive definition, a number witness
  guards the default object assignment, and the FA formula is read on the
  internal number domain with the internal cardinality map
  (`FregeArithmeticInterpretation.translate`). `toFF_valid` is the translation
  lemma in every full TS model of FF, and `ff_interprets_fa` transfers
  FA-validity to a derivation from the printed axioms, by completeness over
  the equality models of the Part II algebra theory and the certified bridges
  to `Printed.theory`. `FregeArithmeticProofTransfer.interpret` is `toFF`
  applied to the FA source formula of a Z2 sentence (`interpret_eq`).
* `toFA` goes through Z2: the certified TF -> Z2 translation
  (`MutualInterpretability.fregeanTranslation`, `thm:three-way`) followed by
  the FA source formula of a Z2 sentence
  (`FregeArithmeticProofTransfer.sourceFormula`), which is valid in every FA
  model by Frege's theorem (`source_formula_valid`). `fa_interprets_ff`
  transfers every TF theorem to FA-validity.

The model-theoretic halves are recorded as well: every full TS model of FF
carries an FA model on its number domain (`fa_model_of_ff_model`), and every
FA model yields a full TF model of FF through its internal Z2 model
(`FregeArithmeticZ2.hume_constructs_Z2_model`) and the internal term model of
`thm:reverse` (`InternalSourceModel.extracted_fullTF`), see
`ff_model_of_fa_model`. No new axiom and no new model construction is
introduced in this file.
-/
namespace FregeanECA.V4.FregeArithmetic

open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2 Positive
open scoped FFL.FirstOrder

universe u v

/-- Validity in every Henkin model of Frege Arithmetic (HP plus full
comprehension in the generic FA language), under every assignment. -/
def FAValid (ψ : Part2.FregeArithmetic.Formula) : Prop :=
  ∀ {D : Type u} {R : Nat → Type v} (M : Part2.FregeArithmetic.Interpretation D R),
    Part2.FregeArithmetic.FullConditions M →
    ∀ (o : ObjectAssignment D) (r : PredicateAssignment R), ψ.truth M o r

/-! ### FA into FF: the Corollary 7.2 translation -/

/-- The Corollary 7.2 translation of an FA formula into the applicative
language: the number domain `N` is fixed by its least-inductive definition,
a number witness guards the default object assignment, and the formula is
read on the internal number domain by `FregeArithmeticInterpretation.translate`.
This is the body of `FregeArithmeticProofTransfer.interpret` with the FA
source formula of a Z2 sentence replaced by an arbitrary FA formula. -/
def toFF (ψ : Part2.FregeArithmetic.Formula) : Applicative.Formula :=
  .existsPredicate 0 (.conjunction HumeInternal.naturalDefinition
    (.existsObject (.conjunction (Arithmetic.unary 0 (.var 0))
      (FormulaRenaming.objects (fun _ => 0)
        (FregeArithmeticInterpretation.translate 0 ψ)))))

/-- The Hume-route Z2 translation of `cor:frege-theorem` is `toFF` applied to
the FA source formula of the Z2 sentence. -/
theorem interpret_eq (p : SecondOrderArithmetic.Formula) :
    FregeArithmeticProofTransfer.interpret p =
      toFF (FregeArithmeticProofTransfer.sourceFormula p) := rfl

/-- Translation lemma for `toFF`: in every full TS model of FF, the translation
of a formula valid in all FA models holds under every assignment. The FA model
is the one carried by the number domain (`interpretedModel`), which satisfies
HP and full comprehension by `interpreted_full_conditions`. -/
theorem toFF_valid {D : Type u} {R : Nat → Type v} (M : Positive.Interpretation D R)
    (full : FullTSConditions M) (ψ : Part2.FregeArithmetic.Formula) (hψ : FAValid.{u, v} ψ)
    (o : ObjectAssignment D) (r : PredicateAssignment R) : (toFF ψ).truth M o r := by
  obtain ⟨N, domain⟩ := Arithmetic.full_ts_has_peano_domain M full
  let x : FregeArithmeticInterpretation.Number M N := ⟨Arithmetic.modelZero M, domain.zero_member⟩
  refine ⟨N, ?_, x.val, x.property, ?_⟩
  · exact (HumeInternal.natural_definition_truth M o (pushPredicate r 0 N)).mpr
      domain.represents_least
  · apply (FormulaRenaming.objects_truth M (FregeArithmeticInterpretation.translate 0 ψ)
      (fun _ => 0) (pushObject o x.val) (pushPredicate r 0 N)).mpr
    apply (FregeArithmeticInterpretation.translation_truth M full.full_comprehension domain
      ψ 0 (fun _ => x) r (pushPredicate r 0 N)
      (FregeArithmeticInterpretation.initial_context N r)).mpr
    exact hψ _ (FregeArithmeticInterpretation.interpreted_full_conditions M
      full.full_comprehension domain) (fun _ => x) r

/-- FA interprets in TF: the `toFF` translation of every FA-valid formula is
derivable from the printed axioms. Completeness over the equality models of
the Part II algebra theory reduces this to `toFF_valid`; the certified bridges
`full_functional_algebra_provability`, `original_proof_in_extension`,
`V3.Cleaner.provability_iff_fullFE` and `Printed.provability_iff` carry the
derivation to `Printed.theory`. -/
theorem ff_interprets_fa (ψ : Part2.FregeArithmetic.Formula) (h : FAValid.{0, 0} ψ) :
    Printed.theory ⊢ sentence (toFF ψ).functional := by
  have algebra : fullAlgebraTheory ⊢ sentence (toFF ψ).functional := by
    apply Theory.Proof.complete_on_eq_models.{0, 0}
    intro M _ _ _ hM
    have := Encoded.sorts_of_model hM
    let native := Guarded.extracted M
    have full : FullTSConditions native.applicative :=
      (algebra_axioms_iff_conditions native).mp
        ((Encoded.model_iff_valid (Guarded.extractedRealization M) AlgebraAxiom).mp hM)
    apply (Guarded.sentence_truth (Guarded.extractedRealization M)
      inferInstance (fun _ => inferInstance) (toFF ψ).functional).mpr
    intro objects functions predicates
    exact (shared_formula_preserves_truth native (toFF ψ) objects functions predicates).mpr
      (toFF_valid native.applicative full ψ h objects predicates)
  exact (Printed.provability_iff _).mpr
    ((V3.Cleaner.provability_iff_fullFE _).mpr
      (FunctionExtensionality.original_proof_in_extension _
        ((full_functional_algebra_provability (toFF ψ)).mpr algebra)))

/-! ### FF into FA: through Z2 -/

/-- The FA source formula of the Z2 translation of a TF formula: the
certified TF -> Z2 translation of `thm:three-way` followed by the FA formula
expressing a Z2 sentence on the Frege numbers. -/
noncomputable def toFA (p : Functional.Formula) : Part2.FregeArithmetic.Formula :=
  FregeArithmeticProofTransfer.sourceFormula (MutualInterpretability.fregeanTranslation p)

/-- TF interprets in FA: the `toFA` translation of every theorem of the
printed theory is valid in every Henkin model of FA, at every universe. -/
theorem fa_interprets_ff (p : Functional.Formula) (h : Printed.theory ⊢ sentence p) :
    FAValid.{u, v} (toFA p) := by
  intro D R M full o r
  exact FregeArithmeticProofTransfer.source_formula_valid M full _
    (V3.Certificate.cleaner_to_Z2 p ((Printed.provability_iff _).mp h)) o r

/-- The applicative variant of `toFA`, for the shared language of NECA + RC. -/
noncomputable def toFA' (p : Applicative.Formula) : Part2.FregeArithmetic.Formula :=
  FregeArithmeticProofTransfer.sourceFormula (Research.Z2Reverse.ReverseProofTransfer.translate p)

/-- NECA + RC interprets in FA. -/
theorem fa_interprets_algebra (p : Applicative.Formula)
    (h : V3.RelationalComprehension.theory ⊢ sentence p.functional) :
    FAValid.{u, v} (toFA' p) := by
  intro D R M full o r
  exact FregeArithmeticProofTransfer.source_formula_valid M full _
    (V3.Certificate.algebra_to_Z2 p h) o r

/-! ### The model-theoretic halves -/

/-- Every full TS model of FF carries a Henkin model of FA: its number domain
with the internal cardinality map satisfies HP and full comprehension. -/
theorem fa_model_of_ff_model {D : Type u} {R : Nat → Type v} (M : Positive.Interpretation D R)
    (full : FullTSConditions M) :
    ∃ (N : R 0) (domain : Arithmetic.PeanoDomain M N),
      Part2.FregeArithmetic.FullConditions
        (FregeArithmeticInterpretation.interpretedModel M full.full_comprehension domain) := by
  obtain ⟨N, domain⟩ := Arithmetic.full_ts_has_peano_domain M full
  exact ⟨N, domain,
    FregeArithmeticInterpretation.interpreted_full_conditions M full.full_comprehension domain⟩

section TaggedInstances
variable {D : Type u} {R : Nat → Type v} {M : Positive.Interpretation D R} {N : R 0}

/-- The tagged two-sorted carrier of a Z2 model (`ArithmeticEncoding.taggedModel`),
exposed as a Foundation structure for the encoded Z2 language so that the
internal term model of `thm:reverse` can be built on it. These are exactly the
instances packed into `ArithmeticEncoding.taggedModel`. -/
instance taggedModelNonempty (A : SecondOrderArithmetic.Operations M N) :
    Nonempty (ArithmeticEncoding.Tagged A) :=
  ⟨.number A.zero⟩

instance taggedModelStructure (A : SecondOrderArithmetic.Operations M N) :
    Structure ArithmeticEncoding.language (ArithmeticEncoding.Tagged A) :=
  ArithmeticEncoding.taggedStructure A

instance taggedModelEq (A : SecondOrderArithmetic.Operations M N) :
    Structure.Eq ArithmeticEncoding.language (ArithmeticEncoding.Tagged A) :=
  ArithmeticEncoding.tagged_equality A

end TaggedInstances

/-- Every Henkin model of FA yields a full TF model of FF: Frege's theorem
builds a Z2 model inside the FA model (`hume_constructs_Z2_model`), and the
internal term model of `thm:reverse` turns that Z2 model into a full TS model
whose copy expansion satisfies the full TF conditions (`extracted_fullTF`). -/
theorem ff_model_of_fa_model {D : Type u} {R : Nat → Type v}
    (M : Part2.FregeArithmetic.Interpretation D R) (full : Part2.FregeArithmetic.FullConditions M) :
    FullTFConditions (copyExpansion
      (Research.Z2Reverse.InternalSourceModel.extractedInterpretation
        (ArithmeticEncoding.Tagged
          (SecondOrderArithmetic.arithmeticOperations (FregeArithmeticZ2.arithmetic M full)))
        (FregeArithmeticZ2.hume_constructs_Z2_model M full))) :=
  Research.Z2Reverse.InternalSourceModel.extracted_fullTF _ _

/-- The same FF model, measured by the certificate's notion of an FF model:
every Henkin model of FA yields a model of the printed axioms A1–A6 (and so
of the encoded presentation). The copy expansion of the internal term model
satisfies full comprehension and FE (`copy_satisfies_full_FE`), and the
printed axioms have exactly those models (`V3.Cleaner.axioms_iff_fullFE`,
`Printed.axioms_iff_cleaner`). -/
theorem printed_model_of_fa_model {D : Type u} {R : Nat → Type v}
    (M : Part2.FregeArithmetic.Interpretation D R) (full : Part2.FregeArithmetic.FullConditions M) :
    ∀ p, Printed.Axiom p → Valid (copyExpansion
      (Research.Z2Reverse.InternalSourceModel.extractedInterpretation
        (ArithmeticEncoding.Tagged
          (SecondOrderArithmetic.arithmeticOperations (FregeArithmeticZ2.arithmetic M full)))
        (FregeArithmeticZ2.hume_constructs_Z2_model M full))) p := by
  let native := Research.Z2Reverse.InternalSourceModel.extractedInterpretation
    (ArithmeticEncoding.Tagged
      (SecondOrderArithmetic.arithmeticOperations (FregeArithmeticZ2.arithmetic M full)))
    (FregeArithmeticZ2.hume_constructs_Z2_model M full)
  have ts : FullTSConditions native :=
    Research.Z2Reverse.InternalSourceModel.extracted_fullTS _ _
  let : Nonempty _ := ⟨native.constantK⟩
  let := ts.full_comprehension.relations_nonempty
  exact (Printed.axioms_iff_cleaner _).mpr
    ((V3.Cleaner.axioms_iff_fullFE _).mpr
      (FunctionExtensionality.copy_satisfies_full_FE native ts))

end FregeanECA.V4.FregeArithmetic

#print axioms FregeanECA.V4.FregeArithmetic.ff_interprets_fa
#print axioms FregeanECA.V4.FregeArithmetic.fa_interprets_ff
#print axioms FregeanECA.V4.FregeArithmetic.fa_interprets_algebra
#print axioms FregeanECA.V4.FregeArithmetic.fa_model_of_ff_model
#print axioms FregeanECA.V4.FregeArithmetic.ff_model_of_fa_model
#print axioms FregeanECA.V4.FregeArithmetic.printed_model_of_fa_model
