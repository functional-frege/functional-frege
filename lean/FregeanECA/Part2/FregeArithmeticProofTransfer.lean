import FregeanECA.Part2.FregeArithmeticData
import FregeanECA.Part2.FregeArithmeticTranslation
import FregeanECA.Part2.FregeArithmeticZ2
import FregeanECA.Part2.ArithmeticModelInterpretation
import FregeanECA.Part2.ArithmeticClosure
import FregeanECA.Part2.FormulaRenaming

/-! A fixed formula translation and actual Foundation proof transfer through
the standard Frege route. The construction is Part II -> interpreted HP ->
Frege numbers -> Z2. The earlier direct Part II -> Z2 proof is not used.

Free arithmetic number parameters are universally closed before translation;
free relation parameters are retained and universally closed by the final
sentence encoding. Every auxiliary domain and graph is explicitly constrained
by a formula. No model-dependent choice appears in the syntactic translation. -/

namespace FregeanECA.Part2.FregeArithmeticProofTransfer
open Positive Arithmetic
open FFL FFL.FirstOrder
open scoped FFL.FirstOrder
universe u v
variable {D : Type u} {R : Nat → Type v}

/-- All arithmetic number parameters have been closed, so the remaining
default assignment may use the explicitly bound Frege zero (slot 1). -/
def slots : FregeArithmeticDefinable.Slots :=
  { FregeArithmeticDefinable.initialSlots with objects := fun _ => 1 }

/-- Existential order: Frege number predicate, application graph, zero, tag.
The tag is the Frege successor of zero, not an arbitrary computational object. -/
def sourceFormula (p : SecondOrderArithmetic.Formula) : FregeArithmetic.Formula :=
  .existsPredicate 0 (.existsPredicate 2 (.existsObject (.existsObject
    (.conjunction FregeArithmeticData.dataFormula
      (FregeArithmeticDefinable.translate slots
        (ArithmeticInterpretation.interpret (SecondOrderArithmetic.closeAllNumbers p)))))))

theorem source_formula_valid (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p)
    (o : ObjectAssignment D) (r : PredicateAssignment R) :
    (sourceFormula p).truth M o r := by
  let N := FregeArithmeticRecursion.naturalPredicate M full
  let z := FregeArithmeticRecursion.zero M full
  let k := FregeArithmeticRecursion.successor M full z
  let native := FregeArithmeticRecursion.model M full
  obtain ⟨G, data, graph⟩ := FregeArithmeticData.canonical_data_exists M full
  let t := pushObject (pushObject o z.val) k.val
  let q := pushPredicate (pushPredicate r 0 N) 2 G
  refine ⟨N, G, z.val, k.val, ?_, ?_⟩
  · apply (FregeArithmeticData.data_formula_truth M t q).mpr
    simpa [t, q, pushObject, pushPredicate, N, z, k] using data
  · have ctx : FregeArithmeticDefinable.Context M N k z G slots
        (fun _ => z) t r q := by
      constructor
      · intro i; rfl
      · rfl
      · rfl
      · simp [slots, FregeArithmeticDefinable.initialSlots, q, pushPredicate]
      · simp [slots, FregeArithmeticDefinable.initialSlots, q, pushPredicate]
      · exact (FregeArithmeticDefinable.initial_context M N k z G (fun _ => z) r).predicates
    apply (FregeArithmeticDefinable.translation_truth M N native.apply k z G graph
      (ArithmeticInterpretation.interpret (SecondOrderArithmetic.closeAllNumbers p))
      slots (fun _ => z) t r q ctx).mpr
    change (ArithmeticInterpretation.interpret (SecondOrderArithmetic.closeAllNumbers p)).truth
      native (fun _ => z) r
    have comp := FregeArithmeticRecursion.model_has_full_comprehension M full
    exact ArithmeticModelInterpretation.interpreted_valid native comp
      (FregeArithmeticZ2.arithmetic M full).domain (SecondOrderArithmetic.closeAllNumbers p)
      (fun arithmetic => SecondOrderArithmetic.closeAllNumbers_valid _ p
        (ArithmeticEncoding.arithmetic_proof_truth arithmetic comp p proof)) (fun _ => z) r

/-- The base number domain is defined by its least-inductive formula. The
guarded default object only supplies a value to unused free object slots.
Capture-avoiding renaming preserves all bound variables and witnesses. -/
def interpret (p : SecondOrderArithmetic.Formula) : Applicative.Formula :=
  .existsPredicate 0 (.conjunction HumeInternal.naturalDefinition
    (.existsObject (.conjunction (unary 0 (.var 0))
      (FormulaRenaming.objects (fun _ => 0)
        (FregeArithmeticInterpretation.translate 0 (sourceFormula p))))))

theorem interpreted_valid (M : Positive.Interpretation D R)
    (full : FullTSConditions M) (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p)
    (o : ObjectAssignment D) (r : PredicateAssignment R) :
    (interpret p).truth M o r := by
  obtain ⟨N, domain⟩ := full_ts_has_peano_domain M full
  let x : FregeArithmeticInterpretation.Number M N := ⟨modelZero M, domain.zero_member⟩
  refine ⟨N, ?_, x.val, x.property, ?_⟩
  · exact (HumeInternal.natural_definition_truth M o (pushPredicate r 0 N)).mpr
      domain.represents_least
  · apply (FormulaRenaming.objects_truth M
      (FregeArithmeticInterpretation.translate 0 (sourceFormula p))
      (fun _ => 0) (pushObject o x.val) (pushPredicate r 0 N)).mpr
    apply (FregeArithmeticInterpretation.translation_truth M full.full_comprehension domain
      (sourceFormula p) 0 (fun _ => x) r (pushPredicate r 0 N)
      (FregeArithmeticInterpretation.initial_context N r)).mpr
    exact source_formula_valid _
      (FregeArithmeticInterpretation.interpreted_full_conditions M full.full_comprehension domain)
      p proof (fun _ => x) r

/-- Every actual Foundation Z2 proof transfers through HP to the relational
Part II theory. The conclusion is an actual target derivation, not a model
existence statement or a conditional arithmetic-validity assumption. -/
theorem via_hume_Z2_proof_transfer (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    fullAlgebraTheory ⊢ Guarded.sentence (interpret p).functional := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ hM
  have := Encoded.sorts_of_model hM
  let native := Guarded.extracted M
  have full : FullTSConditions native.applicative :=
    (algebra_axioms_iff_conditions native).mp
      ((Encoded.model_iff_valid (Guarded.extractedRealization M) AlgebraAxiom).mp hM)
  apply (Guarded.sentence_truth (Guarded.extractedRealization M)
    inferInstance (fun _ => inferInstance) (interpret p).functional).mpr
  intro objects functions predicates
  exact (shared_formula_preserves_truth native (interpret p) objects functions predicates).mpr
    (interpreted_valid native.applicative full p proof objects predicates)

/-- The identical translated sentence is derivable in the Fregean Part II
theory, by the already proved shared-language equivalence. -/
theorem via_hume_Z2_proof_transfer_fregean (p : SecondOrderArithmetic.Formula)
    (proof : ArithmeticEncoding.theory ⊢ ArithmeticEncoding.sentence p) :
    fullFunctionalTheory ⊢ Guarded.sentence (interpret p).functional :=
  (full_functional_algebra_provability (interpret p)).mpr
    (via_hume_Z2_proof_transfer p proof)

/-- A syntactic non-vacuity check: the fixed translation of contradiction is
false in every target interpretation, even without any target axioms. -/
theorem interpretation_preserves_falsum (M : Positive.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) :
    ¬ (interpret .falsum).truth M o r := by
  simp [interpret, sourceFormula, SecondOrderArithmetic.closeAllNumbers,
    SecondOrderArithmetic.closeNumbers, SecondOrderArithmetic.Formula.numberBound,
    ArithmeticInterpretation.interpret, SecondOrderArithmetic.guardedTranslation,
    SecondOrderArithmetic.numberGuards, SecondOrderArithmetic.Formula.translate,
    FregeArithmeticDefinable.translate, FregeArithmeticInterpretation.translate,
    FormulaRenaming.objects, Applicative.Formula.truth]

end FregeanECA.Part2.FregeArithmeticProofTransfer

#print axioms FregeanECA.Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer
#print axioms FregeanECA.Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer_fregean
