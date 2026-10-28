import FregeanECA.LambdaInterpretation
import FregeanECA.Part2.Conservativity

/-! Actual proof-theoretic exactness for the fixed K/S translation of lambda
terms. Provability is Foundation's existing classical sequent calculus.
Soundness in the canonical model gives reflection; equality-model completeness
and the proved general interpretation give preservation. -/

namespace FregeanECA.Part2.ProgramEquations

open Frege Frege.OpenLambda FFL FFL.FirstOrder LambdaInterpretation

theorem canonical_eca : Pure.ECAConditions (pureAlgebra OpenLambda.algebra) :=
  ⟨OpenLambda.algebra.constant_returns_first_argument,
    OpenLambda.algebra.distribute_applies_the_same_argument,
    the_constructed_open_term_algebra_is_extensional,
    ⟨termClass (.coeff 0), termClass (.coeff 1),
      the_constructed_extensional_algebra_is_nontrivial⟩⟩

/-- The actual first-order ECA calculus proves exactly the translated
beta-eta equations, with all free names universally closed. -/
theorem bare_program_equation_iff (M N : OpenLambda.Term 0) :
    (Bare.theory ⊢ Bare.sentence (equation M N)) ↔ BetaEtaConvertible M N := by
  constructor
  · intro proof
    let : Nonempty Element := ⟨termClass (.coeff 0)⟩
    have truth := Theory.Proof.sound_small proof
      (Bare.model_valid (pureAlgebra OpenLambda.algebra) canonical_eca)
    have valid := (Bare.model_truth (pureAlgebra OpenLambda.algebra) (equation M N)).mp truth
    exact canonical_equation_reflects_conversion M N
      (valid (fun name => termClass (.coeff name)))
  · intro conversion
    apply Theory.Proof.complete_on_eq_models.{0, 0} (Bare.sentence (equation M N))
    intro D _ _ _ model
    have eca := (Bare.models_theory_iff D).mp model
    let A := Encoded.algebraOfPure eca
    apply (Bare.sentence_truth D (equation M N)).mpr
    intro assignment
    exact conversion_makes_equation_true A eca.extensional assignment conversion

/-- Part II's Fregean theory proves the fixed translated equation if and only
if the source terms are beta-eta convertible. This is a theory-level theorem,
not merely exactness in one chosen model. -/
theorem full_functional_program_equation_iff (M N : OpenLambda.Term 0) :
    (fullFunctionalTheory ⊢ Guarded.sentence (equation M N).functional) ↔
      BetaEtaConvertible M N :=
  (bare_eca_full_functional_provability (equation M N)).symm.trans
    (bare_program_equation_iff M N)

/-- The equivalent Part II relational-algebraic presentation has exactly the
same beta-eta equations under the same translation. -/
theorem full_algebra_program_equation_iff (M N : OpenLambda.Term 0) :
    (fullAlgebraTheory ⊢ Guarded.sentence (equation M N).functional) ↔
      BetaEtaConvertible M N :=
  (bare_eca_full_algebra_provability (equation M N)).symm.trans
    (bare_program_equation_iff M N)

theorem bare_pointwise_program_equation_iff (M N : OpenLambda.Term 0) :
    (Bare.theory ⊢ Bare.sentence (pointwiseEquation M N)) ↔ BetaEtaConvertible M N := by
  constructor
  · intro proof
    let : Nonempty Element := ⟨termClass (.coeff 0)⟩
    have truth := Theory.Proof.sound_small proof
      (Bare.model_valid (pureAlgebra OpenLambda.algebra) canonical_eca)
    have valid := (Bare.model_truth (pureAlgebra OpenLambda.algebra)
      (pointwiseEquation M N)).mp truth
    exact canonical_equation_reflects_conversion M N
      ((pointwise_iff_equation _ canonical_eca _ M N).mp
        (valid (fun name => termClass (.coeff name))))
  · intro conversion
    apply Theory.Proof.complete_on_eq_models.{0, 0} (Bare.sentence (pointwiseEquation M N))
    intro D _ _ _ model
    have eca := (Bare.models_theory_iff D).mp model
    let A := Encoded.algebraOfPure eca
    apply (Bare.sentence_truth D (pointwiseEquation M N)).mpr
    intro assignment
    apply (pointwise_iff_equation _ eca _ M N).mpr
    exact conversion_makes_equation_true A eca.extensional assignment conversion

/-- Actual provability of agreement on all object inputs is exact for beta-eta
conversion, with the newly bound input variable kept fresh by explicit shift. -/
theorem full_functional_pointwise_program_equation_iff (M N : OpenLambda.Term 0) :
    (fullFunctionalTheory ⊢ Guarded.sentence (pointwiseEquation M N).functional) ↔
      BetaEtaConvertible M N :=
  (bare_eca_full_functional_provability (pointwiseEquation M N)).symm.trans
    (bare_pointwise_program_equation_iff M N)

theorem full_algebra_pointwise_program_equation_iff (M N : OpenLambda.Term 0) :
    (fullAlgebraTheory ⊢ Guarded.sentence (pointwiseEquation M N).functional) ↔
      BetaEtaConvertible M N :=
  (bare_eca_full_algebra_provability (pointwiseEquation M N)).symm.trans
    (bare_pointwise_program_equation_iff M N)

end FregeanECA.Part2.ProgramEquations

#print axioms FregeanECA.Part2.ProgramEquations.bare_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.full_functional_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.full_algebra_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.full_functional_pointwise_program_equation_iff
#print axioms FregeanECA.Part2.ProgramEquations.full_algebra_pointwise_program_equation_iff
