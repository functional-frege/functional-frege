import FregeanECA.Research.Z2Reverse.InternalConversionCongruence
import FregeanECA.Pure

/-!
The concrete combinatory algebra of internally coded beta-eta classes.
K and S are unconditional checked laws. Extensionality and nontriviality
are exposed below as explicit remaining theorem inputs; this module does
not assert them without those inputs and introduces no axioms.
-/
namespace FregeanECA.Research.Z2Reverse.InternalQuotientAlgebra
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalLambdaCode InternalLambdaScope InternalTermQuotient
open InternalConversionCongruence
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

abbrev Object := (conversion (V := V)).Object

noncomputable def algebra : Frege.CombinatoryAlgebra (Object (V := V)) where
  apply := conversion.application
  constant := conversion.decode constantK
  distribute := conversion.decode constantS
  constant_returns_first_argument := quotient_K
  distribute_applies_the_same_argument := quotient_S

noncomputable def interpretation : Pure.Interpretation (Object (V := V)) where
  apply := algebra.apply
  constantK := algebra.constant
  constantS := algebra.distribute

/-- Precisely the code-level extensionality still needed by this packaging lemma. -/
def CodeExtensional : Prop := ∀ s t : V, IsScoped 0 s → IsScoped 0 t →
  (∀ u, IsScoped 0 u → conversion.relation (app s u) (app t u)) → conversion.relation s t

/-- A concrete separation obligation, rather than an assumed algebra carrier. -/
def FreeNamesSeparated : Prop :=
  ¬ conversion.relation (fvar (0 : V)) (fvar 1)

theorem extensional_of_codes (ext : CodeExtensional (V := V)) :
    (algebra (V := V)).IsExtensional := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro s t agree
  apply Quotient.sound
  apply ext s.val t.val s.property t.property
  intro u hu
  have same := agree (conversion.ofTerm ⟨u, hu⟩)
  exact Quotient.exact same

theorem nontrivial_of_free_names (separated : FreeNamesSeparated (V := V)) :
    ∃ x y : Object (V := V), x ≠ y := by
  refine ⟨conversion.decode (fvar 0), conversion.decode (fvar 1), ?_⟩
  intro same
  apply separated
  have rel := (conversion.decode_eq_iff (fvar 0) (fvar 1)).mp same
  simpa only [normalize_of_scoped (fvar (0 : V)) (isScoped_fvar 0 0),
    normalize_of_scoped (fvar (1 : V)) (isScoped_fvar 0 1)] using rel

/-- Conditional assembly only: both remaining hypotheses are displayed explicitly. -/
theorem eca_of_codes (ext : CodeExtensional (V := V))
    (separated : FreeNamesSeparated (V := V)) :
    Pure.ECAConditions (interpretation (V := V)) where
  constant := quotient_K
  distribute := quotient_S
  extensional := extensional_of_codes ext
  nontrivial := nontrivial_of_free_names separated

end FregeanECA.Research.Z2Reverse.InternalQuotientAlgebra
