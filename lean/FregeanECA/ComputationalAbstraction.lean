import FregeanECA.Model

/-!
# Functional abstraction and exact beta-eta equality

Basic Law V concerns equality of value-range objects, not identity
in the function sort. In the canonical open lambda-term model its equivalence
relation is exactly ordinary beta-eta conversion, and this is equivalent to
agreement on every input of that model.

`OpenLambda.Term 0` permits free names; zero means no unbound de Bruijn indices.
The quantifiers below therefore include open inputs. The converse uses the
already proved extensionality of this open term algebra, whose proof chooses
a fresh free name. No claim about observational equivalence, termination,
closed-input-only equivalence, or equality in every individual ECA is made.
-/

namespace FregeanECA.ComputationalAbstraction

open Frege OpenLambda
universe u v

/-- Basic Law V: represented maps have the same value-range object
exactly when they agree at every argument. This is A3 itself, made explicit. -/
theorem range_equality_iff_same_values {D : Type u} {F : Type v}
    (R : Representation D F) (f g : F) :
    R.delta f = R.delta g ↔ ∀ x : D, R.eval f x = R.eval g x :=
  R.lawV f g

/-- The abstraction map into the canonical model identifies precisely the
ordinary beta-eta-convertible open terms. -/
theorem canonical_abstraction_exact (M N : Term 0) :
    termClass M = termClass N ↔ BetaEtaConvertible M N :=
  quotient_classes_are_equal_exactly_when_beta_eta_convertible M N

/-- Beta-eta conversion is exactly agreement on all inputs in the canonical
open term algebra. Outputs here are elements of that same quotient algebra. -/
theorem beta_eta_iff_same_values (M N : Term 0) :
    BetaEtaConvertible M N ↔
      ∀ p : Element, OpenLambda.apply (termClass M) p = OpenLambda.apply (termClass N) p := by
  constructor
  · intro conversion p
    exact congrArg (fun code => OpenLambda.apply code p)
      ((canonical_abstraction_exact M N).mpr conversion)
  · intro same
    apply (canonical_abstraction_exact M N).mp
    exact the_constructed_open_term_algebra_is_extensional _ _ same

/-- The same result stated entirely in lambda syntax. All open input terms
are included, and output equivalence means beta-eta conversion. -/
theorem beta_eta_iff_same_values_on_terms (M N : Term 0) :
    BetaEtaConvertible M N ↔
      ∀ P : Term 0, BetaEtaConvertible (.app M P) (.app N P) := by
  constructor
  · intro conversion P
    exact conversion.appLeft P
  · intro same
    apply (beta_eta_iff_same_values M N).mpr
    intro p
    refine Quotient.inductionOn p ?_
    intro P
    exact (canonical_abstraction_exact (.app M P) (.app N P)).mpr (same P)

/-- In the already constructed Fregean model, the value-range abstraction of
these represented functions agrees exactly with their beta-eta conversion. -/
theorem canonical_fregean_ranges_exact (M N : Term 0) :
    openTermModel.representation.delta (termClass M) =
      openTermModel.representation.delta (termClass N) ↔ BetaEtaConvertible M N :=
  canonical_abstraction_exact M N

end FregeanECA.ComputationalAbstraction

#print axioms FregeanECA.ComputationalAbstraction.range_equality_iff_same_values
#print axioms FregeanECA.ComputationalAbstraction.canonical_abstraction_exact
#print axioms FregeanECA.ComputationalAbstraction.beta_eta_iff_same_values
#print axioms FregeanECA.ComputationalAbstraction.beta_eta_iff_same_values_on_terms
#print axioms FregeanECA.ComputationalAbstraction.canonical_fregean_ranges_exact
