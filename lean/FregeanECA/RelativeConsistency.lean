import FregeanECA.Theorems
import Foundation.FirstOrder.SetTheory.Basic.Axioms

namespace FregeanECA.Encoded
open FFL

/-- The external implication once displayed with the consistency result
(`thm:consistency`), using Foundation's
actual ZFC axiom set and its actual proof predicate. Lean has already proved
the stronger conclusion by an explicit model and first-order soundness;
therefore this premise is unnecessary. This is not an internal ZFC proof
or a formalisation of the construction inside an arbitrary ZFC model. -/
theorem relative_consistency :
    Entailment.Consistent FirstOrder.SetTheory.ZermeloFraenkelChoice →
      Entailment.Consistent functionalTheory ∧ Entailment.Consistent specificationTheory :=
  fun _ => both_theories_consistent

end FregeanECA.Encoded
