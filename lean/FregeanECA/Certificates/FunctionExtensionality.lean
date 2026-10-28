import FregeanECA.Part2.FunctionExtensionality
import Lean.Util.CollectAxioms

/-!
Separate certificate for adding function-identity extensionality (FE).
FE is part of the extended OBJECT THEORY, not an extra Lean axiom.
The original manuscript theory remains unchanged. The checked translations
show mutual interpretability with its FE extension and conservativity over
the pure applicative language. No reverse interpretation in Z2 is asserted.

From lean/: lake env lean --trust=0 FregeanECA/Certificates/FunctionExtensionality.lean
-/

set_option warningAsError true

namespace FregeanECA.Certificates.FunctionExtensionality

theorem checked :
    (type_of% Part2.FunctionExtensionality.mutual_proof_interpretations) ∧
    (∀ p, type_of% (Part2.FunctionExtensionality.shared_v2_provability p)) ∧
    (∀ p, type_of% (Part2.FunctionExtensionality.pure_conservativity p)) ∧
    (type_of% Part2.FunctionExtensionality.consistent) :=
  ⟨Part2.FunctionExtensionality.mutual_proof_interpretations,
    Part2.FunctionExtensionality.shared_v2_provability,
    Part2.FunctionExtensionality.pure_conservativity,
    Part2.FunctionExtensionality.consistent⟩

end FregeanECA.Certificates.FunctionExtensionality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for ax in ← collectAxioms ``FregeanECA.Certificates.FunctionExtensionality.checked do
    unless allowed.contains ax do
      throwError "FUNCTION EXTENSIONALITY CERTIFICATE REJECTED: {ax}"
  logInfo "FUNCTION EXTENSIONALITY CERTIFICATE PASS: proof interpretations, pure-language conservativity, consistency; standard Lean axioms only."

#print axioms FregeanECA.Certificates.FunctionExtensionality.checked
