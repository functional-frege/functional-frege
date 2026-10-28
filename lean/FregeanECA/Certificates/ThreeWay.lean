import FregeanECA.Part2.MutualInterpretability
import Lean.Util.CollectAxioms

/-!
Focused certificate for three-way mutual interpretability and equiconsistency.
The actual theories are full TF, active V2 ECAneq + FCAlgebra, and encoded Z2.
The proof dependencies include the internally coded model in arbitrary Z2
models, fixed syntax translations, and actual Foundation proof transfer.

Run from lean/: lake env lean --trust=0 FregeanECA/Certificates/ThreeWay.lean
Require exit zero. The whitelist below rejects admissions and additional
mathematical axioms anywhere in the audited dependency chains. This entry
file uses the included pinned proofs; it is not dependency-free.
-/
set_option warningAsError true

namespace FregeanECA.Certificates.ThreeWay

theorem checked :
    (type_of% Part2.MutualInterpretability.three_way) ∧
    (type_of% Part2.MutualInterpretability.equiconsistency) ∧
    (∀ p, type_of% (Part2.MutualInterpretability.FE_to_Z2 p)) ∧
    (∀ p, type_of% (Part2.MutualInterpretability.Z2_to_FE p)) :=
  ⟨Part2.MutualInterpretability.three_way,
    Part2.MutualInterpretability.equiconsistency,
    Part2.MutualInterpretability.FE_to_Z2,
    Part2.MutualInterpretability.Z2_to_FE⟩

end FregeanECA.Certificates.ThreeWay

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``FregeanECA.Certificates.ThreeWay.checked,
    ``FregeanECA.Research.Z2Reverse.InternalSourceModel.extracted_fullTS,
    ``FregeanECA.Research.Z2Reverse.ReverseProofTransfer.source_semantics,
    ``FregeanECA.Research.Z2Reverse.ReverseProofTransfer.translation_preserves_falsum,
    ``FregeanECA.Part2.ArithmeticInterpretation.interpretation_preserves_falsum]
  for endpoint in endpoints do
    for ax in ← collectAxioms endpoint do
      unless allowed.contains ax do
        throwError "THREE-WAY CERTIFICATE REJECTED at {endpoint}: {ax}"
  logInfo "THREE-WAY CERTIFICATE PASS: all six proof-transfer directions, equiconsistency, and optional FE extension; standard Lean axioms only."

#print axioms FregeanECA.Certificates.ThreeWay.checked
#print axioms FregeanECA.Research.Z2Reverse.ReverseProofTransfer.source_semantics
#print axioms FregeanECA.Research.Z2Reverse.ReverseProofTransfer.translation_preserves_falsum
#print axioms FregeanECA.Part2.ArithmeticInterpretation.interpretation_preserves_falsum
