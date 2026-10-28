import FregeanECA.Part2.FregeArithmeticProofTransfer
import Lean.Util.CollectAxioms

/-! HUME ROUTE: actual internal HP and Z2 derivations in both Part II theories.
From `lean/`: lake env lean --trust=0 FregeanECA/Certificates/HumeRoute.lean
HP concerns available concepts ON THE INTERPRETED NUMBER DOMAIN; this does
not assert HP for all native objects. HumeInternal.lean defines its sentence.
FregeArithmeticProofTransfer.lean defines the fixed composed translation.
No consistency, arithmetic-validity, or model-existence premise is assumed.
-/
set_option warningAsError true

namespace FregeanECA.Certificates.HumeRoute
open FFL FFL.FirstOrder
universe u v

def theory (axioms : Functional.Formula → Prop) : Theory Guarded.language :=
  Theory.eqAxiom Guarded.language ∪ Guarded.sortTheory ∪
    {sentence | ∃ p, axioms p ∧ Guarded.sentence p = sentence}

abbrev TFfull := theory Part2.FullFunctionalAxiom
abbrev TSfull := theory Part2.AlgebraAxiom
abbrev Z2 := Part2.ArithmeticEncoding.theory
noncomputable abbrev arithmeticSentence := Part2.ArithmeticEncoding.sentence
noncomputable abbrev shared (p : Applicative.Formula) := Guarded.sentence p.functional
noncomputable abbrev translated (p : Part2.SecondOrderArithmetic.Formula) :=
  shared (Part2.FregeArithmeticProofTransfer.interpret p)

/-- A number domain exists, every available concept on it has a unique
defined abstract, and abstracts agree exactly for equinumerous concepts. -/
theorem internal_hume :
    (TFfull ⊢ shared Part2.HumeInternal.internalHumeSentence) ∧
    (TSfull ⊢ shared Part2.HumeInternal.internalHumeSentence) :=
  ⟨Part2.HumeInternal.internal_hume_provable_fregean,
    Part2.HumeInternal.internal_hume_provable⟩

/-- Transfer through interpreted HP and the generic Frege theorem.
Free number parameters are universally closed before the fixed translation. -/
theorem arithmetic_transfer : ∀ p : Part2.SecondOrderArithmetic.Formula,
    (Z2 ⊢ arithmeticSentence p) → (TFfull ⊢ translated p) ∧ (TSfull ⊢ translated p) :=
  fun p proof => ⟨Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer_fregean p proof,
    Part2.FregeArithmeticProofTransfer.via_hume_Z2_proof_transfer p proof⟩

/-- The translation cannot turn contradiction into a valid target formula. -/
theorem false_stays_false {D : Type u} {R : Nat → Type v}
    (M : Positive.Interpretation D R) (o : Positive.ObjectAssignment D)
    (r : Positive.PredicateAssignment R) :
    ¬ (Part2.FregeArithmeticProofTransfer.interpret .falsum).truth M o r :=
  Part2.FregeArithmeticProofTransfer.interpretation_preserves_falsum M o r

theorem checked : (type_of% internal_hume) ∧ (type_of% arithmetic_transfer) ∧
    (∀ {D : Type u} {R : Nat → Type v} (M : Positive.Interpretation D R)
      (o : Positive.ObjectAssignment D) (r : Positive.PredicateAssignment R),
        type_of% (false_stays_false M o r)) :=
  ⟨internal_hume, arithmetic_transfer, @false_stays_false⟩

end FregeanECA.Certificates.HumeRoute

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for ax in ← collectAxioms ``FregeanECA.Certificates.HumeRoute.checked do
    unless allowed.contains ax do throwError "Hume-route certificate rejected: {ax}"
  logInfo "HUME-ROUTE CERTIFICATE PASS: standard Lean axioms only; require exit code 0."

#print axioms FregeanECA.Certificates.HumeRoute.checked
