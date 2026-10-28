import FregeanECA.Part2.Consequences
import FregeanECA.Part2.ProgramEquations
import Lean.Util.CollectAxioms

/-! PART II: equivalence, consistency, retained strength, exact computation.
From `lean/`: lake env lean --trust=0 FregeanECA/Certificates/PartTwo.lean
Actual schemes: Part2/Axioms.lean and Part2/AlgebraAxioms.lean.
Arithmetic through HP has its own focused certificate, HumeRoute.lean.
This entry file has no mathematical premises and imports no master certificate.
-/
set_option warningAsError true

namespace FregeanECA.Certificates.PartTwo
open FFL FFL.FirstOrder

def theory (axioms : Functional.Formula → Prop) : Theory Guarded.language :=
  Theory.eqAxiom Guarded.language ∪ Guarded.sortTheory ∪
    {sentence | ∃ p, axioms p ∧ Guarded.sentence p = sentence}

/-- Part I, for the precise preservation comparison. -/
abbrev TF := theory Axioms.FunctionalAxiom
abbrev TS := theory Axioms.SpecificationAxiom

/-- Full classical relational comprehension; computational A2 is unchanged. -/
abbrev TFfull := theory Part2.FullFunctionalAxiom
/-- Nontrivial ECA and positive closure, complement, predicate projection. -/
abbrev TSfull := theory Part2.AlgebraAxiom

noncomputable abbrev shared (p : Applicative.Formula) :=
  Guarded.sentence p.functional

theorem equivalence_and_consistency :
    (∀ p : Applicative.Formula, (TFfull ⊢ shared p) ↔ (TSfull ⊢ shared p)) ∧
    (TFfull ⊬ (⊥ : Sentence Guarded.language)) ∧
    (TSfull ⊬ (⊥ : Sentence Guarded.language)) :=
  ⟨Part2.full_functional_algebra_provability,
    Part2.full_neither_theory_proves_false.2, Part2.full_neither_theory_proves_false.1⟩

theorem retains_part_one :
    (∀ p : Sentence Guarded.language, (TF ⊢ p) → (TFfull ⊢ p)) ∧
    (∀ p : Sentence Guarded.language, (TS ⊢ p) → (TSfull ⊢ p)) :=
  ⟨Part2.preserves_part_one_functional, Part2.preserves_part_one_algebraic⟩

/-- Actual provable program equations coincide with ordinary beta-eta
conversion under the fixed K/S translation; open source terms are included. -/
theorem program_equations : ∀ M N : Frege.OpenLambda.Term 0,
    ((TFfull ⊢ Guarded.sentence (LambdaInterpretation.equation M N).functional) ↔
      Frege.OpenLambda.BetaEtaConvertible M N) ∧
    ((TSfull ⊢ Guarded.sentence (LambdaInterpretation.equation M N).functional) ↔
      Frege.OpenLambda.BetaEtaConvertible M N) :=
  fun M N => ⟨Part2.ProgramEquations.full_functional_program_equation_iff M N,
    Part2.ProgramEquations.full_algebra_program_equation_iff M N⟩

theorem checked : (type_of% equivalence_and_consistency) ∧
    (type_of% retains_part_one) ∧ (type_of% program_equations) :=
  ⟨equivalence_and_consistency, retains_part_one, program_equations⟩

end FregeanECA.Certificates.PartTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for ax in ← collectAxioms ``FregeanECA.Certificates.PartTwo.checked do
    unless allowed.contains ax do throwError "Part II certificate rejected: {ax}"
  logInfo "PART II CERTIFICATE PASS: standard Lean axioms only; require exit code 0."

#print axioms FregeanECA.Certificates.PartTwo.checked
