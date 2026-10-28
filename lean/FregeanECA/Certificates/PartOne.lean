import FregeanECA.Theorems
import Lean.Util.CollectAxioms

/-! PART I: equivalence and consistency, without a consistency premise.
From `lean/`: lake env lean --trust=0 FregeanECA/Certificates/PartOne.lean
This independent entry file reuses pinned proofs; it is not dependency-free.
Definitions: Syntax.lean (language), Axioms.lean (literal schemes),
Guarded.lean (sorts and sentence encoding), Theorems.lean (proofs).
Read the complete statement of `checked` below: ⊢ is actual derivability.
-/
set_option warningAsError true

namespace FregeanECA.Certificates.PartOne
open FFL FFL.FirstOrder

/-- Equality, sort/typing axioms, and all universally closed proper axioms. -/
def theory (axioms : Functional.Formula → Prop) : Theory Guarded.language :=
  Theory.eqAxiom Guarded.language ∪ Guarded.sortTheory ∪
    {sentence | ∃ p, axioms p ∧ Guarded.sentence p = sentence}

/-- Positive relational comprehension, finite functional comprehension,
functional Basic Law V, coverage, and nontriviality; no function-identity FE. -/
abbrev TF := theory Axioms.FunctionalAxiom

/-- Nontrivial ECA plus the five positive relation-closure schemes. -/
abbrev TS := theory Axioms.SpecificationAxiom

noncomputable abbrev shared (p : Applicative.Formula) :=
  Guarded.sentence p.functional

/-- Every shared sentence has the same provability; neither theory proves
false. The consistency proof constructs a model and uses soundness. -/
theorem checked :
    (∀ p : Applicative.Formula, (TF ⊢ shared p) ↔ (TS ⊢ shared p)) ∧
    (TF ⊬ (⊥ : Sentence Guarded.language)) ∧
    (TS ⊬ (⊥ : Sentence Guarded.language)) :=
  ⟨Encoded.functional_specification_provability, Encoded.neither_theory_proves_false⟩

end FregeanECA.Certificates.PartOne

-- Reject any admission or extra axiom in the complete proof dependency chain.
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  for ax in ← collectAxioms ``FregeanECA.Certificates.PartOne.checked do
    unless allowed.contains ax do throwError "Part I certificate rejected: {ax}"
  logInfo "PART I CERTIFICATE PASS: standard Lean axioms only; require exit code 0."

#print axioms FregeanECA.Certificates.PartOne.checked
