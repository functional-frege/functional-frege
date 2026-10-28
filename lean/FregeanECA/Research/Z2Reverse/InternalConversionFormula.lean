import FregeanECA.Research.Z2Reverse.InternalConversionCongruence
import FregeanECA.Research.Z2Reverse.InternalAtomicDefinitions

/-!
One fixed parameter-free arithmetic formula for internally finite beta-eta
conversion. Its witnesses are model-valued coded vectors and certificates;
the construction does not select a defining formula from a particular model.
-/

namespace FregeanECA.Research.Z2Reverse.InternalConversionFormula

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalPaths InternalParallelBeta InternalEtaReduction
open InternalConversionCongruence ArithmeticModel
open scoped FFL.FirstOrder

/-- Fixed syntax for one edge of the symmetric beta-eta reduction graph. -/
noncomputable def edgeFormula : 𝚺₁.Semisentence 2 := .mkSigma
  “s t. (!parallelFormula 0 s t ∨ !stepFormula 0 s t) ∨
    (!parallelFormula 0 t s ∨ !stepFormula 0 t s)”

/-- A coded path has a model-valued length, with all adjacent vertices checked. -/
noncomputable def certificateFormula : 𝚺₁.Semisentence 3 := .mkSigma
  “c s t. ∃ n, !lenDef (n + 1) c ∧ !nthDef s c 0 ∧ !nthDef t c n ∧
    ∀ i < n, ∃ a b, !nthDef a c i ∧ !nthDef b c (i + 1) ∧ !edgeFormula a b”

noncomputable def conversionFormula : 𝚺₁.Semisentence 2 := .mkSigma
  “s t. ∃ c, !certificateFormula c s t”

section Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

instance edge_defined : 𝚺₁-Relation
    (fun s t : V => (Parallel 0 s t ∨ Step 0 s t) ∨ (Parallel 0 t s ∨ Step 0 t s))
      via edgeFormula := .mk fun v => by simp [edgeFormula]

instance certificate_defined : 𝚺₁-Relation₃
    (InternalPaths.Certificate (fun s t : V =>
      (Parallel 0 s t ∨ Step 0 s t) ∨ (Parallel 0 t s ∨ Step 0 t s)))
      via certificateFormula := .mk fun v => by
  simp [certificateFormula, InternalPaths.Certificate, eq_comm]

instance conversion_defined : 𝚺₁-Relation (conversion.relation : V → V → Prop)
    via conversionFormula := .mk fun v => by
  simp [conversionFormula, conversion, Convert, Reach]

theorem conversion_truth (s t : V) :
    conversionFormula.val.Eval ![s, t] Empty.elim ↔ conversion.relation s t := by
  simp

end Arithmetic

section Native

universe u v
variable {N : Type u} {S : Type v} (A : ArithmeticStructure N S)
  (model : ModelsZ2 A) (witnessSets : Nat → S)

/-- The concrete conversion object on the number carrier of any native Z2 model. -/
noncomputable def nativeConversion : InternalAtomicDefinitions.SourceConversion A model witnessSets := by
  letI := ArithmeticLanguage.oRingStructure A
  letI : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := ArithmeticLanguage.models_pa A model witnessSets
  exact conversion

theorem native_truth (s t : N) :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ArithmeticLanguage.models_iSigmaOne A model witnessSets
    conversionFormula.val.Eval (s := ArithmeticLanguage.oRingModel A) ![s, t] Empty.elim ↔
      (nativeConversion A model witnessSets).relation s t := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* 𝗣𝗔 := ArithmeticLanguage.models_pa A model witnessSets
  exact conversion_truth s t

/-- All finite atomic formulas are now supplied by fixed arithmetic syntax. -/
noncomputable def definitions :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ArithmeticLanguage.models_iSigmaOne A model witnessSets
    ArithmeticCodeAtoms.Definitions A (nativeConversion A model witnessSets).presentation
      (nativeConversion A model witnessSets).codeOperations := by
  letI := ArithmeticLanguage.oRingStructure A
  letI : N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  exact InternalAtomicDefinitions.definitions A model witnessSets
    (nativeConversion A model witnessSets) conversionFormula.val (native_truth A model witnessSets)

end Native

end FregeanECA.Research.Z2Reverse.InternalConversionFormula
