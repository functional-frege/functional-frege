import FregeanECA.Research.Z2Reverse.NativeAtomTranslation
import FregeanECA.Research.Z2Reverse.InternalTermQuotient

/-!
The finite atomic arithmetic interface of the internal term quotient.
All formula builders are fixed syntax. The only remaining definability input
is an explicitly supplied parameter-free formula for the conversion relation.
-/

namespace FregeanECA.Research.Z2Reverse.InternalAtomicDefinitions

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalTermQuotient ArithmeticModel
open scoped FFL.FirstOrder

def constantKFormula : 𝚺₁.Semisentence 1 := .mkSigma
  “y. ∃ b c, !qqBvarDef b 1 ∧ !lamFormula c b ∧ !lamFormula y c”

def constantSFormula : 𝚺₁.Semisentence 1 := .mkSigma
  “y. ∃ b0 b1 b2 p q r s t,
    !qqBvarDef b0 0 ∧ !qqBvarDef b1 1 ∧ !qqBvarDef b2 2 ∧
    !appFormula p b2 b0 ∧ !appFormula q b1 b0 ∧ !appFormula r p q ∧
    !lamFormula s r ∧ !lamFormula t s ∧ !lamFormula y t”

noncomputable def normalizedConversionFormula (conversion : Semisentence ℒₒᵣ 2) :
    Semisentence ℒₒᵣ 2 :=
  “s t. ∃ a b, !normalizeFormula.val a s ∧ !normalizeFormula.val b t ∧ !conversion a b”

abbrev NTerm := Part2.SecondOrderArithmetic.Term
abbrev NFormula := Part2.SecondOrderArithmetic.Formula

noncomputable def equalFormula (conversion : Semisentence ℒₒᵣ 2) (a b : NTerm) : NFormula :=
  NativeAtomTranslation.instantiate (normalizedConversionFormula conversion) ![a, b]

def kFormula (output : NTerm) : NFormula :=
  NativeAtomTranslation.instantiate constantKFormula.val ![output]

def sFormula (output : NTerm) : NFormula :=
  NativeAtomTranslation.instantiate constantSFormula.val ![output]

noncomputable def applicationFormula (a b output : NTerm) : NFormula :=
  NativeAtomTranslation.instantiate applyCodeFormula.val ![output, a, b]

section ArithmeticGraphs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

instance constantK_defined :
    𝚺₁-Predicate (fun x : V => x = constantK) via constantKFormula :=
  .mk fun v => by simp [constantKFormula, constantK, bvar]

instance constantS_defined :
    𝚺₁-Predicate (fun x : V => x = constantS) via constantSFormula :=
  .mk fun v => by simp [constantSFormula, constantS, bvar]

theorem normalizedConversionFormula_truth (conversion : Semisentence ℒₒᵣ 2) (s t : V) :
    (normalizedConversionFormula conversion).Eval ![s, t] Empty.elim ↔
      conversion.Eval ![normalize s, normalize t] Empty.elim := by
  simp [normalizedConversionFormula]

end ArithmeticGraphs

section Native

universe u v
variable {N : Type u} {S : Type v} (A : ArithmeticStructure N S)
  (model : ModelsZ2 A) (witnessSets : Nat → S)

abbrev SourceConversion :=
  @Conversion N (ArithmeticLanguage.oRingStructure A)
    (ArithmeticLanguage.models_iSigmaOne A model witnessSets)

variable (c : SourceConversion A model witnessSets) (conversion : Semisentence ℒₒᵣ 2)
  (conversion_truth :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
    ∀ a b : N,
    conversion.Eval (s := ArithmeticLanguage.oRingModel A) ![a, b] Empty.elim ↔ c.relation a b)

include conversion_truth in
theorem equalFormula_truth (a b : NTerm) (numbers : Nat → N) (sets : Nat → S) :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
    truth A numbers sets (equalFormula conversion a b) ↔
      c.decode (termValue A numbers a) = c.decode (termValue A numbers b) := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  rw [equalFormula, NativeAtomTranslation.instantiate_truth, c.decode_eq_iff]
  change (normalizedConversionFormula conversion).Eval
      ((termValue A numbers) ∘ ![a, b]) Empty.elim ↔ _
  rw [Matrix.comp₂, normalizedConversionFormula_truth]
  exact conversion_truth _ _

theorem kFormula_truth (output : NTerm) (numbers : Nat → N) (sets : Nat → S) :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
    truth A numbers sets (kFormula output) ↔ termValue A numbers output = (constantK : N) := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  rw [kFormula, NativeAtomTranslation.instantiate_truth]
  change constantKFormula.val.Eval ((termValue A numbers) ∘ ![output]) Empty.elim ↔ _
  rw [Matrix.comp₁]
  simp

theorem sFormula_truth (output : NTerm) (numbers : Nat → N) (sets : Nat → S) :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
    truth A numbers sets (sFormula output) ↔ termValue A numbers output = (constantS : N) := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  rw [sFormula, NativeAtomTranslation.instantiate_truth]
  change constantSFormula.val.Eval ((termValue A numbers) ∘ ![output]) Empty.elim ↔ _
  rw [Matrix.comp₁]
  simp

theorem applicationFormula_truth (a b output : NTerm) (numbers : Nat → N) (sets : Nat → S) :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
    truth A numbers sets (applicationFormula a b output) ↔
      termValue A numbers output = applyCode (termValue A numbers a) (termValue A numbers b) := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  rw [applicationFormula, NativeAtomTranslation.instantiate_truth]
  change applyCodeFormula.val.Eval ((termValue A numbers) ∘ ![output, a, b]) Empty.elim ↔ _
  rw [Matrix.comp₃]
  simp

/-- A fixed conversion formula supplies the last atomic definability datum. -/
noncomputable def definitions :
    letI := ArithmeticLanguage.oRingStructure A
    letI : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
    ArithmeticCodeAtoms.Definitions A c.presentation c.codeOperations := by
  let := ArithmeticLanguage.oRingStructure A
  let : N↓[ℒₒᵣ] ⊧* Arithmetic.ISigma 1 := ArithmeticLanguage.models_iSigmaOne A model witnessSets
  exact {
    pair := fun x y => ⟪x, y⟫
    pair_injective := fun a b d e h =>
      ⟨by simpa using congrArg Arithmetic.pi₁ h, by simpa using congrArg Arithmetic.pi₂ h⟩
    tuple_law := fun _ _ => rfl
    equalFormula := equalFormula conversion
    kFormula := kFormula
    sFormula := sFormula
    appFormula := applicationFormula
    pairFormula := NativeAtomTranslation.pairFormula
    equal_truth := equalFormula_truth A model witnessSets c conversion conversion_truth
    k_truth := kFormula_truth A model witnessSets
    s_truth := sFormula_truth A model witnessSets
    app_truth := applicationFormula_truth A model witnessSets
    pair_truth := by
      intro a b output numbers sets
      rw [NativeAtomTranslation.pairFormula_truth A model,
        NativeAtomTranslation.pair_eq_arithmetic A model sets] }

end Native

end FregeanECA.Research.Z2Reverse.InternalAtomicDefinitions
