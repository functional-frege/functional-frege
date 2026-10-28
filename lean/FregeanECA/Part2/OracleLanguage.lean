import Foundation.FirstOrder.Basic.Definability
import Foundation.FirstOrder.Basic.Coding

/-! An auxiliary oracle language with names and a syntactic diagonal operation.
The operation is interpreted by actual formula decoding and substitution; no
truth predicate or undefinability assumption occurs in the interpretation.
This is a prerequisite for the complement-only countermodel, not that result.
-/
namespace FregeanECA.Part2.Oracle

open FFL FFL.FirstOrder

/-- The infinite signature has an effective symbol encoding. -/
abbrev language : Language where
  Func := fun _ => Nat
  Rel := fun _ => Nat

instance : language.Encodable where
  func := fun _ => inferInstanceAs (Encodable Nat)
  rel := fun _ => inferInstanceAs (Encodable Nat)

/-- There is a name for each member of the intended domain. -/
def name (a : Nat) : Semiterm language ξ n := .func (arity := 0) a Fin.elim0

/-- The distinguished unary function symbol denotes syntactic diagonalisation. -/
def diagonalTerm (t : Semiterm language ξ n) : Semiterm language ξ n :=
  .func (arity := 1) 0 (fun _ => t)

/-- Substitute the name of a code in the formula bearing that code. -/
def diagonalCode (code : Nat) : Nat :=
  match Encodable.decode (α := Semisentence language 1) code with
  | none => 0
  | some formula => Encodable.encode (formula ⇜ fun _ => (name code : ClosedTerm language))

theorem diagonalCode_encode (formula : Semisentence language 1) :
    diagonalCode (Encodable.encode formula) =
      Encodable.encode (formula ⇜ fun _ => (name (Encodable.encode formula) : ClosedTerm language)) := by
  simp [diagonalCode]

/-- Arbitrary interpretations of the remaining symbols are allowed. -/
@[instance_reducible] def interpretation
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat)
    (predicates : ∀ n, Nat → (Fin n → Nat) → Prop) : Structure language Nat where
  func := fun {n} f xs =>
    if h : n = 0 then f
    else if h : n = 1 ∧ f = 0 then diagonalCode (xs ⟨0, by omega⟩)
    else operations n f xs
  rel := fun {n} r xs => predicates n r xs

section Semantics
variable (operations : ∀ n, Nat → (Fin n → Nat) → Nat)
variable (predicates : ∀ n, Nat → (Fin n → Nat) → Prop)
local notation "oracleStructure" => interpretation operations predicates

@[simp] theorem name_value (a : Nat) (bound : Fin n → Nat) (free : ξ → Nat) :
    (name a : Semiterm language ξ n).val (s := oracleStructure) bound free = a := by
  rfl

@[simp] theorem diagonalTerm_value (t : Semiterm language ξ n)
    (bound : Fin n → Nat) (free : ξ → Nat) :
    (diagonalTerm t).val (s := oracleStructure) bound free = diagonalCode (t.val (s := oracleStructure) bound free) := by
  rfl

def diagonal (formula : Semisentence language 1) : Semisentence language 1 :=
  formula ⇜ fun _ => diagonalTerm (.bvar 0)

def fixedPoint (formula : Semisentence language 1) : Sentence language :=
  diagonal formula ⇜ fun _ => name (Encodable.encode (diagonal formula))

/-- A semantic fixed point built from the concrete syntax, for every oracle. -/
theorem fixedPoint_truth (formula : Semisentence language 1) :
    (fixedPoint formula).Evalb (s := oracleStructure) Fin.elim0 ↔
      formula.Evalb (s := oracleStructure) (fun _ => Encodable.encode (fixedPoint formula)) := by
  simp only [fixedPoint, diagonal, Semiformula.Evalb, Semiformula.eval_substs]
  simp only [Function.comp_def, name_value, diagonalTerm_value, Semiterm.val_bvar]
  rw [diagonalCode_encode]

/-- No formula of this language defines its own sentence truth set. -/
theorem no_truth_formula :
    ¬ ∃ truth : Semisentence language 1,
      ∀ sentence : Sentence language,
        sentence.Evalb (s := oracleStructure) Fin.elim0 ↔ truth.Evalb (s := oracleStructure) (fun _ => Encodable.encode sentence) := by
  rintro ⟨truth, correct⟩
  let liar := fixedPoint (∼truth)
  have hd := fixedPoint_truth operations predicates (∼truth)
  have hc := correct liar
  have hn : liar.Evalb (s := oracleStructure) Fin.elim0 ↔ ¬ truth.Evalb (s := oracleStructure) (fun _ => Encodable.encode liar) := by
    simpa [liar] using hd
  by_cases ht : truth.Evalb (s := oracleStructure) (fun _ => Encodable.encode liar)
  · exact (hn.mp (hc.mpr ht)) ht
  · exact ht (hc.mp (hn.mpr ht))

/-- Parameter elimination uses the actual names, not an extra comprehension
principle or a truth predicate. -/
def closeParameters (formula : Semiformula language Nat n) :
    Semisentence language n := Rew.rewrite name ▹ formula

theorem closeParameters_truth (formula : Semiformula language Nat n)
    (values : Fin n → Nat) :
    (closeParameters formula).Evalb (s := oracleStructure) values ↔
      formula.Eval (s := oracleStructure) values id := by
  simp only [closeParameters, Semiformula.Evalb, Semiformula.eval_rewrite, name_value]
  rfl

def sentenceTruth (code : Nat) : Prop :=
  ∃ sentence : Sentence language, Encodable.encode sentence = code ∧
    sentence.Evalb (s := oracleStructure) Fin.elim0

@[simp] theorem sentenceTruth_encode (sentence : Sentence language) :
    sentenceTruth operations predicates (Encodable.encode sentence) ↔
      sentence.Evalb (s := oracleStructure) Fin.elim0 := by
  simp [sentenceTruth]

/-- Genuine first-order undefinability, including arbitrary object parameters.
The conclusion uses Foundation's formula-witness definition of definability. -/
theorem no_definable_truth :
    ¬ @Language.Definable language Nat oracleStructure 1
      (fun values => sentenceTruth operations predicates (values 0)) := by
  rintro ⟨formula, correct⟩
  apply no_truth_formula operations predicates
  refine ⟨closeParameters formula, fun sentence => ?_⟩
  rw [closeParameters_truth]
  exact (sentenceTruth_encode operations predicates sentence).symm.trans
    (correct (fun _ => Encodable.encode sentence)).symm

end Semantics
end FregeanECA.Part2.Oracle





