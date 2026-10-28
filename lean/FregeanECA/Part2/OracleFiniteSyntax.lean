import FregeanECA.Part2.OracleLanguage
import Mathlib.Data.List.OfFn

/-! Actual finite subexpression lists for the auxiliary first-order language.
Indices retain the number of bound-variable slots, so entering a quantifier
does not identify syntactically different contexts. No truth predicate occurs
in these definitions. -/
namespace FregeanECA.Part2.Oracle

open FFL FFL.FirstOrder

abbrev FormulaNode := (n : Nat) × Semisentence language n
abbrev TermNode := (n : Nat) × ClosedSemiterm language n

def formulaCode (formula : Semisentence language n) : Nat :=
  Encodable.encode (⟨n, formula⟩ : FormulaNode)

def termCode (term : ClosedSemiterm language n) : Nat :=
  Encodable.encode (⟨n, term⟩ : TermNode)

def termParts {n : Nat} : ClosedSemiterm language n → List TermNode
  | .bvar i => [⟨n, .bvar i⟩]
  | .fvar impossible => nomatch impossible
  | .func symbol arguments =>
      ⟨n, .func symbol arguments⟩ ::
        (List.ofFn fun i => termParts (arguments i)).flatten

def formulaParts {n : Nat} : Semisentence language n → List FormulaNode
  | .verum => [⟨n, .verum⟩]
  | .falsum => [⟨n, .falsum⟩]
  | .rel symbol arguments => [⟨n, .rel symbol arguments⟩]
  | .nrel symbol arguments => [⟨n, .nrel symbol arguments⟩]
  | .and left right => ⟨n, .and left right⟩ :: (formulaParts left ++ formulaParts right)
  | .or left right => ⟨n, .or left right⟩ :: (formulaParts left ++ formulaParts right)
  | .all body => ⟨n, .all body⟩ :: formulaParts body
  | .exs body => ⟨n, .exs body⟩ :: formulaParts body

def formulaTermParts {n : Nat} : Semisentence language n → List TermNode
  | .verum | .falsum => []
  | .rel _ arguments | .nrel _ arguments =>
      (List.ofFn fun i => termParts (arguments i)).flatten
  | .and left right | .or left right => formulaTermParts left ++ formulaTermParts right
  | .all body | .exs body => formulaTermParts body

@[simp] theorem term_mem_parts (term : ClosedSemiterm language n) :
    (⟨n, term⟩ : TermNode) ∈ termParts term := by
  cases term with
  | bvar i => simp [termParts]
  | fvar impossible => exact impossible.elim
  | func symbol arguments => simp [termParts]

@[simp] theorem formula_mem_parts (formula : Semisentence language n) :
    (⟨n, formula⟩ : FormulaNode) ∈ formulaParts formula := by
  cases formula <;> simp [formulaParts]

theorem termParts_argument_subset (symbol : language.Func arity)
    (arguments : Fin arity → ClosedSemiterm language n) (i : Fin arity) :
    termParts (arguments i) ⊆ termParts (.func symbol arguments) := by
  intro node h
  simp only [termParts, List.mem_cons, List.mem_flatten, List.mem_ofFn]
  exact Or.inr ⟨termParts (arguments i), ⟨i, rfl⟩, h⟩

theorem termParts_trans {term : ClosedSemiterm language n} {node : TermNode}
    (h : node ∈ termParts term) : termParts node.2 ⊆ termParts term := by
  induction term with
  | bvar i =>
      simp only [termParts, List.mem_singleton] at h
      cases h
      exact List.Subset.refl _
  | fvar impossible => exact impossible.elim
  | @func arity symbol arguments ih =>
      simp only [termParts, List.mem_cons, List.mem_flatten, List.mem_ofFn] at h
      rcases h with rfl | ⟨parts, ⟨i, rfl⟩, hi⟩
      · exact List.Subset.refl _
      · exact List.Subset.trans (ih i hi) (termParts_argument_subset symbol arguments i)

theorem formulaParts_trans {formula : Semisentence language n} {node : FormulaNode}
    (h : node ∈ formulaParts formula) : formulaParts node.2 ⊆ formulaParts formula := by
  induction formula with
  | verum | falsum | rel _ _ | nrel _ _ =>
      simp only [formulaParts, List.mem_singleton] at h
      cases h
      exact List.Subset.refl _
  | and left right ihl ihr | or left right ihl ihr =>
      simp only [formulaParts, List.mem_cons, List.mem_append] at h
      rcases h with rfl | hl | hr
      · exact List.Subset.refl _
      · intro item hi
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihl hl hi))
      · intro item hi
        exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihr hr hi))
  | all body ih | exs body ih =>
      simp only [formulaParts, List.mem_cons] at h
      rcases h with rfl | hb
      · exact List.Subset.refl _
      · intro item hi
        exact List.mem_cons_of_mem _ (ih hb hi)

theorem formulaTermParts_subformula {formula : Semisentence language n}
    {node : FormulaNode} (h : node ∈ formulaParts formula) :
    formulaTermParts node.2 ⊆ formulaTermParts formula := by
  induction formula with
  | verum | falsum | rel _ _ | nrel _ _ =>
      simp only [formulaParts, List.mem_singleton] at h
      cases h
      exact List.Subset.refl _
  | and left right ihl ihr | or left right ihl ihr =>
      simp only [formulaParts, List.mem_cons, List.mem_append] at h
      rcases h with rfl | hl | hr
      · exact List.Subset.refl _
      · intro item hi
        exact List.mem_append_left _ (ihl hl hi)
      · intro item hi
        exact List.mem_append_right _ (ihr hr hi)
  | all body ih | exs body ih =>
      simp only [formulaParts, List.mem_cons] at h
      rcases h with rfl | hb
      · exact List.Subset.refl _
      · exact ih hb

theorem formulaTermParts_subterm {formula : Semisentence language n}
    {node : TermNode} (h : node ∈ formulaTermParts formula) :
    termParts node.2 ⊆ formulaTermParts formula := by
  induction formula with
  | verum | falsum => simp [formulaTermParts] at h
  | rel symbol arguments | nrel symbol arguments =>
      simp only [formulaTermParts, List.mem_flatten, List.mem_ofFn] at h
      rcases h with ⟨parts, ⟨i, rfl⟩, hi⟩
      intro item hj
      simp only [formulaTermParts, List.mem_flatten, List.mem_ofFn]
      exact ⟨termParts (arguments i), ⟨i, rfl⟩, termParts_trans hi hj⟩
  | and left right ihl ihr | or left right ihl ihr =>
      simp only [formulaTermParts, List.mem_append] at h
      rcases h with hl | hr
      · intro item hi
        exact List.mem_append_left _ (ihl hl hi)
      · intro item hi
        exact List.mem_append_right _ (ihr hr hi)
  | all body ih | exs body ih => exact ih h

def formulaTag (code : Nat) : Nat :=
  match Encodable.decode (α := FormulaNode) code with
  | none => 8
  | some ⟨_, .verum⟩ => 0
  | some ⟨_, .falsum⟩ => 1
  | some ⟨_, .rel _ _⟩ => 2
  | some ⟨_, .nrel _ _⟩ => 3
  | some ⟨_, .and _ _⟩ => 4
  | some ⟨_, .or _ _⟩ => 5
  | some ⟨_, .all _⟩ => 6
  | some ⟨_, .exs _⟩ => 7

def formulaArity (code : Nat) : Nat :=
  match Encodable.decode (α := FormulaNode) code with
  | some ⟨_, .rel (arity := arity) _ _⟩ | some ⟨_, .nrel (arity := arity) _ _⟩ => arity
  | _ => 0

def formulaSymbol (code : Nat) : Nat :=
  match Encodable.decode (α := FormulaNode) code with
  | some ⟨_, .rel symbol _⟩ | some ⟨_, .nrel symbol _⟩ => symbol
  | _ => 0

def formulaLeft (code : Nat) : Nat :=
  match Encodable.decode (α := FormulaNode) code with
  | some ⟨_, .and left _⟩ | some ⟨_, .or left _⟩ => formulaCode left
  | some ⟨_, .all body⟩ | some ⟨_, .exs body⟩ => formulaCode body
  | _ => 0

def formulaRight (code : Nat) : Nat :=
  match Encodable.decode (α := FormulaNode) code with
  | some ⟨_, .and _ right⟩ | some ⟨_, .or _ right⟩ => formulaCode right
  | _ => 0

def formulaArgument (code index : Nat) : Nat :=
  match Encodable.decode (α := FormulaNode) code with
  | some ⟨_, .rel (arity := arity) _ arguments⟩
  | some ⟨_, .nrel (arity := arity) _ arguments⟩ =>
      if h : index < arity then termCode (arguments ⟨index, h⟩) else 0
  | _ => 0

def termTag (code : Nat) : Nat :=
  match Encodable.decode (α := TermNode) code with
  | some ⟨_, .bvar _⟩ => 0
  | some ⟨_, .func _ _⟩ => 1
  | _ => 2

def termArity (code : Nat) : Nat :=
  match Encodable.decode (α := TermNode) code with
  | some ⟨_, .func (arity := arity) _ _⟩ => arity
  | _ => 0

def termSymbol (code : Nat) : Nat :=
  match Encodable.decode (α := TermNode) code with
  | some ⟨_, .func symbol _⟩ => symbol
  | _ => 0

def termVariable (code : Nat) : Nat :=
  match Encodable.decode (α := TermNode) code with
  | some ⟨_, .bvar i⟩ => i.val
  | _ => 0

def termArgument (code index : Nat) : Nat :=
  match Encodable.decode (α := TermNode) code with
  | some ⟨_, .func (arity := arity) _ arguments⟩ =>
      if h : index < arity then termCode (arguments ⟨index, h⟩) else 0
  | _ => 0

def isSubformula (root code : Nat) : Nat :=
  match Encodable.decode (α := FormulaNode) root with
  | none => 0
  | some node => if code ∈ (formulaParts node.2).map Encodable.encode then 1 else 0

def isSubterm (root code : Nat) : Nat :=
  match Encodable.decode (α := FormulaNode) root with
  | none => 0
  | some node => if code ∈ (formulaTermParts node.2).map Encodable.encode then 1 else 0

def packSentence (code : Nat) : Nat :=
  match Encodable.decode (α := Sentence language) code with
  | none => 0
  | some sentence => formulaCode sentence

def isSentence (code : Nat) : Nat :=
  if (Encodable.decode (α := Sentence language) code).isSome then 1 else 0

@[simp] theorem isSubformula_formulaCode (formula : Semisentence language n)
    (node : FormulaNode) :
    isSubformula (formulaCode formula) (Encodable.encode node) = 1 ↔
      node ∈ formulaParts formula := by
  simp [isSubformula, formulaCode]

@[simp] theorem isSubterm_formulaCode (formula : Semisentence language n)
    (node : TermNode) :
    isSubterm (formulaCode formula) (Encodable.encode node) = 1 ↔
      node ∈ formulaTermParts formula := by
  simp [isSubterm, formulaCode]

end FregeanECA.Part2.Oracle
