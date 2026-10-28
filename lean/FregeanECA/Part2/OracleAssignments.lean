import FregeanECA.Part2.OracleLanguage
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Logic.Equiv.List

/-! Finite assignment coding and the satisfaction formula for each fixed
first-order formula. There is deliberately no uniform satisfaction predicate.
Binary function symbol zero is reserved for decoded-list lookup; binary symbol
one, reserved for combinatory application, is preserved by this wrapper. -/
namespace FregeanECA.Part2.Oracle

open FFL FFL.FirstOrder

def lookupCode (code index : Nat) : Nat :=
  ((Encodable.decode (α := List Nat) code).getD []).getD index 0

def assignmentCode (values : Fin n → Nat) : Nat :=
  Encodable.encode (List.ofFn values)

def pushAssignment (value code : Nat) : Nat :=
  Encodable.encode (value :: (Encodable.decode (α := List Nat) code).getD [])

@[simp] theorem lookupCode_pushAssignment_zero (value code : Nat) :
    lookupCode (pushAssignment value code) 0 = value := by
  simp [lookupCode, pushAssignment]

@[simp] theorem lookupCode_pushAssignment_succ (value code index : Nat) :
    lookupCode (pushAssignment value code) (index + 1) = lookupCode code index := by
  simp [lookupCode, pushAssignment]

@[simp] theorem lookupCode_assignmentCode (values : Fin n → Nat) (i : Fin n) :
    lookupCode (assignmentCode values) i.val = values i := by
  simp only [lookupCode, assignmentCode, Encodable.encodek, Option.getD_some]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def withLookup (operations : ∀ n, Nat → (Fin n → Nat) → Nat) :
    ∀ n, Nat → (Fin n → Nat) → Nat := fun n symbol values =>
  if h : n = 2 ∧ symbol = 0 then
    lookupCode (values ⟨0, by omega⟩) (values ⟨1, by omega⟩)
  else operations n symbol values

@[simp] theorem withLookup_binary_zero
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat) (values : Fin 2 → Nat) :
    withLookup operations 2 0 values = lookupCode (values 0) (values 1) := by
  simp [withLookup]

@[simp] theorem withLookup_other
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat)
    (symbol : Nat) (values : Fin n → Nat) (h : ¬ (n = 2 ∧ symbol = 0)) :
    withLookup operations n symbol values = operations n symbol values := by
  simp [withLookup, h]

@[simp] theorem withLookup_binary_one
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat) (values : Fin 2 → Nat) :
    withLookup operations 2 1 values = operations 2 1 values := by
  simp [withLookup]

def lookupTerm (environment index : Semiterm language ξ n) : Semiterm language ξ n :=
  .func (arity := 2) 0 ![environment, index]

/-- For each fixed formula, replace its finitely many free slots by lookup
terms applied to one coded assignment. This is an ordinary formula. -/
def satisfactionFormula (formula : Semisentence language n) : Semisentence language 1 :=
  formula ⇜ fun i => lookupTerm (.bvar 0) (name i.val)

def assignmentTerm (term : Semiterm language Empty n) : Semiterm language Empty 1 :=
  Rew.subst (fun i => lookupTerm (.bvar 0) (name i.val)) term

section Semantics
variable (operations : ∀ n, Nat → (Fin n → Nat) → Nat)
variable (predicates : ∀ n, Nat → (Fin n → Nat) → Prop)
local notation "assignmentStructure" => interpretation (withLookup operations) predicates

@[simp] theorem lookupTerm_value (environment index : Semiterm language ξ n)
    (bound : Fin n → Nat) (free : ξ → Nat) :
    (lookupTerm environment index).val (s := assignmentStructure) bound free =
      lookupCode (environment.val (s := assignmentStructure) bound free)
        (index.val (s := assignmentStructure) bound free) := by
  rfl

theorem satisfactionFormula_truth (formula : Semisentence language n) (code : Nat) :
    (satisfactionFormula formula).Evalb (s := assignmentStructure) (fun _ => code) ↔
      formula.Evalb (s := assignmentStructure) (fun i => lookupCode code i.val) := by
  simp [satisfactionFormula, Semiformula.Evalb, Semiformula.eval_substs,
    Function.comp_def, lookupTerm_value]

theorem satisfactionFormula_assignmentCode (formula : Semisentence language n)
    (values : Fin n → Nat) :
    (satisfactionFormula formula).Evalb (s := assignmentStructure)
        (fun _ => assignmentCode values) ↔
      formula.Evalb (s := assignmentStructure) values := by
  rw [satisfactionFormula_truth]
  simp

theorem assignmentTerm_value (term : Semiterm language Empty n) (code : Nat) :
    (assignmentTerm term).val (s := assignmentStructure) (fun _ => code) Empty.elim =
      term.val (s := assignmentStructure) (fun i => lookupCode code i.val) Empty.elim := by
  simp [assignmentTerm, Semiterm.val_substs, Function.comp_def, lookupTerm_value]

theorem assignmentTerm_assignmentCode (term : Semiterm language Empty n)
    (values : Fin n → Nat) :
    (assignmentTerm term).val (s := assignmentStructure)
        (fun _ => assignmentCode values) Empty.elim =
      term.val (s := assignmentStructure) values Empty.elim := by
  rw [assignmentTerm_value]
  simp

end Semantics

def equalTerm (left right : Semiterm language ξ n) : Semiformula language ξ n :=
  .rel (arity := 2) 0 ![left, right]

/-- The code identifies one fixed formula. Its truth under a coded assignment
is expressed by substitution into that formula itself. -/
def formulaEntry (formula : (n : Nat) × Semisentence language n) :
    Semisentence language 2 :=
  .and (equalTerm (.bvar 0) (name (Encodable.encode formula)))
    (formula.2 ⇜ fun i => lookupTerm (.bvar 1) (name i.val))

def termEntry (term : (n : Nat) × Semiterm language Empty n) :
    Semisentence language 3 :=
  .and (equalTerm (.bvar 0) (name (Encodable.encode term)))
    (equalTerm (.bvar 2) (Rew.subst
      (fun i => lookupTerm (.bvar 1) (name i.val)) term.2))

def finiteFormulaTable : List ((n : Nat) × Semisentence language n) →
    Semisentence language 2
  | [] => ⊥
  | formula :: formulas => .or (formulaEntry formula) (finiteFormulaTable formulas)

def finiteTermTable : List ((n : Nat) × Semiterm language Empty n) →
    Semisentence language 3
  | [] => ⊥
  | term :: terms => .or (termEntry term) (finiteTermTable terms)

section Tables
variable (operations : ∀ n, Nat → (Fin n → Nat) → Nat)
variable (predicates : ∀ n, Nat → (Fin n → Nat) → Prop)
variable (equality : ∀ values : Fin 2 → Nat, predicates 2 0 values ↔ values 0 = values 1)
local notation "assignmentStructure" => interpretation (withLookup operations) predicates

private theorem table_and_truth (p q : Semisentence language n) (values : Fin n → Nat) :
    (Semiformula.and p q).Evalb (s := assignmentStructure) values ↔
      p.Evalb (s := assignmentStructure) values ∧ q.Evalb (s := assignmentStructure) values := Iff.rfl

private theorem table_or_truth (p q : Semisentence language n) (values : Fin n → Nat) :
    (Semiformula.or p q).Evalb (s := assignmentStructure) values ↔
      p.Evalb (s := assignmentStructure) values ∨ q.Evalb (s := assignmentStructure) values := Iff.rfl

include equality

theorem equalTerm_truth (left right : Semiterm language ξ n)
    (bound : Fin n → Nat) (free : ξ → Nat) :
    (equalTerm left right).Eval (s := assignmentStructure) bound free ↔
      left.val (s := assignmentStructure) bound free =
        right.val (s := assignmentStructure) bound free := by
  exact equality _

theorem formulaEntry_truth (formula : (n : Nat) × Semisentence language n)
    (values : Fin 2 → Nat) :
    (formulaEntry formula).Evalb (s := assignmentStructure) values ↔
      values 0 = Encodable.encode formula ∧
        formula.2.Evalb (s := assignmentStructure) (fun i => lookupCode (values 1) i.val) := by
  rw [formulaEntry, table_and_truth]
  simp [Semiformula.Evalb, Semiformula.eval_substs,
    equalTerm_truth operations predicates equality, Function.comp_def]

theorem termEntry_truth (term : (n : Nat) × Semiterm language Empty n)
    (values : Fin 3 → Nat) :
    (termEntry term).Evalb (s := assignmentStructure) values ↔
      values 0 = Encodable.encode term ∧
        values 2 = term.2.val (s := assignmentStructure)
          (fun i => lookupCode (values 1) i.val) Empty.elim := by
  rw [termEntry, table_and_truth]
  simp [Semiformula.Evalb, Semiterm.val_substs,
    equalTerm_truth operations predicates equality, Function.comp_def]

theorem finiteFormulaTable_truth (formulas : List ((n : Nat) × Semisentence language n))
    (values : Fin 2 → Nat) :
    (finiteFormulaTable formulas).Evalb (s := assignmentStructure) values ↔
      ∃ formula ∈ formulas, values 0 = Encodable.encode formula ∧
        formula.2.Evalb (s := assignmentStructure) (fun i => lookupCode (values 1) i.val) := by
  induction formulas with
  | nil => simp [finiteFormulaTable, Semiformula.Evalb]
  | cons formula formulas ih =>
      rw [finiteFormulaTable, table_or_truth, formulaEntry_truth operations predicates equality, ih]
      simp

theorem finiteTermTable_truth (terms : List ((n : Nat) × Semiterm language Empty n))
    (values : Fin 3 → Nat) :
    (finiteTermTable terms).Evalb (s := assignmentStructure) values ↔
      ∃ term ∈ terms, values 0 = Encodable.encode term ∧
        values 2 = term.2.val (s := assignmentStructure)
          (fun i => lookupCode (values 1) i.val) Empty.elim := by
  induction terms with
  | nil => simp [finiteTermTable, Semiformula.Evalb]
  | cons term terms ih =>
      rw [finiteTermTable, table_or_truth, termEntry_truth operations predicates equality, ih]
      simp

end Tables
end FregeanECA.Part2.Oracle
