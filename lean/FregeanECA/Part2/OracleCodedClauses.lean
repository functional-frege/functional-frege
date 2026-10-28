import FregeanECA.Part2.OracleTupleClauses
import FregeanECA.Part2.OracleSyntaxFacts

/-! Coded first-order compositional clauses agree with the corresponding
typed syntax clauses. -/
namespace FregeanECA.Part2.Oracle
open FFL FFL.FirstOrder

def functionCodeClause (ops : Operations) (table : ValueTable) (code environment value : Nat) : Prop :=
  ∃ arguments, (∀ i, i < termArity code →
    table (termArgument code i) environment (lookupCode arguments i)) ∧
    primitiveGraph ops (termArity code) (termSymbol code) arguments value

def atomicCodeClause (ops : Operations) (table : ValueTable) (code environment : Nat) : Prop :=
  ∃ arguments, (∀ i, i < formulaArity code →
    table (formulaArgument code i) environment (lookupCode arguments i)) ∧
    modelPredicates ops (formulaArity code) (formulaSymbol code)
      (fun i => lookupCode arguments i.val)

def termCodeClause (ops : Operations) (table : ValueTable) (code environment value : Nat) : Prop :=
  (termTag code = 0 ∧ value = lookupCode environment (termVariable code)) ∨
    (termTag code = 1 ∧ functionCodeClause ops table code environment value)

def formulaCodeClause (ops : Operations) (table : TruthTable) (terms : ValueTable)
    (code environment : Nat) : Prop :=
  formulaTag code = 0 ∨
  (formulaTag code = 2 ∧ atomicCodeClause ops terms code environment) ∨
  (formulaTag code = 3 ∧ ¬atomicCodeClause ops terms code environment) ∨
  (formulaTag code = 4 ∧ table (formulaLeft code) environment ∧ table (formulaRight code) environment) ∨
  (formulaTag code = 5 ∧ (table (formulaLeft code) environment ∨ table (formulaRight code) environment)) ∨
  (formulaTag code = 6 ∧ ∀ value, table (formulaLeft code) (pushAssignment value environment)) ∨
  (formulaTag code = 7 ∧ ∃ value, table (formulaLeft code) (pushAssignment value environment))

theorem functionCodeClause_truth (operations : Operations) (table : ValueTable)
    (symbol : language.Func arity) (arguments : Fin arity → ClosedSemiterm language n)
    (environment value : Nat) :
    functionCodeClause operations table (termCode (.func symbol arguments)) environment value ↔
      termClause operations table (.func symbol arguments) environment value := by
  simp only [functionCodeClause, termArity_func, termSymbol_func, bounded_nat_forall_iff,
    termArgument_func, termClause]
  exact coded_function_clause operations arity symbol value
    (fun i output => table (termCode (arguments i)) environment output)

theorem atomicCodeClause_rel_truth (operations : Operations) (table : ValueTable)
    (symbol : language.Rel arity) (arguments : Fin arity → ClosedSemiterm language n)
    (environment : Nat) :
    atomicCodeClause operations table (formulaCode (.rel symbol arguments)) environment ↔
      ∃ actual, (∀ i, table (termCode (arguments i)) environment (actual i)) ∧
        modelPredicates operations arity symbol actual := by
  simp only [atomicCodeClause, modelPredicates, formulaArity_rel, formulaSymbol_rel, bounded_nat_forall_iff,
    formulaArgument_rel]
  simpa only [modelPredicates] using coded_predicate_clause arity
    (fun i output => table (termCode (arguments i)) environment output)
    (modelPredicates operations arity symbol)

theorem atomicCodeClause_nrel_truth (operations : Operations) (table : ValueTable)
    (symbol : language.Rel arity) (arguments : Fin arity → ClosedSemiterm language n)
    (environment : Nat) :
    atomicCodeClause operations table (formulaCode (.nrel symbol arguments)) environment ↔
      ∃ actual, (∀ i, table (termCode (arguments i)) environment (actual i)) ∧
        modelPredicates operations arity symbol actual := by
  simp only [atomicCodeClause, modelPredicates, formulaArity_nrel, formulaSymbol_nrel, bounded_nat_forall_iff,
    formulaArgument_nrel]
  simpa only [modelPredicates] using coded_predicate_clause arity
    (fun i output => table (termCode (arguments i)) environment output)
    (modelPredicates operations arity symbol)

theorem termCodeClause_truth (operations : Operations) (table : ValueTable)
    (term : ClosedSemiterm language n) (environment value : Nat) :
    termCodeClause operations table (termCode term) environment value ↔
      termClause operations table term environment value := by
  cases term with
  | bvar i => simp [termCodeClause, termClause]
  | fvar impossible => exact impossible.elim
  | func symbol arguments =>
      simpa [termCodeClause] using functionCodeClause_truth operations table symbol arguments environment value

theorem formulaCodeClause_truth (operations : Operations) (truth : TruthTable) (values : ValueTable)
    (formula : Semisentence language n) (environment : Nat) :
    formulaCodeClause operations truth values (formulaCode formula) environment ↔
      formulaClause operations truth values formula environment := by
  cases formula <;>
    simp [formulaCodeClause, formulaClause, atomicCodeClause_rel_truth, atomicCodeClause_nrel_truth]

end FregeanECA.Part2.Oracle
