import FregeanECA.Part2.OracleFiniteTables

/-! Replace finite argument tuples in the compositional clauses by one object
code. These equivalences use actual encoded finite lists and the primitive
operation graph, not a uniform term evaluator. -/
namespace FregeanECA.Part2.Oracle

open FFL FFL.FirstOrder

theorem coded_function_clause (operations : Operations) (arity symbol value : Nat)
    (condition : Fin arity → Nat → Prop) :
    (∃ code, (∀ i : Fin arity, condition i (lookupCode code i.val)) ∧
      primitiveGraph operations arity symbol code value) ↔
    (∃ actual : Fin arity → Nat, (∀ i, condition i (actual i)) ∧
      value = primitiveValue operations arity symbol actual) := by
  constructor
  · rintro ⟨code, conditions, actual, hcode, hvalue⟩
    subst code
    exact ⟨actual, fun i => by simpa using conditions i, hvalue.symm⟩
  · rintro ⟨actual, conditions, hvalue⟩
    refine ⟨assignmentCode actual, ?_, actual, rfl, hvalue.symm⟩
    intro i
    simpa using conditions i

theorem coded_predicate_clause (arity : Nat) (condition : Fin arity → Nat → Prop)
    (predicate : (Fin arity → Nat) → Prop) :
    (∃ code, (∀ i : Fin arity, condition i (lookupCode code i.val)) ∧
      predicate (fun i => lookupCode code i.val)) ↔
    (∃ actual : Fin arity → Nat, (∀ i, condition i (actual i)) ∧ predicate actual) := by
  constructor
  · rintro ⟨code, conditions, hp⟩
    exact ⟨_,conditions,hp⟩
  · rintro ⟨actual, conditions, hp⟩
    refine ⟨assignmentCode actual, ?_, ?_⟩
    · intro i
      simpa using conditions i
    · simpa using hp

theorem bounded_nat_forall_iff (arity : Nat) (predicate : Nat → Prop) :
    (∀ i : Nat, i < arity → predicate i) ↔ ∀ i : Fin arity, predicate i.val := by
  constructor
  · exact fun h i => h i.val i.isLt
  · exact fun h i hi => h ⟨i,hi⟩

end FregeanECA.Part2.Oracle
