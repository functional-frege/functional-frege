import FregeanECA.Part2.OracleTargetBindings

namespace FregeanECA.Part2.OracleTarget
open FFL FFL.FirstOrder Positive
noncomputable section

def liftSlot (arity index : Nat) : Nat :=
  if arity = 1 ∨ arity = 2 then index+1 else index

def tableSlots : Slots where
  functions := fun n symbol => liftSlot n (baseSlots.functions n symbol)
  relations := fun n symbol =>
    if (n = 2 ∨ n = 3) ∧ symbol = 100 then 0
    else liftSlot (n-1) (baseSlots.relations n symbol)

def tableAssignment (operations : Operations) (P : Relations operations 1)
    (V : Relations operations 2) : PredicateAssignment (Relations operations) :=
  pushPredicate (pushPredicate (baseAssignment operations) 1 P) 2 V

def tabledPredicates (operations : Operations) (P : Relations operations 1)
    (V : Relations operations 2) : ∀ n, Nat → (Fin n → Nat) → Prop :=
  fun n symbol arguments =>
    if h : n = 2 ∧ symbol = 100 then
      P.val ![arguments ⟨0, by omega⟩, arguments ⟨1, by omega⟩]
    else if h : n = 3 ∧ symbol = 100 then
      V.val ![arguments ⟨0, by omega⟩, arguments ⟨1, by omega⟩, arguments ⟨2, by omega⟩]
    else Oracle.modelPredicates operations n symbol arguments

@[instance_reducible] def tabledStructure (operations : Operations) (P : Relations operations 1)
    (V : Relations operations 2) : Structure Oracle.language Nat :=
  Oracle.interpretation (Oracle.modelOperations operations) (tabledPredicates operations P V)

theorem tableAssignment_old (operations : Operations) (P : Relations operations 1)
    (V : Relations operations 2) (n index : Nat) :
    tableAssignment operations P V n (liftSlot n index) = baseAssignment operations n index := by
  by_cases h1 : n = 1
  · subst n; simp [tableAssignment, liftSlot, pushPredicate]
  by_cases h2 : n = 2
  · subst n; simp [tableAssignment, liftSlot, pushPredicate]
  simp [tableAssignment, liftSlot, pushPredicate, h1, h2]

theorem tabled_relation_old (operations : Operations) (P : Relations operations 1)
    (V : Relations operations 2) (n symbol : Nat) (arguments : Fin n → Nat)
    (ordinary : ¬ ((n = 2 ∨ n = 3) ∧ symbol = 100)) :
    @Structure.rel Oracle.language Nat (tabledStructure operations P V) n symbol arguments ↔
      @Structure.rel Oracle.language Nat (Oracle.modelStructure operations) n symbol arguments := by
  have h2 : ¬ (n = 2 ∧ symbol = 100) := by tauto
  have h3 : ¬ (n = 3 ∧ symbol = 100) := by tauto
  change tabledPredicates operations P V n symbol arguments ↔
    Oracle.modelPredicates operations n symbol arguments
  simp only [tabledPredicates, h2, h3, ↓reduceDIte]

theorem table_bindings (operations : Operations) (P : Relations operations 1)
    (V : Relations operations 2) :
    letI := tabledStructure operations P V
    Bindings (Oracle.definableModel operations) (tableAssignment operations P V) tableSlots := by
  letI := tabledStructure operations P V
  constructor
  · intro n symbol arguments output
    simp only [tableSlots, tableAssignment_old]
    exact (base_bindings operations).functions (source := Oracle.modelStructure operations)
      n symbol arguments output
  · intro n symbol arguments
    by_cases special : (n = 2 ∨ n = 3) ∧ symbol = 100
    · rcases special with ⟨h2 | h3, rfl⟩
      · subst n
        have eta : ![arguments 0, arguments 1] = arguments := by
          funext i
          exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i
        simp only [relationHolds, tableSlots, ↓reduceIte, tableAssignment, pushPredicate,
          ↓reduceDIte, tabledStructure, Oracle.interpretation, tabledPredicates]
        change P.val arguments ↔ P.val ![arguments 0, arguments 1]
        rw [eta]
      · subst n
        have eta : ![arguments 0, arguments 1, arguments 2] = arguments := by
          funext i
          exact Fin.cases rfl (fun j => Fin.cases rfl
            (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
        simp only [relationHolds, tableSlots, ↓reduceIte, tableAssignment, pushPredicate,
          ↓reduceDIte, tabledStructure, Oracle.interpretation, tabledPredicates]
        change V.val arguments ↔ V.val ![arguments 0, arguments 1, arguments 2]
        rw [eta]
    · apply Iff.trans ?_ (tabled_relation_old operations P V n symbol arguments special).symm
      cases n with
      | zero =>
        simpa only [relationHolds, tableSlots, special, ↓reduceIte, Nat.zero_sub,
          tableAssignment_old] using (base_bindings operations).relations
            (source := Oracle.modelStructure operations) 0 symbol arguments
      | succ n =>
        simpa only [relationHolds, tableSlots, special, ↓reduceIte, Nat.add_sub_cancel_right,
          tableAssignment_old] using (base_bindings operations).relations
            (source := Oracle.modelStructure operations) (n+1) symbol arguments

end
end FregeanECA.Part2.OracleTarget
