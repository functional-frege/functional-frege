import FregeanECA.Part2.OracleTargetTranslation
import FregeanECA.Part2.OracleModel

namespace FregeanECA.Part2.OracleTarget
open FFL FFL.FirstOrder Positive
noncomputable section

abbrev Operations := ∀ n, Nat → (Fin n → Nat) → Nat
abbrev Relations (operations : Operations) :=
  @FirstOrderRelations.Relation Oracle.language Nat (Oracle.modelStructure operations)

def baseSlots : Slots where
  functions := fun _ symbol => 4*symbol+1
  relations := fun n symbol => if n = 0 then 4*symbol+2 else 4*symbol+4

def functionGraph (operations : Operations) (n symbol : Nat) : Relations operations n := by
  letI := Oracle.modelStructure operations
  refine ⟨fun values => values 0 = Structure.func (L := Oracle.language) symbol (fun i : Fin n => values i.succ), ?_⟩
  refine ⟨Semiformula.rel (arity := 2) 0
    ![Semiterm.bvar 0, Semiterm.func symbol (fun i : Fin n => .bvar i.succ)], ?_⟩
  intro values
  rfl

def predicateRelation (operations : Operations) (n symbol : Nat) : Relations operations n := by
  letI := Oracle.modelStructure operations
  exact ⟨fun values => Structure.rel (L := Oracle.language) symbol values,
    ⟨Semiformula.rel symbol (fun i : Fin (n+1) => .bvar i), fun _ => Iff.rfl⟩⟩

/-- The fixed auxiliary model interprets all nullary predicates as false. -/
def nullaryRelation (operations : Operations) (_symbol : Nat) : Relations operations 0 := by
  letI := Oracle.modelStructure operations
  exact ⟨fun _ => False, ⟨Semiformula.falsum, fun _ => Iff.rfl⟩⟩

def emptyRelation (operations : Operations) (n : Nat) : Relations operations n := by
  letI := Oracle.modelStructure operations
  exact ⟨fun _ => False, ⟨Semiformula.falsum, fun _ => Iff.rfl⟩⟩

def baseAssignment (operations : Operations) : PredicateAssignment (Relations operations) :=
  fun n index =>
    if index % 4 = 1 then functionGraph operations n (index / 4)
    else if index % 4 = 0 ∧ 0 < index then predicateRelation operations n (index / 4 - 1)
    else if h : n = 0 then
      h ▸ nullaryRelation operations (index / 4)
    else emptyRelation operations n

theorem base_functions (operations : Operations) (n symbol : Nat) :
    baseAssignment operations n (4*symbol+1) = functionGraph operations n symbol := by
  have hmod : (4*symbol+1)%4 = 1 := by omega
  have hdiv : (4*symbol+1)/4 = symbol := by omega
  simp only [baseAssignment, hmod, if_pos, hdiv]

theorem base_relations (operations : Operations) (n symbol : Nat) :
    baseAssignment operations n (4*symbol+4) = predicateRelation operations n symbol := by
  have hmod : (4*symbol+4)%4 = 0 := by omega
  have hdiv : (4*symbol+4)/4-1 = symbol := by omega
  have hpos : 0 < 4*symbol+4 := by omega
  simp only [baseAssignment, hmod, Nat.zero_ne_one, if_false, hpos, and_self, if_pos, hdiv]

theorem base_nullary (operations : Operations) (symbol : Nat) :
    baseAssignment operations 0 (4*symbol+2) = nullaryRelation operations symbol := by
  have hmod : (4*symbol+2)%4 = 2 := by omega
  have hdiv : (4*symbol+2)/4 = symbol := by omega
  simp only [baseAssignment, hmod, OfNat.ofNat_ne_one, if_false, OfNat.ofNat_ne_zero,
    false_and, dite_true, hdiv]

theorem base_bindings (operations : Operations) :
    letI := Oracle.modelStructure operations
    Bindings (Oracle.definableModel operations) (baseAssignment operations) baseSlots := by
  letI := Oracle.modelStructure operations
  constructor
  · intro n symbol arguments output
    simp only [baseSlots, base_functions]
    rfl
  · intro n symbol arguments
    cases n with
    | zero =>
      simp only [relationHolds, baseSlots, ↓reduceIte, base_nullary]
      have ha : arguments = Fin.elim0 := Subsingleton.elim _ _
      rw [ha]
      rfl
    | succ n =>
      simp only [relationHolds, baseSlots, Nat.succ_ne_zero, if_false, base_relations]
      rfl

end
end FregeanECA.Part2.OracleTarget
