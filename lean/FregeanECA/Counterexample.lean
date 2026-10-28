import Std

/-!
# The invariant-relation counterexample

The object domain is Bool and application returns its right argument.
Available n-ary relations are exactly predicates invariant under flipping
all coordinates simultaneously. The semantic B1--B5 families hold for
every positive arity, but the positive atom x = a has no relation at the
parameter assignment a = false. No formula syntax or general soundness
theorem is assumed in this module.
-/

namespace FregeanECA.Counterexample

abbrev Tuple (n : Nat) := Fin n → Bool

def swap {n : Nat} (xs : Tuple n) : Tuple n := fun i => !(xs i)

def application (_a x : Bool) : Bool := x

/-- Left-associated application of an object to all arguments of a tuple. -/
def applyTuple : (n : Nat) → Bool → Tuple n → Bool
  | 0, a, _ => a
  | n + 1, a, xs =>
      application (applyTuple n a (fun i => xs i.castSucc)) (xs (Fin.last n))

theorem a_positive_application_returns_the_last_argument
    (n : Nat) (a : Bool) (xs : Tuple (n + 1)) :
    applyTuple (n + 1) a xs = xs (Fin.last n) := rfl

/-- Append the quantified object as the final coordinate. -/
def append {n : Nat} (xs : Tuple n) (y : Bool) : Tuple (n + 1) :=
  fun i => if h : i.val < n then xs ⟨i.val, h⟩ else y

theorem swap_append {n : Nat} (xs : Tuple n) (y : Bool) :
    swap (append xs y) = append (swap xs) (!y) := by
  funext i
  simp only [swap, append]
  split <;> rfl

structure Relation (n : Nat) where
  holds : Tuple n → Prop
  invariant : ∀ xs, holds (swap xs) ↔ holds xs

def universalRelation (n : Nat) : Relation n where
  holds := fun _ => True
  invariant := fun _ => Iff.rfl

theorem each_relation_sort_is_nonempty (n : Nat) : Nonempty (Relation (n + 1)) :=
  ⟨universalRelation (n + 1)⟩

def diagonal : Relation 2 where
  holds := fun xs => xs 0 = xs 1
  invariant := by
    intro xs
    change (Bool.not (xs 0) = Bool.not (xs 1)) ↔ xs 0 = xs 1
    constructor
    · intro same
      have twice := congrArg Bool.not same
      simpa using twice
    · exact congrArg Bool.not

def intersection {n : Nat} (P Q : Relation n) : Relation n where
  holds := fun xs => P.holds xs ∧ Q.holds xs
  invariant := fun xs => and_congr (P.invariant xs) (Q.invariant xs)

def union {n : Nat} (P Q : Relation n) : Relation n where
  holds := fun xs => P.holds xs ∨ Q.holds xs
  invariant := fun xs => or_congr (P.invariant xs) (Q.invariant xs)

/-- B3 uses genuine repeated application, not an assumed invariant map. -/
def substitute {m n : Nat} (R : Relation (m + 1))
    (programs : Fin (m + 1) → Bool) : Relation (n + 1) where
  holds := fun xs => R.holds (fun i => applyTuple (n + 1) (programs i) xs)
  invariant := by
    intro xs
    change R.holds (swap (fun _ => xs (Fin.last n))) ↔
      R.holds (fun _ => xs (Fin.last n))
    exact R.invariant _

def existsProject {n : Nat} (R : Relation (n + 1)) : Relation n where
  holds := fun xs => ∃ y, R.holds (append xs y)
  invariant := by
    intro xs
    constructor
    · rintro ⟨y, witness⟩
      refine ⟨!y, (R.invariant (append xs (!y))).mp ?_⟩
      simpa only [swap_append, Bool.not_not] using witness
    · rintro ⟨y, witness⟩
      refine ⟨!y, ?_⟩
      simpa only [swap_append] using (R.invariant (append xs y)).mpr witness

def forallProject {n : Nat} (R : Relation (n + 1)) : Relation n where
  holds := fun xs => ∀ y, R.holds (append xs y)
  invariant := by
    intro xs
    constructor
    · intro every y
      apply (R.invariant (append xs y)).mp
      simpa only [swap_append] using every (!y)
    · intro every y
      have witness := (R.invariant (append xs (!y))).mpr (every (!y))
      simpa only [swap_append, Bool.not_not] using witness

/-- The five semantic specification families, at all positive arities. -/
structure SpecificationClosure : Prop where
  equality : ∃ delta : Relation 2, ∀ xs,
    delta.holds xs ↔ xs 0 = xs 1
  intersection_union : ∀ n (P Q : Relation (n + 1)),
    ∃ U V : Relation (n + 1), ∀ xs,
      (U.holds xs ↔ P.holds xs ∧ Q.holds xs) ∧
      (V.holds xs ↔ P.holds xs ∨ Q.holds xs)
  substitution : ∀ m n (R : Relation (m + 1)) (programs : Fin (m + 1) → Bool),
    ∃ P : Relation (n + 1), ∀ xs,
      P.holds xs ↔ R.holds (fun i => applyTuple (n + 1) (programs i) xs)
  existential_projection : ∀ n (R : Relation (n + 2)),
    ∃ P : Relation (n + 1), ∀ xs,
      P.holds xs ↔ ∃ y, R.holds (append xs y)
  universal_projection : ∀ n (R : Relation (n + 2)),
    ∃ P : Relation (n + 1), ∀ xs,
      P.holds xs ↔ ∀ y, R.holds (append xs y)

theorem the_invariant_relations_satisfy_all_five_families : SpecificationClosure where
  equality := ⟨diagonal, fun _ => Iff.rfl⟩
  intersection_union := fun _ P Q =>
    ⟨intersection P Q, union P Q, fun _ => ⟨Iff.rfl, Iff.rfl⟩⟩
  substitution := fun _ _ R programs => ⟨substitute R programs, fun _ => Iff.rfl⟩
  existential_projection := fun _ R => ⟨existsProject R, fun _ => Iff.rfl⟩
  universal_projection := fun _ R => ⟨forallProject R, fun _ => Iff.rfl⟩

theorem the_object_domain_is_nontrivial : ∃ a b : Bool, a ≠ b :=
  ⟨false, true, by decide⟩

/-- This is the comprehension body x = a, with its parameter fixed to false. -/
theorem no_relation_defines_parameter_equality_at_false :
    ¬ ∃ P : Relation 1, ∀ x : Bool, P.holds (fun _ => x) ↔ x = false := by
  rintro ⟨P, defines⟩
  have atFalse : P.holds (fun _ => false) := (defines false).mpr rfl
  have atTrue : P.holds (fun _ => true) :=
    (P.invariant (fun _ => false)).mpr atFalse
  have impossible : true = false := (defines true).mp atTrue
  cases impossible

theorem parameter_equalities_do_not_all_have_relations :
    ¬ ∀ a : Bool, ∃ P : Relation 1, ∀ x : Bool,
      P.holds (fun _ => x) ↔ x = a := by
  intro comprehension
  exact no_relation_defines_parameter_equality_at_false (comprehension false)

/-- A concrete nontrivial B1--B5 structure failing an atomic positive instance. -/
theorem positive_specification_closure_does_not_supply_parameter_singletons :
    (∃ a b : Bool, a ≠ b) ∧ SpecificationClosure ∧
      ¬ (∀ a : Bool, ∃ P : Relation 1, ∀ x : Bool,
        P.holds (fun _ => x) ↔ x = a) :=
  ⟨the_object_domain_is_nontrivial,
    the_invariant_relations_satisfy_all_five_families,
    parameter_equalities_do_not_all_have_relations⟩

end FregeanECA.Counterexample
