import Frege.CombinatoryAlgebra
import FregeanECA.Syntax

/-!
# A checked arithmetic starting point for Part II

The K/S equations alone give an injective successor with a missing zero in
every nontrivial combinatory algebra. No application extensionality is used.
The least-domain formula below is the actual impredicative formula in the
existing applicative syntax. Its representation is an explicitly named NEW
comprehension instance, not a consequence assumed of Part I's positive schema.
This file does not yet formalise arithmetic recursion or a Z2 proof translation.
-/

namespace FregeanECA.Part2.Arithmetic

universe u v
variable {D : Type u} {R : Nat → Type v}

def zero (A : Frege.CombinatoryAlgebra D) : D := A.identity

def successor (A : Frege.CombinatoryAlgebra D) (x : D) : D :=
  A.apply A.constant x

/-- Applying a successor code recovers its predecessor. -/
theorem predecessor_equation (A : Frege.CombinatoryAlgebra D) (x argument : D) :
    A.apply (successor A x) argument = x :=
  A.constant_returns_first_argument x argument

theorem successor_injective (A : Frege.CombinatoryAlgebra D) {x y : D}
    (h : successor A x = successor A y) : x = y := by
  have applied := congrArg (fun f => A.apply f (zero A)) h
  simpa only [predecessor_equation] using applied

theorem zero_not_successor (A : Frege.CombinatoryAlgebra D)
    (nontrivial : ∃ a b : D, a ≠ b) (x : D) : zero A ≠ successor A x := by
  intro h
  have collapse : ∀ y : D, y = x := by
    intro y
    calc
      y = A.apply (zero A) y := (A.identity_returns_its_argument y).symm
      _ = A.apply (successor A x) y := congrArg (fun f => A.apply f y) h
      _ = x := predecessor_equation A x y
  obtain ⟨a, b, different⟩ := nontrivial
  exact different ((collapse a).trans (collapse b).symm)

def numeral (A : Frege.CombinatoryAlgebra D) : Nat → D
  | 0 => zero A
  | n + 1 => successor A (numeral A n)

/-- All standard finite K-iterates of I are pairwise distinct. -/
theorem numeral_injective (A : Frege.CombinatoryAlgebra D)
    (nontrivial : ∃ a b : D, a ≠ b) {m n : Nat}
    (h : numeral A m = numeral A n) : m = n := by
  induction m generalizing n with
  | zero =>
      cases n with
      | zero => rfl
      | succ n => exact False.elim (zero_not_successor A nontrivial (numeral A n) h)
  | succ m ih =>
      cases n with
      | zero => exact False.elim (zero_not_successor A nontrivial (numeral A m) h.symm)
      | succ n => exact congrArg Nat.succ (ih (successor_injective A h))

theorem distinct_numerals (A : Frege.CombinatoryAlgebra D)
    (nontrivial : ∃ a b : D, a ≠ b) {m n : Nat} (different : m ≠ n) :
    numeral A m ≠ numeral A n := fun h => different (numeral_injective A nontrivial h)

/-- Explicit arbitrarily large finite families, without a cardinality premise. -/
theorem arbitrarily_many_distinct_objects (A : Frege.CombinatoryAlgebra D)
    (nontrivial : ∃ a b : D, a ≠ b) (size : Nat) :
    ∃ f : Fin size → D, ∀ i j, f i = f j → i = j := by
  refine ⟨fun i => numeral A i.val, ?_⟩
  intro i j h
  exact Fin.ext (numeral_injective A nontrivial h)

def zeroTerm : Positive.Term :=
  .app (.app .constantS .constantK) .constantK

def successorTerm (term : Positive.Term) : Positive.Term := .app .constantK term

def unary (index : Nat) (term : Positive.Term) : Applicative.Formula :=
  .relation 0 index (fun _ => term)

/-- The displayed formula ∀X[(X(I) ∧ ∀y(X(y) → X(Ky))) → X(x)].
The sole free object variable is x at index zero; X is freshly bound. -/
def leastInductiveFormula : Applicative.Formula :=
  .forallPredicate 0
    (.implies
      (.conjunction (unary 0 zeroTerm)
        (.forallObject (.implies (unary 0 (.var 0))
          (unary 0 (successorTerm (.var 0))))))
      (unary 0 (.var 0)))

def modelZero (M : Positive.Interpretation D R) : D :=
  M.apply (M.apply M.constantS M.constantK) M.constantK

def modelSuccessor (M : Positive.Interpretation D R) (x : D) : D :=
  M.apply M.constantK x

def member (M : Positive.Interpretation D R) (P : R 0) (x : D) : Prop :=
  M.satisfies 0 P (fun _ => x)

def Inductive (M : Positive.Interpretation D R) (P : R 0) : Prop :=
  member M P (modelZero M) ∧
    ∀ x, member M P x → member M P (modelSuccessor M x)

def Least (M : Positive.Interpretation D R) (x : D) : Prop :=
  ∀ P : R 0, Inductive M P → member M P x

/-- The syntax has exactly the intended meaning, including the predicate binder. -/
theorem least_inductive_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    leastInductiveFormula.truth M objects predicates ↔ Least M (objects 0) := by
  simp only [leastInductiveFormula, Applicative.Formula.truth, unary,
    zeroTerm, successorTerm, Positive.Term.value, Positive.pushPredicate,
    Positive.pushObject, Least, Inductive, member, modelZero, modelSuccessor,
    dite_true]

def RepresentsLeast (M : Positive.Interpretation D R) (N : R 0) : Prop :=
  ∀ x, member M N x ↔ Least M x

/-- Only one actual comprehension instance, with all surrounding parameters fixed.
It is deliberately separate from positive comprehension. -/
def LeastComprehensionInstance (M : Positive.Interpretation D R)
    (parameters : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) : Prop :=
  ∃ N : R 0, ∀ x, member M N x ↔
    leastInductiveFormula.truth M (Positive.pushObject parameters x) predicates

theorem least_comprehension_instance_exact (M : Positive.Interpretation D R)
    (parameters : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    LeastComprehensionInstance M parameters predicates ↔ ∃ N, RepresentsLeast M N := by
  simp only [LeastComprehensionInstance, RepresentsLeast,
    least_inductive_formula_truth, Positive.pushObject]

theorem least_zero (M : Positive.Interpretation D R) : Least M (modelZero M) := by
  intro P closed
  exact closed.1

theorem least_successor (M : Positive.Interpretation D R) {x : D}
    (h : Least M x) : Least M (modelSuccessor M x) := by
  intro P closed
  exact closed.2 x (h P closed)

theorem represented_least_is_inductive (M : Positive.Interpretation D R)
    {N : R 0} (represents : RepresentsLeast M N) : Inductive M N := by
  constructor
  · exact (represents _).mpr (least_zero M)
  · intro x hx
    exact (represents _).mpr (least_successor M ((represents x).mp hx))

theorem represented_least_induction (M : Positive.Interpretation D R)
    {N : R 0} (represents : RepresentsLeast M N) {P : R 0}
    (closed : Inductive M P) {x : D} (natural : member M N x) : member M P x :=
  (represents x).mp natural P closed

/-- The exact new comprehension instance supplies a least inductive available relation. -/
theorem least_inductive_domain (M : Positive.Interpretation D R)
    (parameters : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R)
    (comprehension : LeastComprehensionInstance M parameters predicates) :
    ∃ N : R 0, RepresentsLeast M N ∧ Inductive M N ∧
      ∀ P : R 0, Inductive M P → ∀ x, member M N x → member M P x := by
  obtain ⟨N, represents⟩ :=
    (least_comprehension_instance_exact M parameters predicates).mp comprehension
  exact ⟨N, represents, represented_least_is_inductive M represents,
    fun _ closed _ natural => represented_least_induction M represents closed natural⟩

/-- This ordinary closure condition is already supplied by Part I's positive
comprehension. It is stated locally to keep this checkpoint independent. -/
def UnaryIntersection (M : Positive.Interpretation D R) : Prop :=
  ∀ P Q : R 0, ∃ H : R 0, ∀ x, member M H x ↔ member M P x ∧ member M Q x

/-- Induction with the usual step restricted to natural inputs, rather than all objects. -/
theorem relativised_relation_induction (M : Positive.Interpretation D R)
    (intersections : UnaryIntersection M) {N : R 0} (represents : RepresentsLeast M N)
    {P : R 0} (base : member M P (modelZero M))
    (step : ∀ x, member M N x → member M P x → member M P (modelSuccessor M x)) :
    ∀ x, member M N x → member M P x := by
  obtain ⟨H, describes⟩ := intersections N P
  have naturalInductive := represented_least_is_inductive M represents
  have hInductive : Inductive M H := by
    constructor
    · exact (describes _).mpr ⟨naturalInductive.1, base⟩
    · intro x hx
      obtain ⟨nx, px⟩ := (describes x).mp hx
      exact (describes _).mpr ⟨naturalInductive.2 x nx, step x nx px⟩
  intro x nx
  exact ((describes x).mp (represented_least_induction M represents hInductive nx)).2

/-- Any additionally represented formula inherits induction on the least domain.
Full classical comprehension would provide the displayed representation premise. -/
theorem represented_formula_induction (M : Positive.Interpretation D R)
    (intersections : UnaryIntersection M) {N : R 0} (represents : RepresentsLeast M N)
    (formula : Applicative.Formula) (parameters : Positive.ObjectAssignment D)
    (predicates : Positive.PredicateAssignment R)
    (formulaComprehension : ∃ P : R 0, ∀ x, member M P x ↔
      formula.truth M (Positive.pushObject parameters x) predicates)
    (base : formula.truth M (Positive.pushObject parameters (modelZero M)) predicates)
    (step : ∀ x, member M N x →
      formula.truth M (Positive.pushObject parameters x) predicates →
      formula.truth M (Positive.pushObject parameters (modelSuccessor M x)) predicates) :
    ∀ x, member M N x →
      formula.truth M (Positive.pushObject parameters x) predicates := by
  obtain ⟨P, describes⟩ := formulaComprehension
  intro x nx
  apply (describes x).mp
  apply relativised_relation_induction M intersections represents ((describes _).mpr base) ?_ x nx
  intro y ny py
  exact (describes _).mpr (step y ny ((describes y).mp py))

/-- Retain an arbitrary combinatory algebra and an arbitrary Henkin relation family. -/
def interpretation (A : Frege.CombinatoryAlgebra D)
    (satisfies : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop) :
    Positive.Interpretation D R where
  apply := A.apply
  constantK := A.constant
  constantS := A.distribute
  satisfies := satisfies

theorem numerals_belong_to_least (A : Frege.CombinatoryAlgebra D)
    (satisfies : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    {N : R 0} (represents : RepresentsLeast (interpretation A satisfies) N) (n : Nat) :
    member (interpretation A satisfies) N (numeral A n) := by
  have closed := represented_least_is_inductive (interpretation A satisfies) represents
  induction n with
  | zero => exact closed.1
  | succ n ih => exact closed.2 (numeral A n) ih

/-- A conditional Henkin-domain certificate with the exact additional closure
premises. This is not yet a certificate for all Z2 axioms. -/
theorem peano_domain_checkpoint (A : Frege.CombinatoryAlgebra D)
    (nontrivial : ∃ a b : D, a ≠ b)
    (satisfies : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (parameters : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R)
    (comprehension : LeastComprehensionInstance (interpretation A satisfies) parameters predicates)
    (intersections : UnaryIntersection (interpretation A satisfies)) :
    ∃ N : R 0,
      RepresentsLeast (interpretation A satisfies) N ∧
      member (interpretation A satisfies) N (zero A) ∧
      (∀ x, member (interpretation A satisfies) N x →
        member (interpretation A satisfies) N (successor A x)) ∧
      (∀ x, zero A ≠ successor A x) ∧
      (∀ x y, successor A x = successor A y → x = y) ∧
      (∀ P : R 0, member (interpretation A satisfies) P (zero A) →
        (∀ x, member (interpretation A satisfies) N x →
          member (interpretation A satisfies) P x →
          member (interpretation A satisfies) P (successor A x)) →
        ∀ x, member (interpretation A satisfies) N x →
          member (interpretation A satisfies) P x) := by
  obtain ⟨N, represents, closed, _⟩ :=
    least_inductive_domain (interpretation A satisfies) parameters predicates comprehension
  refine ⟨N, represents, closed.1, closed.2, zero_not_successor A nontrivial,
    fun _ _ h => successor_injective A h, ?_⟩
  intro P base step
  exact relativised_relation_induction (interpretation A satisfies)
    intersections represents base step

end FregeanECA.Part2.Arithmetic
