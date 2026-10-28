import FregeanECA.Comprehension

/-! A generic source language for Frege Arithmetic. Its only primitive
object-valued operation is number abstraction on unary predicates. The
comprehension contract ranges over the actual source grammar, including
number terms and nested relation quantifiers. No ECA, Peano domain, standard
Nat identification, or arithmetic interpretation is assumed. Relation
coextension is expressible by formulas; representative identity is a logical
atom, without an axiom identifying coextensive representatives. The standard
Frege theorem below does not use that extra atom. Indices n denote relation
arities n+1. -/

namespace FregeanECA.Part2.FregeArithmetic
open Positive
universe u v

structure Interpretation (D : Type u) (R : Nat → Type v) where
  satisfies : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop
  number : R 0 → D

inductive Term where
  | var (index : Nat)
  | number (predicateIndex : Nat)

def Term.value {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) : Term → D
  | .var i => objects i
  | .number i => M.number (predicates 0 i)

inductive Formula where
  | equal (left right : Term)
  | relation (arity index : Nat) (arguments : Fin (arity + 1) → Term)
  | relationEqual (arity left right : Nat)
  | falsum
  | implies (left right : Formula)
  | conjunction (left right : Formula)
  | disjunction (left right : Formula)
  | existsObject (body : Formula)
  | forallObject (body : Formula)
  | existsPredicate (arity : Nat) (body : Formula)
  | forallPredicate (arity : Nat) (body : Formula)

def Formula.truth {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) : Formula → Prop
  | .equal s t => s.value M objects predicates = t.value M objects predicates
  | .relation arity index arguments => M.satisfies arity (predicates arity index)
      (fun i => (arguments i).value M objects predicates)
  | .relationEqual arity left right => predicates arity left = predicates arity right
  | .falsum => False
  | .implies p q => p.truth M objects predicates → q.truth M objects predicates
  | .conjunction p q => p.truth M objects predicates ∧ q.truth M objects predicates
  | .disjunction p q => p.truth M objects predicates ∨ q.truth M objects predicates
  | .existsObject p => ∃ x, p.truth M (pushObject objects x) predicates
  | .forallObject p => ∀ x, p.truth M (pushObject objects x) predicates
  | .existsPredicate arity p => ∃ P, p.truth M objects (pushPredicate predicates arity P)
  | .forallPredicate arity p => ∀ P, p.truth M objects (pushPredicate predicates arity P)

structure HasFullComprehension {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) : Prop where
  relations_nonempty : ∀ arity, Nonempty (R arity)
  comprehend : ∀ (arity : Nat) (formula : Formula)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R),
    ∃ relation : R arity, ∀ arguments,
      M.satisfies arity relation arguments ↔
        formula.truth M (assignTuple (arity + 1) arguments objects) predicates

def pair {D : Type u} (x y : D) : Fin 2 → D := Fin.cases x (fun _ => y)

@[simp] theorem pair_zero {D : Type u} (x y : D) : pair x y 0 = x := rfl
@[simp] theorem pair_one {D : Type u} (x y : D) : pair x y 1 = y := rfl

def member {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) (P : R 0) (x : D) : Prop :=
  M.satisfies 0 P (fun _ => x)

def member2 {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) (G : R 1) (x y : D) : Prop :=
  M.satisfies 1 G (pair x y)

structure GraphBijection {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) (A B : D → Prop) (G : R 1) : Prop where
  support : ∀ x y, member2 M G x y → A x ∧ B y
  total : ∀ x, A x → ∃ y, member2 M G x y
  onto : ∀ y, B y → ∃ x, member2 M G x y
  functional : ∀ x y z, member2 M G x y → member2 M G x z → y = z
  injective : ∀ x y z, member2 M G x z → member2 M G y z → x = y

def Equinumerous {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) (P Q : R 0) : Prop :=
  ∃ G : R 1, GraphBijection M (member M P) (member M Q) G

def HumePrinciple {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) : Prop :=
  ∀ P Q : R 0, M.number P = M.number Q ↔ Equinumerous M P Q

structure FullConditions {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) : Prop where
  comprehension : HasFullComprehension M
  hume : HumePrinciple M

def unary (index : Nat) (t : Term) : Formula := .relation 0 index (fun _ => t)
def binary (index : Nat) (s t : Term) : Formula := .relation 1 index (pair s t)
def iffFormula (p q : Formula) : Formula := .conjunction (.implies p q) (.implies q p)
def notFormula (p : Formula) : Formula := .implies p .falsum

theorem binary_truth {D : Type u} {R : Nat → Type v}
    (M : Interpretation D R) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) (i : Nat) (s t : Term) :
    (binary i s t).truth M objects predicates ↔
      member2 M (predicates 1 i) (s.value M objects predicates) (t.value M objects predicates) := by
  have values : (fun j => (pair s t j).value M objects predicates) =
      pair (s.value M objects predicates) (t.value M objects predicates) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp only [binary, Formula.truth, values, member2]

end FregeanECA.Part2.FregeArithmetic
