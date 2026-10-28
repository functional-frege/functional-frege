import FregeanECA.Representation
import Frege.BetaEtaSeparation

/-!
A semantic model of all five axioms of the new functional theory. Relation
domains contain every predicate, so A1 holds even without its positivity
restriction. A2 is checked for every finite applicative term, not just K and S.
The certificate does not formalise a proof calculus or its soundness theorem.
-/
namespace FregeanECA

open Frege
universe u

/-- Arguments use de Bruijn order: index zero is supplied last. Thus for two
arguments this is `(code env[1]) env[0]`. -/
def applyArguments {D : Type u} (A : CombinatoryAlgebra D) (code : D) :
    {n : Nat} → (Fin n → D) → D
  | 0, _ => code
  | n + 1, env => A.apply (applyArguments A code (fun i : Fin n => env i.succ)) (env 0)

/-- Repeated bracket abstraction produces an object representing a finite
applicative term. Coefficients are arbitrary object parameters. -/
def closeTerm {D : Type u} (A : CombinatoryAlgebra D) :
    {n : Nat} → CombinatorTerm D n → D
  | 0, t => CombinatorTerm.evaluate A id t Fin.elim0
  | _ + 1, t => closeTerm A t.abstractNewest

theorem closeTerm_spec {D : Type u} (A : CombinatoryAlgebra D)
    {n : Nat} (t : CombinatorTerm D n) (env : Fin n → D) :
    applyArguments A (closeTerm A t) env = CombinatorTerm.evaluate A id t env := by
  induction n with
  | zero =>
      have h : env = Fin.elim0 := by funext i; exact Fin.elim0 i
      subst env
      rfl
  | succ n ih =>
      simp only [closeTerm, applyArguments]
      rw [ih t.abstractNewest]
      rw [CombinatorTerm.applying_an_abstraction_substitutes_its_argument]
      congr 1
      funext i
      exact Fin.cases rfl (fun _ => rfl) i

/-- One function-sort element for each represented object function. This uses
a copy of D, rather than postulating that every set-theoretic map D → D exists
in the function sort. -/
def representedFunctions {D : Type u} (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) : Representation D D where
  eval := A.apply
  delta := id
  lawV := by
    intro a b
    constructor
    · intro h x
      exact congrArg (fun c => A.apply c x) h
    · exact ext a b
  coverage := fun a => ⟨a, rfl⟩

theorem represented_application {D : Type u} (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) (a b : D) :
    (representedFunctions A ext).app a b = A.apply a b :=
  (representedFunctions A ext).application_of_representative a b

/-- A semantic certificate for A1--A5. Relation n has arity n+1. A2 is written
with `delta f` applied to all arguments; A3--A4 make its first application
exactly `eval f`, by `Representation.application_of_representative`. The term
grammar also permits K and S, so this clause includes every term required by A2.
-/
structure FregeanModel where
  Object : Type u
  Function : Type u
  Relation : Nat → Type u
  algebra : CombinatoryAlgebra Object
  representation : Representation Object Function
  application_agrees : ∀ a b, representation.app a b = algebra.apply a b
  holds : {n : Nat} → Relation n → (Fin (n + 1) → Object) → Prop
  relational_comprehension : ∀ n (p : (Fin (n + 1) → Object) → Prop),
    ∃ R : Relation n, ∀ xs, holds R xs ↔ p xs
  functional_comprehension : ∀ n (t : CombinatorTerm Object (n + 1)),
    ∃ f : Function, ∀ env,
      applyArguments algebra (representation.delta f) env =
        CombinatorTerm.evaluate algebra id t env
  nontrivial : ∃ a b : Object, a ≠ b

/-- The powerset relation expansion of an arbitrary nontrivial extensional
combinatory algebra. A3 and A4 are fields of `representation`; A1, A2 and A5
are separately discharged below. -/
noncomputable def fullModel {D : Type u} (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) (nt : ∃ a b : D, a ≠ b) : FregeanModel.{u} where
  Object := D
  Function := D
  Relation n := (Fin (n + 1) → D) → Prop
  algebra := A
  representation := representedFunctions A ext
  application_agrees := represented_application A ext
  holds := fun R xs => R xs
  relational_comprehension := fun _ p => ⟨p, fun _ => Iff.rfl⟩
  functional_comprehension := by
    intro n t
    exact ⟨closeTerm A t, closeTerm_spec A t⟩
  nontrivial := nt

/-- The explicit open beta-eta term algebra supplies the object domain; no
model-existence or consistency premise is assumed. -/
noncomputable def openTermModel : FregeanModel.{0} :=
  fullModel OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional
    ⟨OpenLambda.termClass (.coeff 0), OpenLambda.termClass (.coeff 1),
      OpenLambda.the_constructed_extensional_algebra_is_nontrivial⟩

theorem a_fregean_model_exists : Nonempty FregeanModel.{0} := ⟨openTermModel⟩

/-- Duplicate every represented function while keeping the same object
application and full relation domains. All of A1--A5 still hold. -/
noncomputable def duplicateFullModel {D : Type u} (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) (nt : ∃ a b : D, a ≠ b) : FregeanModel.{u} where
  Object := D
  Function := D × Bool
  Relation n := (Fin (n + 1) → D) → Prop
  algebra := A
  representation := duplicateRepresentation A ext
  application_agrees := by
    intro a b
    exact (duplicateRepresentation A ext).application_of_representative (a, false) b
  holds := fun R xs => R xs
  relational_comprehension := fun _ p => ⟨p, fun _ => Iff.rfl⟩
  functional_comprehension := by
    intro n t
    exact ⟨(closeTerm A t, false), closeTerm_spec A t⟩
  nontrivial := nt

theorem a_fregean_model_without_function_extensionality_exists :
    ∃ M : FregeanModel.{0}, ¬ M.representation.FunctionExtensionality := by
  refine ⟨duplicateFullModel OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional
    ⟨OpenLambda.termClass (.coeff 0), OpenLambda.termClass (.coeff 1),
      OpenLambda.the_constructed_extensional_algebra_is_nontrivial⟩, ?_⟩
  exact duplicateRepresentation_not_extensional OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional

end FregeanECA
