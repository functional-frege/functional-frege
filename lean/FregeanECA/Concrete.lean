import FregeanECA.Equivalence

namespace FregeanECA
open Frege
universe u

def fullRelations {D : Type u} (A : CombinatoryAlgebra D) :
    Positive.Interpretation D (fun n => (Fin (n+1) → D) → Prop) where
  apply := A.apply
  constantK := A.constant
  constantS := A.distribute
  satisfies := fun _ P xs => P xs

theorem fullRelations_closure {D : Type u} (A : CombinatoryAlgebra D) :
    Positive.PositiveClosure (fullRelations A) where
  equality := ⟨fun xs => xs 0 = xs 1, fun _ => Iff.rfl⟩
  preimage := fun source target P programs =>
    ⟨fun xs => P (fun i => Positive.applyArguments (fullRelations A) (programs i) xs), fun _ => Iff.rfl⟩
  intersection := fun _ P Q => ⟨fun xs => P xs ∧ Q xs, fun _ => Iff.rfl⟩
  union := fun _ P Q => ⟨fun xs => P xs ∨ Q xs, fun _ => Iff.rfl⟩
  existsProjection := fun _ P => ⟨fun xs => ∃ y, P (Positive.appendLast xs y), fun _ => Iff.rfl⟩
  forallProjection := fun _ P => ⟨fun xs => ∀ y, P (Positive.appendLast xs y), fun _ => Iff.rfl⟩

theorem fullRelations_satisfies_TS {D : Type u} (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) (nt : ∃ a b : D, a ≠ b) : TSConditions (fullRelations A) where
  combinatory := ⟨A.constant_returns_first_argument, A.distribute_applies_the_same_argument⟩
  extensional := ext
  nontrivial := nt
  closure := fullRelations_closure A

theorem fullRelations_satisfies_TF {D : Type u} (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) (nt : ∃ a b : D, a ≠ b) :
    TFConditions (copyExpansion (fullRelations A)) :=
  ts_expansion_satisfies_tf (fullRelations_satisfies_TS A ext nt)

def duplicateExpansion {D : Type u} (A : CombinatoryAlgebra D) :
    Functional.Interpretation D (D × Bool) (fun n => (Fin (n+1) → D) → Prop) where
  applicative := fullRelations A
  eval := fun f x => A.apply f.1 x
  delta := Prod.fst

theorem duplicateExpansion_satisfies_TF {D : Type u} (A : CombinatoryAlgebra D)
    (ext : A.IsExtensional) (nt : ∃ a b : D, a ≠ b) :
    TFConditions (duplicateExpansion A) where
  comprehension := {
    relations_nonempty := fun _ => ⟨fun _ => False⟩
    comprehend := fun n p o f r =>
      ⟨fun xs => p.truth (duplicateExpansion A) (Positive.assignTuple (n+1) xs o) f r, fun _ => Iff.rfl⟩ }
  functional_comprehension := by
    intro n t o
    obtain ⟨a, ha⟩ := Positive.terms_have_codes (fullRelations A)
      ⟨A.constant_returns_first_argument, A.distribute_applies_the_same_argument⟩ (n+1) o t
    exact ⟨(a,false),ha⟩
  lawV := fun f g => ⟨fun h x => congrArg (fun a => A.apply a x) h, ext f.1 g.1⟩
  coverage := fun a => ⟨(a,false),rfl⟩
  nontrivial := nt
  evaluation := fun _ _ => rfl
  combinatory := ⟨A.constant_returns_first_argument, A.distribute_applies_the_same_argument⟩

abbrev OpenObject := OpenLambda.Element
abbrev OpenRelation (n : Nat) := (Fin (n+1) → OpenObject) → Prop

def openSpecification : Positive.Interpretation OpenObject OpenRelation :=
  fullRelations OpenLambda.algebra
def openFunctional : Functional.Interpretation OpenObject OpenObject OpenRelation :=
  copyExpansion openSpecification
def openDuplicate : Functional.Interpretation OpenObject (OpenObject × Bool) OpenRelation :=
  duplicateExpansion OpenLambda.algebra

theorem open_nontrivial : ∃ a b : OpenObject, a ≠ b :=
  ⟨OpenLambda.termClass (.coeff 0), OpenLambda.termClass (.coeff 1),
    OpenLambda.the_constructed_extensional_algebra_is_nontrivial⟩

theorem openSpecification_satisfies_TS : TSConditions openSpecification :=
  fullRelations_satisfies_TS OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional open_nontrivial

theorem openFunctional_satisfies_TF : TFConditions openFunctional :=
  ts_expansion_satisfies_tf openSpecification_satisfies_TS

theorem openDuplicate_satisfies_TF : TFConditions openDuplicate :=
  duplicateExpansion_satisfies_TF OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional open_nontrivial

end FregeanECA
