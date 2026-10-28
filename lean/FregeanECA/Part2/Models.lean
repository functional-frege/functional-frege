import FregeanECA.Part2.Closure
import FregeanECA.Concrete
import FregeanECA.ActualFE

/-!
Part II's full classical comprehension has explicit powerset models. These
certificates quantify over the actual formula grammars, including identity of
relation and function representatives. They do not change computational A2.
The new comprehension schema has not here been encoded in Foundation's proof
calculus; these are semantic model certificates, not syntactic consistency
theorems for the strengthened theories.
-/

namespace FregeanECA.Part2
open Frege
universe u v w

/-- Full A1 in the entire functional language, with all parameters and all
object, function and relation quantifiers admitted. -/
structure HasFullFunctionalComprehension {D : Type u} {F : Type v}
    {R : Nat → Type w} (model : Functional.Interpretation D F R) : Prop where
  relations_nonempty : ∀ arity, Nonempty (R arity)
  comprehend : ∀ (arity : Nat) (formula : Functional.Formula)
    (parameters : Positive.ObjectAssignment D) (functions : Nat → F)
    (predicates : Positive.PredicateAssignment R),
    ∃ relation : R arity, ∀ arguments,
      model.applicative.satisfies arity relation arguments ↔
        formula.truth model (Positive.assignTuple (arity + 1) arguments parameters)
          functions predicates

/-- The Part I specification axioms together with full classical relational
comprehension. B1--B5 remain valid but are not claimed sufficient alone. -/
structure FullTSConditions {D : Type u} {R : Nat → Type v}
    (model : Positive.Interpretation D R) : Prop extends TSConditions model where
  full_comprehension : HasFullComprehension model

/-- The Part I functional axioms with A1 strengthened. In particular A2 still
represents only finite applicative terms. -/
structure FullTFConditions {D : Type u} {F : Type v} {R : Nat → Type w}
    (model : Functional.Interpretation D F R) : Prop extends TFConditions model where
  full_comprehension : HasFullFunctionalComprehension model

theorem fullRelations_comprehend_all_formulas {D : Type u}
    (A : CombinatoryAlgebra D) : HasFullComprehension (fullRelations A) where
  relations_nonempty := fun _ => ⟨fun _ => False⟩
  comprehend := fun n formula parameters predicates =>
    ⟨fun arguments => formula.truth (fullRelations A)
        (Positive.assignTuple (n + 1) arguments parameters) predicates,
      fun _ => Iff.rfl⟩

theorem copyExpansion_comprehends_all_functional_formulas {D : Type u}
    (A : CombinatoryAlgebra D) :
    HasFullFunctionalComprehension (copyExpansion (fullRelations A)) where
  relations_nonempty := fun _ => ⟨fun _ => False⟩
  comprehend := fun n formula parameters functions predicates =>
    ⟨fun arguments => formula.truth (copyExpansion (fullRelations A))
        (Positive.assignTuple (n + 1) arguments parameters) functions predicates,
      fun _ => Iff.rfl⟩

theorem duplicateExpansion_comprehends_all_functional_formulas {D : Type u}
    (A : CombinatoryAlgebra D) :
    HasFullFunctionalComprehension (duplicateExpansion A) where
  relations_nonempty := fun _ => ⟨fun _ => False⟩
  comprehend := fun n formula parameters functions predicates =>
    ⟨fun arguments => formula.truth (duplicateExpansion A)
        (Positive.assignTuple (n + 1) arguments parameters) functions predicates,
      fun _ => Iff.rfl⟩

theorem fullRelations_satisfies_full_TS {D : Type u}
    (A : CombinatoryAlgebra D) (ext : A.IsExtensional) (nt : ∃ a b : D, a ≠ b) :
    FullTSConditions (fullRelations A) where
  toTSConditions := fullRelations_satisfies_TS A ext nt
  full_comprehension := fullRelations_comprehend_all_formulas A

theorem copyExpansion_satisfies_full_TF {D : Type u}
    (A : CombinatoryAlgebra D) (ext : A.IsExtensional) (nt : ∃ a b : D, a ≠ b) :
    FullTFConditions (copyExpansion (fullRelations A)) where
  toTFConditions := fullRelations_satisfies_TF A ext nt
  full_comprehension := copyExpansion_comprehends_all_functional_formulas A

theorem duplicateExpansion_satisfies_full_TF {D : Type u}
    (A : CombinatoryAlgebra D) (ext : A.IsExtensional) (nt : ∃ a b : D, a ≠ b) :
    FullTFConditions (duplicateExpansion A) where
  toTFConditions := duplicateExpansion_satisfies_TF A ext nt
  full_comprehension := duplicateExpansion_comprehends_all_functional_formulas A

/-- No model-existence or consistency premise: the checked open beta-eta term
algebra supplies the nontrivial ECA. -/
theorem openSpecification_satisfies_full_TS : FullTSConditions openSpecification :=
  fullRelations_satisfies_full_TS OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional open_nontrivial

theorem openFunctional_satisfies_full_TF : FullTFConditions openFunctional :=
  copyExpansion_satisfies_full_TF OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional open_nontrivial

theorem openDuplicate_satisfies_full_TF : FullTFConditions openDuplicate :=
  duplicateExpansion_satisfies_full_TF OpenLambda.algebra
    OpenLambda.the_constructed_open_term_algebra_is_extensional open_nontrivial

/-- Full classical functional-language comprehension does not force FE. -/
theorem full_comprehension_has_a_model_without_FE :
    FullTFConditions openDuplicate ∧
      ¬ Axioms.Valid openDuplicate Axioms.functionExtensionality :=
  ⟨openDuplicate_satisfies_full_TF, Axioms.openDuplicate_FE_is_not_valid⟩

/-- The exact unsafe strengthening: no fixed result value can turn every
available unary relation into a represented native characteristic test.
Only one actual full-comprehension instance is used in the diagonal. -/
theorem full_comprehension_excludes_unrestricted_predicate_representation
    {D : Type u} {R : Nat → Type v} (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) (a : D) :
    ¬ (∀ relation : R 0, ∃ code : D, ∀ x : D,
      M.satisfies 0 relation (fun _ => x) ↔ M.apply code x = a) := by
  classical
  intro represents
  let predicates : Positive.PredicateAssignment R :=
    fun n _ => Classical.choice (full.relations_nonempty n)
  let formula : Applicative.Formula := .implies
    (.equal (.app (.var 0) (.var 0)) (.var 1)) .falsum
  obtain ⟨relation, diagonal⟩ := full.comprehend 0 formula (fun _ => a) predicates
  obtain ⟨code, characteristic⟩ := represents relation
  have instanceLaw := diagonal (fun _ => code)
  change M.satisfies 0 relation (fun _ => code) ↔ (M.apply code code = a → False)
    at instanceLaw
  have impossible : (M.apply code code = a) ↔ ¬ (M.apply code code = a) :=
    (characteristic code).symm.trans instanceLaw
  by_cases same : M.apply code code = a
  · exact impossible.mp same same
  · exact same (impossible.mpr same)

end FregeanECA.Part2
