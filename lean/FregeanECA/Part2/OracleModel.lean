import FregeanECA.Part2.OracleAssignments
import FregeanECA.Part2.DefinableRelations
import FregeanECA.Part2.NaturalECA

/-! A concrete natural-number ECA with first-order-definable relations.
The auxiliary primitive operation graph evaluates one primitive symbol only;
it is not an evaluator for arbitrary formulas or even arbitrary terms.
-/
namespace FregeanECA.Part2.Oracle
open FFL FFL.FirstOrder

instance : Language.Eq language := ⟨0⟩

noncomputable def withApplication
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat) :
    ∀ n, Nat → (Fin n → Nat) → Nat := fun n symbol values =>
  if h : n = 2 ∧ symbol = 1 then
    NaturalECA.algebra.apply (values ⟨0, by omega⟩) (values ⟨1, by omega⟩)
  else operations n symbol values

noncomputable def modelOperations
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat) :=
  withLookup (withApplication operations)

noncomputable def primitiveValue
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat)
    (arity symbol : Nat) (arguments : Fin arity → Nat) : Nat :=
  @Structure.func language Nat
    (interpretation (modelOperations operations) (fun _ _ _ => False))
    arity symbol arguments

def primitiveGraph
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat)
    (arity symbol code value : Nat) : Prop :=
  ∃ arguments : Fin arity → Nat,
    assignmentCode arguments = code ∧ primitiveValue operations arity symbol arguments = value

def modelPredicates (operations : ∀ n, Nat → (Fin n → Nat) → Nat) :
    ∀ n, Nat → (Fin n → Nat) → Prop := fun n symbol values =>
  if h : n = 2 ∧ symbol = 0 then
    values ⟨0, by omega⟩ = values ⟨1, by omega⟩
  else if h : n = 4 ∧ symbol = 0 then
    primitiveGraph operations (values ⟨0, by omega⟩) (values ⟨1, by omega⟩)
      (values ⟨2, by omega⟩) (values ⟨3, by omega⟩)
  else False

@[instance_reducible] noncomputable def modelStructure
    (operations : ∀ n, Nat → (Fin n → Nat) → Nat) : Structure language Nat :=
  interpretation (modelOperations operations) (modelPredicates operations)

theorem model_equality (operations) :
    letI := modelStructure operations
    Structure.Eq language Nat := by
  letI := modelStructure operations
  exact ⟨fun _ _ => Iff.rfl⟩

def applicationTerm (f x : Semiterm language ξ n) : Semiterm language ξ n :=
  .func (arity := 2) 1 ![f, x]

theorem applicationTerm_value (operations) (f x : Semiterm language ξ n)
    (bound : Fin n → Nat) (free : ξ → Nat) :
    (applicationTerm f x).val (s := modelStructure operations) bound free =
      NaturalECA.algebra.apply (f.val (s := modelStructure operations) bound free)
        (x.val (s := modelStructure operations) bound free) := by
  rfl

theorem application_definable (operations) :
    letI := modelStructure operations
    language.DefinableFunction₂ NaturalECA.algebra.apply := by
  letI := modelStructure operations
  letI := model_equality operations
  refine ⟨“x y z. x = !!(applicationTerm (.bvar 1) (.bvar 2))”, ?_⟩
  intro values
  simp [applicationTerm_value]

noncomputable def definableModel (operations) :=
  @FirstOrderRelations.interpretation language Nat (modelStructure operations) NaturalECA.algebra

/-- This is an actual nontrivial model, with all other auxiliary operations
still free to be instantiated by finite-syntax selectors. -/
theorem definable_model_satisfies_B_and_C (operations) :
    TSConditions (definableModel operations) ∧ ComplementClosure (definableModel operations) := by
  letI := modelStructure operations
  letI := model_equality operations
  letI := application_definable operations
  exact FirstOrderRelations.specification_with_complements NaturalECA.algebra
    NaturalECA.extensional NaturalECA.nontrivial

theorem definable_model_has_no_truth_relation (operations) :
    ¬ ∃ relation : @FirstOrderRelations.Relation language Nat (modelStructure operations) 0,
      ∀ code, relation.val (fun _ => code) ↔
        sentenceTruth (modelOperations operations) (modelPredicates operations) code := by
  letI := modelStructure operations
  rintro ⟨relation, correct⟩
  apply no_definable_truth (modelOperations operations) (modelPredicates operations)
  apply Language.Definable.of_iff relation.property
  intro values
  have equal : (fun _ : Fin 1 => values 0) = values := by
    funext i
    have : i = 0 := Fin.eq_zero i
    subst i
    rfl
  simpa only [equal] using (correct (values 0)).symm

/-- Correctness on actual sentence codes already contradicts diagonalisation;
no requirement is imposed on junk or noncanonical codes. -/
theorem no_relation_correct_on_sentence_codes (operations) :
    ¬ ∃ relation : @FirstOrderRelations.Relation language Nat (modelStructure operations) 0,
      ∀ sentence : Sentence language,
        relation.val (fun _ => Encodable.encode sentence) ↔
          sentence.Evalb (s := modelStructure operations) Fin.elim0 := by
  letI := modelStructure operations
  rintro ⟨relation, correct⟩
  obtain ⟨formula, defines⟩ := relation.property
  apply no_truth_formula (modelOperations operations) (modelPredicates operations)
  refine ⟨closeParameters formula, fun sentence => ?_⟩
  rw [closeParameters_truth]
  exact (correct sentence).symm.trans
    (defines (fun _ => Encodable.encode sentence)).symm

theorem primitiveGraph_assignmentCode (operations) (arity symbol : Nat)
    (arguments : Fin arity → Nat) (value : Nat) :
    primitiveGraph operations arity symbol (assignmentCode arguments) value ↔
      primitiveValue operations arity symbol arguments = value := by
  constructor
  · rintro ⟨other, sameCode, correct⟩
    have same : other = arguments := by
      funext i
      have equal := congrArg (fun code => lookupCode code i.val) sameCode
      simpa only [lookupCode_assignmentCode] using equal
    simpa only [same] using correct
  · intro correct
    exact ⟨arguments, rfl, correct⟩

theorem model_primitiveValue (operations) (arity symbol : Nat)
    (arguments : Fin arity → Nat) :
    @Structure.func language Nat (modelStructure operations) arity symbol arguments =
      primitiveValue operations arity symbol arguments := rfl

theorem modelPredicates_equality (operations) (arguments : Fin 2 → Nat) :
    modelPredicates operations 2 0 arguments ↔ arguments 0 = arguments 1 := by
  simp [modelPredicates]

theorem modelPredicates_primitiveGraph (operations) (arguments : Fin 4 → Nat) :
    modelPredicates operations 4 0 arguments ↔
      primitiveGraph operations (arguments 0) (arguments 1) (arguments 2) (arguments 3) := by
  simp [modelPredicates]

end FregeanECA.Part2.Oracle
