import FregeanECA.Part2.OracleFiniteSyntax
import FregeanECA.Part2.OracleModel

/-! Finite compositional satisfaction tables. The witnesses below are actual
first-order formulas (finite disjunctions of substitution instances), not a
uniform truth predicate. The uniform first-order matrix is constructed in the
next module. -/
namespace FregeanECA.Part2.Oracle

open FFL FFL.FirstOrder

abbrev Operations := ∀ n, Nat → (Fin n → Nat) → Nat
abbrev TruthTable := Nat → Nat → Prop
abbrev ValueTable := Nat → Nat → Nat → Prop

noncomputable def termValue (operations : Operations) (term : ClosedSemiterm language n)
    (environment : Nat) : Nat :=
  term.val (s := modelStructure operations) (fun i => lookupCode environment i.val) Empty.elim

def formulaTruth (operations : Operations) (formula : Semisentence language n)
    (environment : Nat) : Prop :=
  formula.Evalb (s := modelStructure operations) (fun i => lookupCode environment i.val)

def termClause (operations : Operations) (table : ValueTable)
    (term : ClosedSemiterm language n) (environment value : Nat) : Prop :=
  match term with
  | .bvar i => value = lookupCode environment i.val
  | .fvar impossible => nomatch impossible
  | .func symbol arguments =>
      ∃ values, (∀ i, table (termCode (arguments i)) environment (values i)) ∧
        value = primitiveValue operations _ symbol values

def formulaClause (operations : Operations) (truth : TruthTable) (values : ValueTable)
    (formula : Semisentence language n) (environment : Nat) : Prop :=
  match formula with
  | .verum => True
  | .falsum => False
  | .rel symbol arguments =>
      ∃ actual, (∀ i, values (termCode (arguments i)) environment (actual i)) ∧
        modelPredicates operations _ symbol actual
  | .nrel symbol arguments =>
      ¬ ∃ actual, (∀ i, values (termCode (arguments i)) environment (actual i)) ∧
        modelPredicates operations _ symbol actual
  | .and left right => truth (formulaCode left) environment ∧ truth (formulaCode right) environment
  | .or left right => truth (formulaCode left) environment ∨ truth (formulaCode right) environment
  | .all body => ∀ value, truth (formulaCode body) (pushAssignment value environment)
  | .exs body => ∃ value, truth (formulaCode body) (pushAssignment value environment)

def CorrectTermTable (operations : Operations) (root : Semisentence language n)
    (values : ValueTable) : Prop :=
  ∀ node ∈ formulaTermParts root, ∀ environment value,
    values (Encodable.encode node) environment value ↔
      termClause operations values node.2 environment value

def CorrectFormulaTable (operations : Operations) (root : Semisentence language n)
    (truth : TruthTable) (values : ValueTable) : Prop :=
  ∀ node ∈ formulaParts root, ∀ environment,
    truth (Encodable.encode node) environment ↔
      formulaClause operations truth values node.2 environment

theorem termClause_truth (operations : Operations) (values : ValueTable)
    (term : ClosedSemiterm language n) (environment value : Nat)
    (children : ∀ node ∈ termParts term, ∀ output,
      values (Encodable.encode node) environment output ↔ output = termValue operations node.2 environment) :
    termClause operations values term environment value ↔ value = termValue operations term environment := by
  cases term with
  | bvar i => rfl
  | fvar impossible => exact impossible.elim
  | func symbol arguments =>
      change (∃ actual, (∀ i, values (termCode (arguments i)) environment (actual i)) ∧
        value = primitiveValue operations _ symbol actual) ↔ _
      have hc : ∀ i output, values (termCode (arguments i)) environment output ↔
          output = termValue operations (arguments i) environment := by
        intro i output
        exact children _ (termParts_argument_subset symbol arguments i (term_mem_parts _)) output
      constructor
      · rintro ⟨actual, ha, hv⟩
        have he : actual = fun i => termValue operations (arguments i) environment :=
          funext fun i => (hc i _).mp (ha i)
        subst actual
        exact hv
      · intro hv
        exact ⟨_, fun i => (hc i _).mpr rfl, hv⟩

theorem correct_term_table_truth (operations : Operations) (root : Semisentence language n)
    (values : ValueTable) (correct : CorrectTermTable operations root values)
    (term : ClosedSemiterm language k) (member : (⟨k,term⟩ : TermNode) ∈ formulaTermParts root)
    (environment value : Nat) :
    values (termCode term) environment value ↔ value = termValue operations term environment := by
  induction term generalizing value with
  | bvar i => exact correct _ member _ _
  | fvar impossible => exact impossible.elim
  | func symbol arguments ih =>
      rw [show values (termCode (.func symbol arguments)) environment value ↔
        termClause operations values (.func symbol arguments) environment value from correct _ member _ _]
      change (∃ actual, (∀ i, values (termCode (arguments i)) environment (actual i)) ∧
        value = primitiveValue operations _ symbol actual) ↔ _
      have hc : ∀ i output, values (termCode (arguments i)) environment output ↔
          output = termValue operations (arguments i) environment := by
        intro i output
        exact ih i (formulaTermParts_subterm member
          (termParts_argument_subset symbol arguments i (term_mem_parts _))) output
      constructor
      · rintro ⟨actual, ha, hv⟩
        have he : actual = fun i => termValue operations (arguments i) environment :=
          funext fun i => (hc i _).mp (ha i)
        subst actual
        exact hv
      · intro hv
        exact ⟨_, fun i => (hc i _).mpr rfl, hv⟩

theorem lookup_push_vector (value environment : Nat) :
    (fun i : Fin (n+1) => lookupCode (pushAssignment value environment) i.val) =
      Matrix.vecCons value (fun i : Fin n => lookupCode environment i.val) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem formulaClause_truth (operations : Operations) (truth : TruthTable) (values : ValueTable)
    (formula : Semisentence language n) (environment : Nat)
    (formulas : ∀ node ∈ formulaParts formula, ∀ code,
      truth (Encodable.encode node) code ↔ formulaTruth operations node.2 code)
    (terms : ∀ node ∈ formulaTermParts formula, ∀ output,
      values (Encodable.encode node) environment output ↔ output = termValue operations node.2 environment) :
    formulaClause operations truth values formula environment ↔ formulaTruth operations formula environment := by
  have atomic : ∀ {arity} (symbol : language.Rel arity)
      (arguments : Fin arity → ClosedSemiterm language n)
      (h : ∀ i, (⟨n,arguments i⟩ : TermNode) ∈ formulaTermParts formula),
      (∃ actual, (∀ i, values (termCode (arguments i)) environment (actual i)) ∧
        modelPredicates operations _ symbol actual) ↔
      modelPredicates operations _ symbol (fun i => termValue operations (arguments i) environment) := by
    intro arity symbol arguments h
    constructor
    · rintro ⟨actual, ha, hp⟩
      have he : actual = fun i => termValue operations (arguments i) environment :=
        funext fun i => (terms _ (h i) _).mp (ha i)
      simpa [he] using hp
    · intro hp
      exact ⟨_, fun i => (terms _ (h i) _).mpr rfl, hp⟩
  cases formula with
  | verum => rfl
  | falsum => rfl
  | rel symbol arguments =>
      apply atomic symbol arguments
      intro i
      simp only [formulaTermParts, List.mem_flatten, List.mem_ofFn]
      exact ⟨termParts (arguments i), ⟨i,rfl⟩, term_mem_parts _⟩
  | nrel symbol arguments =>
      apply not_congr (atomic symbol arguments ?_)
      intro i
      simp only [formulaTermParts, List.mem_flatten, List.mem_ofFn]
      exact ⟨termParts (arguments i), ⟨i,rfl⟩, term_mem_parts _⟩
  | and left right =>
      exact and_congr (formulas _ (by simp [formulaParts]) _) (formulas _ (by simp [formulaParts]) _)
  | or left right =>
      exact or_congr (formulas _ (by simp [formulaParts]) _) (formulas _ (by simp [formulaParts]) _)
  | all body =>
      change (∀ value, truth (formulaCode body) (pushAssignment value environment)) ↔ _
      simp only [formulaTruth, Semiformula.Evalb, Semiformula.eval_all]
      apply forall_congr'
      intro value
      change truth (formulaCode body) (pushAssignment value environment) ↔
        body.Evalb (s := modelStructure operations)
          (Matrix.vecCons value (fun i => lookupCode environment i.val))
      rw [← lookup_push_vector]
      exact formulas ⟨_,body⟩ (by simp [formulaParts]) (pushAssignment value environment)
  | exs body =>
      change (∃ value, truth (formulaCode body) (pushAssignment value environment)) ↔ _
      simp only [formulaTruth, Semiformula.Evalb, Semiformula.eval_ex]
      apply exists_congr
      intro value
      change truth (formulaCode body) (pushAssignment value environment) ↔
        body.Evalb (s := modelStructure operations)
          (Matrix.vecCons value (fun i => lookupCode environment i.val))
      rw [← lookup_push_vector]
      exact formulas ⟨_,body⟩ (by simp [formulaParts]) (pushAssignment value environment)

theorem correct_formula_table_truth (operations : Operations) (root : Semisentence language n)
    (truth : TruthTable) (values : ValueTable)
    (valueCorrect : CorrectTermTable operations root values)
    (truthCorrect : CorrectFormulaTable operations root truth values)
    (formula : Semisentence language k) (member : (⟨k,formula⟩ : FormulaNode) ∈ formulaParts root)
    (environment : Nat) :
    truth (formulaCode formula) environment ↔ formulaTruth operations formula environment := by
  induction formula generalizing environment with
  | verum => exact truthCorrect _ member _
  | falsum => exact truthCorrect _ member _
  | rel symbol arguments | nrel symbol arguments =>
      have hc : ∀ i output, values (termCode (arguments i)) environment output ↔
          output = termValue operations (arguments i) environment := by
        intro i output
        apply correct_term_table_truth operations root values valueCorrect
        apply formulaTermParts_subformula member
        simp only [formulaTermParts, List.mem_flatten, List.mem_ofFn]
        exact ⟨termParts (arguments i), ⟨i,rfl⟩, term_mem_parts _⟩
      have ha : (∃ actual, (∀ i, values (termCode (arguments i)) environment (actual i)) ∧
          modelPredicates operations _ symbol actual) ↔
          modelPredicates operations _ symbol (fun i => termValue operations (arguments i) environment) := by
        constructor
        · rintro ⟨actual, hv, hp⟩
          have he : actual = fun i => termValue operations (arguments i) environment :=
            funext fun i => (hc i _).mp (hv i)
          simpa [he] using hp
        · intro hp
          exact ⟨_, fun i => (hc i _).mpr rfl, hp⟩
      first
      | exact (truthCorrect _ member environment).trans ha
      | exact (truthCorrect _ member environment).trans (not_congr ha)
  | and left right ihl ihr =>
      apply (truthCorrect _ member environment).trans
      exact and_congr
        (ihl (formulaParts_trans member (by simp [formulaParts])) _)
        (ihr (formulaParts_trans member (by simp [formulaParts])) _)
  | or left right ihl ihr =>
      apply (truthCorrect _ member environment).trans
      exact or_congr
        (ihl (formulaParts_trans member (by simp [formulaParts])) _)
        (ihr (formulaParts_trans member (by simp [formulaParts])) _)
  | all body ih =>
      apply (truthCorrect _ member environment).trans
      change (∀ value, truth (formulaCode body) (pushAssignment value environment)) ↔
        ∀ value, body.Evalb (s := modelStructure operations)
          (Matrix.vecCons value (fun i => lookupCode environment i.val))
      apply forall_congr'
      intro value
      rw [← lookup_push_vector]
      exact ih (formulaParts_trans member (by simp [formulaParts])) _
  | exs body ih =>
      apply (truthCorrect _ member environment).trans
      change (∃ value, truth (formulaCode body) (pushAssignment value environment)) ↔
        ∃ value, body.Evalb (s := modelStructure operations)
          (Matrix.vecCons value (fun i => lookupCode environment i.val))
      apply exists_congr
      intro value
      rw [← lookup_push_vector]
      exact ih (formulaParts_trans member (by simp [formulaParts])) _

def finiteTruth (operations : Operations) (root : Semisentence language n) : TruthTable :=
  fun code environment => (finiteFormulaTable (formulaParts root)).Evalb
    (s := modelStructure operations) ![code,environment]

def finiteValues (operations : Operations) (root : Semisentence language n) : ValueTable :=
  fun code environment value => (finiteTermTable (formulaTermParts root)).Evalb
    (s := modelStructure operations) ![code,environment,value]

theorem finiteTruth_at_member (operations : Operations) (root : Semisentence language n)
    (node : FormulaNode) (member : node ∈ formulaParts root) (environment : Nat) :
    finiteTruth operations root (Encodable.encode node) environment ↔
      formulaTruth operations node.2 environment := by
  unfold finiteTruth
  change (finiteFormulaTable (formulaParts root)).Evalb
    (s := interpretation (withLookup (withApplication operations)) (modelPredicates operations))
      ![Encodable.encode node,environment] ↔ _
  rw [finiteFormulaTable_truth (withApplication operations) (modelPredicates operations)
    (fun _ => Iff.rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro ⟨other, _, equal, correct⟩
    have he : node = other := Encodable.encode_injective equal
    subst other
    exact correct
  · intro correct
    exact ⟨node, member, rfl, correct⟩

theorem finiteValues_at_member (operations : Operations) (root : Semisentence language n)
    (node : TermNode) (member : node ∈ formulaTermParts root) (environment value : Nat) :
    finiteValues operations root (Encodable.encode node) environment value ↔
      value = termValue operations node.2 environment := by
  unfold finiteValues
  change (finiteTermTable (formulaTermParts root)).Evalb
    (s := interpretation (withLookup (withApplication operations)) (modelPredicates operations))
      ![Encodable.encode node,environment,value] ↔ _
  rw [finiteTermTable_truth (withApplication operations) (modelPredicates operations)
    (fun _ => Iff.rfl)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  constructor
  · rintro ⟨other, _, equal, correct⟩
    have he : node = other := Encodable.encode_injective equal
    subst other
    exact correct
  · intro correct
    exact ⟨node, member, rfl, correct⟩

theorem finiteValues_correct (operations : Operations) (root : Semisentence language n) :
    CorrectTermTable operations root (finiteValues operations root) := by
  intro node member environment value
  apply (finiteValues_at_member operations root node member environment value).trans
  apply Iff.symm
  apply termClause_truth
  intro child childMember output
  exact finiteValues_at_member operations root child (formulaTermParts_subterm member childMember) _ _

theorem finiteTruth_correct (operations : Operations) (root : Semisentence language n) :
    CorrectFormulaTable operations root (finiteTruth operations root) (finiteValues operations root) := by
  intro node member environment
  apply (finiteTruth_at_member operations root node member environment).trans
  apply Iff.symm
  apply formulaClause_truth
  · intro child childMember code
    exact finiteTruth_at_member operations root child (formulaParts_trans member childMember) code
  · intro child childMember output
    exact finiteValues_at_member operations root child (formulaTermParts_subformula member childMember) _ _

/-- The finite witnesses belong to the actual first-order-definable relation
sorts. No second-order comprehension principle is used. -/
def truthRelation (operations : Operations) (root : Semisentence language n) :
    @FirstOrderRelations.Relation language Nat (modelStructure operations) 1 := by
  letI := modelStructure operations
  exact ⟨fun tuple => (finiteFormulaTable (formulaParts root)).Evalb
      (s := modelStructure operations) tuple,
    ⟨Rewriting.emb (finiteFormulaTable (formulaParts root)), fun _ => by
      simp only [Semiformula.eval_emb]⟩⟩

def valueRelation (operations : Operations) (root : Semisentence language n) :
    @FirstOrderRelations.Relation language Nat (modelStructure operations) 2 := by
  letI := modelStructure operations
  exact ⟨fun tuple => (finiteTermTable (formulaTermParts root)).Evalb
      (s := modelStructure operations) tuple,
    ⟨Rewriting.emb (finiteTermTable (formulaTermParts root)), fun _ => by
      simp only [Semiformula.eval_emb]⟩⟩

theorem finite_definable_tables_correct (operations : Operations) (root : Semisentence language n) :
    CorrectTermTable operations root (fun code environment value =>
      (valueRelation operations root).val ![code,environment,value]) ∧
    CorrectFormulaTable operations root
      (fun code environment => (truthRelation operations root).val ![code,environment])
      (fun code environment value => (valueRelation operations root).val ![code,environment,value]) :=
  ⟨finiteValues_correct operations root, finiteTruth_correct operations root⟩

theorem correct_tables_sentence_truth (operations : Operations) (sentence : Sentence language)
    (truth : TruthTable) (values : ValueTable)
    (valueCorrect : CorrectTermTable operations sentence values)
    (truthCorrect : CorrectFormulaTable operations sentence truth values) (environment : Nat) :
    truth (formulaCode sentence) environment ↔
      sentenceTruth (modelOperations operations) (modelPredicates operations) (Encodable.encode sentence) := by
  rw [sentenceTruth_encode]
  have h := correct_formula_table_truth operations sentence truth values valueCorrect truthCorrect
    sentence (formula_mem_parts sentence) environment
  have he : (fun i : Fin 0 => lookupCode environment i.val) = Fin.elim0 := Subsingleton.elim _ _
  simpa only [formulaTruth, he] using h

end FregeanECA.Part2.Oracle
