import FregeanECA.Part2.OracleFiniteTables
import FregeanECA.Part2.OracleSyntaxFacts
import FregeanECA.Part2.OracleCodedClauses

/-! An ordinary, uniform first-order formula for finite compositional tables.
Its only variable predicates are the binary truth table and ternary value
table. Primitive operation graphs evaluate one symbol, never formula truth. -/
namespace FregeanECA.Part2.Oracle

open FFL FFL.FirstOrder

def withSyntax (operations : Operations) : Operations := fun n symbol arguments =>
  if h : n = 1 then
    let a := arguments ⟨0, by omega⟩
    match symbol with
    | 1 => formulaTag a
    | 2 => formulaArity a
    | 3 => formulaSymbol a
    | 4 => formulaLeft a
    | 5 => formulaRight a
    | 6 => termTag a
    | 7 => termArity a
    | 8 => termSymbol a
    | 9 => termVariable a
    | 10 => packSentence a
    | 11 => isSentence a
    | _ => operations n symbol arguments
  else if h : n = 2 then
    let a := arguments ⟨0, by omega⟩
    let b := arguments ⟨1, by omega⟩
    match symbol with
    | 2 => formulaArgument a b
    | 3 => termArgument a b
    | 4 => isSubformula a b
    | 5 => isSubterm a b
    | 6 => pushAssignment a b
    | 7 => if a < b then 1 else 0
    | _ => operations n symbol arguments
  else operations n symbol arguments

def tablePredicates (operations : Operations) (truth : TruthTable) (values : ValueTable) :
    ∀ n, Nat → (Fin n → Nat) → Prop := fun n symbol arguments =>
  if h : n = 2 ∧ symbol = 100 then
    truth (arguments ⟨0, by omega⟩) (arguments ⟨1, by omega⟩)
  else if h : n = 3 ∧ symbol = 100 then
    values (arguments ⟨0, by omega⟩) (arguments ⟨1, by omega⟩) (arguments ⟨2, by omega⟩)
  else modelPredicates (withSyntax operations) n symbol arguments

@[instance_reducible] noncomputable def tableStructure
    (operations : Operations) (truth : TruthTable) (values : ValueTable) : Structure language Nat :=
  interpretation (modelOperations (withSyntax operations)) (tablePredicates operations truth values)

abbrev MatrixTerm n := ClosedSemiterm language n
abbrev MatrixFormula n := Semisentence language n

def unaryTerm (symbol : Nat) (a : MatrixTerm n) : MatrixTerm n := .func symbol ![a]
def binaryTerm (symbol : Nat) (a b : MatrixTerm n) : MatrixTerm n := .func symbol ![a,b]
def truthAtom (code environment : MatrixTerm n) : MatrixFormula n := .rel 100 ![code,environment]
def valueAtom (code environment value : MatrixTerm n) : MatrixFormula n :=
  .rel 100 ![code,environment,value]
def primitiveAtom (arity symbol arguments value : MatrixTerm n) : MatrixFormula n :=
  .rel 0 ![arity,symbol,arguments,value]
def iffFormula (left right : MatrixFormula n) : MatrixFormula n :=
  .and (left 🡒 right) (right 🡒 left)
def lessAtom (a b : MatrixTerm n) : MatrixFormula n :=
  equalTerm (binaryTerm 7 a b) (name 1)
def tagAtom (selector expected : Nat) (code : MatrixTerm n) : MatrixFormula n :=
  equalTerm (unaryTerm selector code) (name expected)

def functionMatrix (code environment value : MatrixTerm n) : MatrixFormula n :=
  .exs (.and
    (.all (lessAtom (.bvar 0) (unaryTerm 7 (Rew.bShift (Rew.bShift code))) 🡒
      valueAtom (binaryTerm 3 (Rew.bShift (Rew.bShift code)) (.bvar 0))
        (Rew.bShift (Rew.bShift environment)) (lookupTerm (.bvar 1) (.bvar 0))))
    (primitiveAtom (unaryTerm 7 (Rew.bShift code)) (unaryTerm 8 (Rew.bShift code))
      (.bvar 0) (Rew.bShift value)))

def termMatrix (code environment value : MatrixTerm n) : MatrixFormula n :=
  .or (.and (tagAtom 6 0 code)
    (equalTerm value (lookupTerm environment (unaryTerm 9 code))))
    (.and (tagAtom 6 1 code) (functionMatrix code environment value))

/-- The fixed model has exactly equality and primitive-operation graph
predicates; all other original predicate symbols are false. -/
def originalPredicateMatrix (arity symbol arguments : MatrixTerm n) : MatrixFormula n :=
  .or
    (.and (equalTerm arity (name 2)) (.and (equalTerm symbol (name 0))
      (equalTerm (lookupTerm arguments (name 0)) (lookupTerm arguments (name 1)))))
    (.and (equalTerm arity (name 4)) (.and (equalTerm symbol (name 0))
      (primitiveAtom (lookupTerm arguments (name 0)) (lookupTerm arguments (name 1))
        (lookupTerm arguments (name 2)) (lookupTerm arguments (name 3)))))

def atomicMatrix (code environment : MatrixTerm n) : MatrixFormula n :=
  .exs (.and
    (.all (lessAtom (.bvar 0) (unaryTerm 2 (Rew.bShift (Rew.bShift code))) 🡒
      valueAtom (binaryTerm 2 (Rew.bShift (Rew.bShift code)) (.bvar 0))
        (Rew.bShift (Rew.bShift environment)) (lookupTerm (.bvar 1) (.bvar 0))))
    (originalPredicateMatrix (unaryTerm 2 (Rew.bShift code))
      (unaryTerm 3 (Rew.bShift code)) (.bvar 0)))

def formulaMatrix (code environment : MatrixTerm n) : MatrixFormula n :=
  .or (tagAtom 1 0 code)
  (.or (.and (tagAtom 1 2 code) (atomicMatrix code environment))
  (.or (.and (tagAtom 1 3 code) (∼atomicMatrix code environment))
  (.or (.and (tagAtom 1 4 code) (.and
    (truthAtom (unaryTerm 4 code) environment) (truthAtom (unaryTerm 5 code) environment)))
  (.or (.and (tagAtom 1 5 code) (.or
    (truthAtom (unaryTerm 4 code) environment) (truthAtom (unaryTerm 5 code) environment)))
  (.or (.and (tagAtom 1 6 code) (.all
    (truthAtom (unaryTerm 4 (Rew.bShift code)) (binaryTerm 6 (.bvar 0) (Rew.bShift environment)))))
    (.and (tagAtom 1 7 code) (.exs
      (truthAtom (unaryTerm 4 (Rew.bShift code)) (binaryTerm 6 (.bvar 0) (Rew.bShift environment))))))))))

def termTableMatrix (root : MatrixTerm n) : MatrixFormula n :=
  .all (.all (.all
    (equalTerm (binaryTerm 5 (Rew.bShift (Rew.bShift (Rew.bShift root))) (.bvar 2)) (name 1) 🡒
      iffFormula (valueAtom (.bvar 2) (.bvar 1) (.bvar 0))
        (termMatrix (.bvar 2) (.bvar 1) (.bvar 0)))))

def truthTableMatrix (root : MatrixTerm n) : MatrixFormula n :=
  .all (.all
    (equalTerm (binaryTerm 4 (Rew.bShift (Rew.bShift root)) (.bvar 1)) (name 1) 🡒
      iffFormula (truthAtom (.bvar 1) (.bvar 0)) (formulaMatrix (.bvar 1) (.bvar 0))))

/-- This single ordinary formula checks finite table clauses for the syntax
below its input sentence code, then queries the root entry. -/
def satisfactionMatrix : MatrixFormula 1 :=
  .and (tagAtom 11 1 (.bvar 0))
    (.and (termTableMatrix (unaryTerm 10 (.bvar 0)))
      (.and (truthTableMatrix (unaryTerm 10 (.bvar 0)))
        (truthAtom (unaryTerm 10 (.bvar 0)) (name 0))))


section MatrixSemantics
variable (operations : Operations) (truth : TruthTable) (values : ValueTable)
local notation "tbl" => tableStructure operations truth values

@[simp] theorem matrix_unary_1 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 1 a).val (s := tbl) bound Empty.elim =
      formulaTag (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_2 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 2 a).val (s := tbl) bound Empty.elim =
      formulaArity (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_3 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 3 a).val (s := tbl) bound Empty.elim =
      formulaSymbol (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_4 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 4 a).val (s := tbl) bound Empty.elim =
      formulaLeft (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_5 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 5 a).val (s := tbl) bound Empty.elim =
      formulaRight (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_6 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 6 a).val (s := tbl) bound Empty.elim =
      termTag (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_7 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 7 a).val (s := tbl) bound Empty.elim =
      termArity (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_8 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 8 a).val (s := tbl) bound Empty.elim =
      termSymbol (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_9 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 9 a).val (s := tbl) bound Empty.elim =
      termVariable (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_10 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 10 a).val (s := tbl) bound Empty.elim =
      packSentence (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_unary_11 (a : MatrixTerm n) (bound : Fin n → Nat) :
    (unaryTerm 11 a).val (s := tbl) bound Empty.elim =
      isSentence (a.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_binary_2 (a b : MatrixTerm n) (bound : Fin n → Nat) :
    (binaryTerm 2 a b).val (s := tbl) bound Empty.elim =
      formulaArgument (a.val (s := tbl) bound Empty.elim) (b.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_binary_3 (a b : MatrixTerm n) (bound : Fin n → Nat) :
    (binaryTerm 3 a b).val (s := tbl) bound Empty.elim =
      termArgument (a.val (s := tbl) bound Empty.elim) (b.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_binary_4 (a b : MatrixTerm n) (bound : Fin n → Nat) :
    (binaryTerm 4 a b).val (s := tbl) bound Empty.elim =
      isSubformula (a.val (s := tbl) bound Empty.elim) (b.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_binary_5 (a b : MatrixTerm n) (bound : Fin n → Nat) :
    (binaryTerm 5 a b).val (s := tbl) bound Empty.elim =
      isSubterm (a.val (s := tbl) bound Empty.elim) (b.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_binary_6 (a b : MatrixTerm n) (bound : Fin n → Nat) :
    (binaryTerm 6 a b).val (s := tbl) bound Empty.elim =
      pushAssignment (a.val (s := tbl) bound Empty.elim) (b.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_name (a : Nat) (bound : Fin n → Nat) :
    (name a : MatrixTerm n).val (s := tbl) bound Empty.elim = a := rfl

@[simp] theorem matrix_lookup (a b : MatrixTerm n) (bound : Fin n → Nat) :
    (lookupTerm a b).val (s := tbl) bound Empty.elim =
      lookupCode (a.val (s := tbl) bound Empty.elim) (b.val (s := tbl) bound Empty.elim) := rfl

@[simp] theorem matrix_equal (a b : MatrixTerm n) (bound : Fin n → Nat) :
    (equalTerm a b).Evalb (s := tbl) bound ↔
      a.val (s := tbl) bound Empty.elim = b.val (s := tbl) bound Empty.elim := Iff.rfl

@[simp] theorem matrix_truthAtom (c e : MatrixTerm n) (bound : Fin n → Nat) :
    (truthAtom c e).Evalb (s := tbl) bound ↔
      truth (c.val (s := tbl) bound Empty.elim) (e.val (s := tbl) bound Empty.elim) := Iff.rfl

@[simp] theorem matrix_valueAtom (c e v : MatrixTerm n) (bound : Fin n → Nat) :
    (valueAtom c e v).Evalb (s := tbl) bound ↔
      values (c.val (s := tbl) bound Empty.elim) (e.val (s := tbl) bound Empty.elim)
        (v.val (s := tbl) bound Empty.elim) := Iff.rfl

@[simp] theorem matrix_primitiveAtom (a s c v : MatrixTerm n) (bound : Fin n → Nat) :
    (primitiveAtom a s c v).Evalb (s := tbl) bound ↔
      primitiveGraph (withSyntax operations) (a.val (s := tbl) bound Empty.elim)
        (s.val (s := tbl) bound Empty.elim) (c.val (s := tbl) bound Empty.elim)
        (v.val (s := tbl) bound Empty.elim) := Iff.rfl

@[simp] theorem matrix_and (p q : MatrixFormula n) (bound : Fin n → Nat) :
    (Semiformula.and p q).Evalb (s := tbl) bound ↔
      p.Evalb (s := tbl) bound ∧ q.Evalb (s := tbl) bound := Iff.rfl

@[simp] theorem matrix_or (p q : MatrixFormula n) (bound : Fin n → Nat) :
    (Semiformula.or p q).Evalb (s := tbl) bound ↔
      p.Evalb (s := tbl) bound ∨ q.Evalb (s := tbl) bound := Iff.rfl

@[simp] theorem matrix_not (p : MatrixFormula n) (bound : Fin n → Nat) :
    (∼p).Evalb (s := tbl) bound ↔ ¬p.Evalb (s := tbl) bound := by
  rw [LogicalConnective.HomClass.map_neg]; rfl

@[simp] theorem matrix_imply (p q : MatrixFormula n) (bound : Fin n → Nat) :
    (p 🡒 q).Evalb (s := tbl) bound ↔
      (p.Evalb (s := tbl) bound → q.Evalb (s := tbl) bound) := by
  rw [LogicalConnective.HomClass.map_imply]; rfl

@[simp] theorem matrix_iff (p q : MatrixFormula n) (bound : Fin n → Nat) :
    (iffFormula p q).Evalb (s := tbl) bound ↔
      (p.Evalb (s := tbl) bound ↔ q.Evalb (s := tbl) bound) := by
  simp only [iffFormula, matrix_and, matrix_imply]
  exact ⟨fun h => ⟨h.1,h.2⟩, fun h => ⟨h.mp,h.mpr⟩⟩

@[simp] theorem matrix_all (p : MatrixFormula (n+1)) (bound : Fin n → Nat) :
    (Semiformula.all p).Evalb (s := tbl) bound ↔
      ∀ x, p.Evalb (s := tbl) (x :> bound) := Iff.rfl

@[simp] theorem matrix_exs (p : MatrixFormula (n+1)) (bound : Fin n → Nat) :
    (Semiformula.exs p).Evalb (s := tbl) bound ↔
      ∃ x, p.Evalb (s := tbl) (x :> bound) := Iff.rfl

@[simp] theorem matrix_less (a b : MatrixTerm n) (bound : Fin n → Nat) :
    (lessAtom a b).Evalb (s := tbl) bound ↔
      a.val (s := tbl) bound Empty.elim < b.val (s := tbl) bound Empty.elim := by
  change (if a.val (s := tbl) bound Empty.elim < b.val (s := tbl) bound Empty.elim then 1 else 0) = 1 ↔ _
  simp

theorem functionMatrix_truth (c e v : MatrixTerm n) (bound : Fin n → Nat) :
    (functionMatrix c e v).Evalb (s := tbl) bound ↔
      functionCodeClause (withSyntax operations) values
        (c.val (s := tbl) bound Empty.elim) (e.val (s := tbl) bound Empty.elim)
        (v.val (s := tbl) bound Empty.elim) := by
  simp [functionMatrix, functionCodeClause, matrix_exs, matrix_and, matrix_all,
    matrix_less, matrix_valueAtom, matrix_primitiveAtom,
    Semiterm.val_bShift, Semiterm.val_bvar]

theorem originalPredicateMatrix_truth (a s c : MatrixTerm n) (bound : Fin n → Nat) :
    (originalPredicateMatrix a s c).Evalb (s := tbl) bound ↔
      modelPredicates (withSyntax operations) (a.val (s := tbl) bound Empty.elim)
        (s.val (s := tbl) bound Empty.elim)
        (fun i => lookupCode (c.val (s := tbl) bound Empty.elim) i.val) := by
  simp only [originalPredicateMatrix, matrix_or, matrix_and, matrix_equal,
    matrix_primitiveAtom, matrix_lookup, matrix_name]
  unfold modelPredicates
  split_ifs with h2 h4
  · obtain ⟨ha,hs⟩ := h2
    simp [ha, hs]
  · obtain ⟨ha,hs⟩ := h4
    simp [ha, hs]
  · simp only [not_and] at h2 h4
    tauto

theorem atomicMatrix_truth (c e : MatrixTerm n) (bound : Fin n → Nat) :
    (atomicMatrix c e).Evalb (s := tbl) bound ↔
      atomicCodeClause (withSyntax operations) values
        (c.val (s := tbl) bound Empty.elim) (e.val (s := tbl) bound Empty.elim) := by
  unfold atomicCodeClause
  have pred_iff (arity symbol arguments : Nat) :
      modelPredicates (withSyntax operations) arity symbol (fun i => lookupCode arguments i.val) ↔
        (arity = 2 ∧ symbol = 0 ∧ lookupCode arguments 0 = lookupCode arguments 1) ∨
        (arity = 4 ∧ symbol = 0 ∧ primitiveGraph (withSyntax operations)
          (lookupCode arguments 0) (lookupCode arguments 1)
          (lookupCode arguments 2) (lookupCode arguments 3)) := by
    unfold modelPredicates
    split_ifs with h2 h4
    · obtain ⟨rfl,rfl⟩ := h2; simp
    · obtain ⟨rfl,rfl⟩ := h4; simp
    · simp only [not_and] at h2 h4
      tauto
  simp only [pred_iff]
  simp [atomicMatrix, originalPredicateMatrix,
    matrix_exs, matrix_and, matrix_all, matrix_less,
    matrix_valueAtom, Semiterm.val_bShift, Semiterm.val_bvar]

theorem termMatrix_truth (c e v : MatrixTerm n) (bound : Fin n → Nat) :
    (termMatrix c e v).Evalb (s := tbl) bound ↔
      termCodeClause (withSyntax operations) values
        (c.val (s := tbl) bound Empty.elim) (e.val (s := tbl) bound Empty.elim)
        (v.val (s := tbl) bound Empty.elim) := by
  simp [termMatrix, termCodeClause, tagAtom, functionMatrix_truth]

theorem formulaMatrix_truth (c e : MatrixTerm n) (bound : Fin n → Nat) :
    (formulaMatrix c e).Evalb (s := tbl) bound ↔
      formulaCodeClause (withSyntax operations) truth values
        (c.val (s := tbl) bound Empty.elim) (e.val (s := tbl) bound Empty.elim) := by
  simp [formulaMatrix, formulaCodeClause, tagAtom, atomicMatrix_truth]

theorem termTableMatrix_truth (root : MatrixTerm n) (bound : Fin n → Nat) :
    (termTableMatrix root).Evalb (s := tbl) bound ↔
      ∀ code environment value, isSubterm (root.val (s := tbl) bound Empty.elim) code = 1 →
        (values code environment value ↔
          termCodeClause (withSyntax operations) values code environment value) := by
  simp [termTableMatrix, termMatrix_truth]

theorem truthTableMatrix_truth (root : MatrixTerm n) (bound : Fin n → Nat) :
    (truthTableMatrix root).Evalb (s := tbl) bound ↔
      ∀ code environment, isSubformula (root.val (s := tbl) bound Empty.elim) code = 1 →
        (truth code environment ↔
          formulaCodeClause (withSyntax operations) truth values code environment) := by
  simp [truthTableMatrix, formulaMatrix_truth]

theorem termTableMatrix_at_formula (root : Semisentence language k)
    (term : MatrixTerm n) (bound : Fin n → Nat)
    (code : term.val (s := tbl) bound Empty.elim = formulaCode root) :
    (termTableMatrix term).Evalb (s := tbl) bound ↔
      CorrectTermTable (withSyntax operations) root values := by
  rw [termTableMatrix_truth, code]
  constructor
  · intro correct ⟨arity,child⟩ member environment value
    have included := (isSubterm_iff root (termCode child)).mpr ⟨⟨arity,child⟩,member,rfl⟩
    exact (correct _ _ _ included).trans
      (termCodeClause_truth (withSyntax operations) values child environment value)
  · intro correct code environment value included
    obtain ⟨⟨arity,child⟩,member,rfl⟩ := (isSubterm_iff root code).mp included
    exact (correct _ member _ _).trans
      (termCodeClause_truth (withSyntax operations) values child environment value).symm

theorem truthTableMatrix_at_formula (root : Semisentence language k)
    (term : MatrixTerm n) (bound : Fin n → Nat)
    (code : term.val (s := tbl) bound Empty.elim = formulaCode root) :
    (truthTableMatrix term).Evalb (s := tbl) bound ↔
      CorrectFormulaTable (withSyntax operations) root truth values := by
  rw [truthTableMatrix_truth, code]
  constructor
  · intro correct ⟨arity,child⟩ member environment
    have included := (isSubformula_iff root (formulaCode child)).mpr ⟨⟨arity,child⟩,member,rfl⟩
    exact (correct _ _ included).trans
      (formulaCodeClause_truth (withSyntax operations) truth values child environment)
  · intro correct code environment included
    obtain ⟨⟨arity,child⟩,member,rfl⟩ := (isSubformula_iff root code).mp included
    exact (correct _ member _).trans
      (formulaCodeClause_truth (withSyntax operations) truth values child environment).symm

/-- The uniform formula checks the exact typed compositional clauses on
every actual sentence code. No truth predicate is a premise. -/
theorem satisfactionMatrix_truth (sentence : Sentence language) :
    satisfactionMatrix.Evalb (s := tbl) (fun _ => Encodable.encode sentence) ↔
      CorrectTermTable (withSyntax operations) sentence values ∧
      CorrectFormulaTable (withSyntax operations) sentence truth values ∧
      truth (formulaCode sentence) 0 := by
  have code : (unaryTerm 10 (.bvar 0) : MatrixTerm 1).val
      (s := tbl) (fun _ => Encodable.encode sentence) Empty.elim = formulaCode sentence := by
    simp
  simp only [satisfactionMatrix, matrix_and, tagAtom, matrix_equal, matrix_unary_11,
    matrix_name, Semiterm.val_bvar, isSentence_encode, true_and]
  rw [termTableMatrix_at_formula operations truth values sentence _ _ code,
    truthTableMatrix_at_formula operations truth values sentence _ _ code]
  simp only [matrix_truthAtom, code, matrix_name]

end MatrixSemantics

/-- Actual available first-order-definable table witnesses suffice for each
sentence. The matrix is uniform, but no uniform truth relation is assumed. -/
theorem exists_definable_tables_iff (operations : Operations) (sentence : Sentence language) :
    (∃ (truth : @FirstOrderRelations.Relation language Nat
          (modelStructure (withSyntax operations)) 1)
       (values : @FirstOrderRelations.Relation language Nat
          (modelStructure (withSyntax operations)) 2),
      satisfactionMatrix.Evalb
        (s := tableStructure operations (fun c e => truth.val ![c,e])
          (fun c e v => values.val ![c,e,v])) (fun _ => Encodable.encode sentence)) ↔
      sentence.Evalb (s := modelStructure (withSyntax operations)) Fin.elim0 := by
  constructor
  · rintro ⟨truth,values,satisfied⟩
    obtain ⟨termCorrect,formulaCorrect,root⟩ :=
      (satisfactionMatrix_truth operations _ _ sentence).mp satisfied
    have trueSentence := (correct_tables_sentence_truth (withSyntax operations) sentence
      _ _ termCorrect formulaCorrect 0).mp root
    exact (sentenceTruth_encode _ _ sentence).mp trueSentence
  · intro trueSentence
    let truth := truthRelation (withSyntax operations) sentence
    let values := valueRelation (withSyntax operations) sentence
    refine ⟨truth,values,(satisfactionMatrix_truth operations _ _ sentence).mpr ?_⟩
    have correct := finite_definable_tables_correct (withSyntax operations) sentence
    refine ⟨correct.1,correct.2,?_⟩
    apply (correct_tables_sentence_truth (withSyntax operations) sentence _ _ correct.1 correct.2 0).mpr
    exact (sentenceTruth_encode _ _ sentence).mpr trueSentence

end FregeanECA.Part2.Oracle
