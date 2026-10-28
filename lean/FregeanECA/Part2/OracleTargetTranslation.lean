import FregeanECA.Part2.OracleLanguage
import FregeanECA.Part2.SecondOrderArithmetic

/-! Relational elimination of auxiliary first-order function symbols.
Every symbol is represented by a designated relation parameter; the truth
lemma records each required graph, including parameter and binder handling. -/
namespace FregeanECA.Part2.OracleTarget
open FFL FFL.FirstOrder Positive
open SecondOrderArithmetic (renameTerm renameTerm_value)
universe u v

structure Slots where
  functions : Nat → Nat → Nat
  relations : Nat → Nat → Nat

def existsMany : Nat → Applicative.Formula → Applicative.Formula
  | 0, body => body
  | n+1, body => existsMany n (.existsObject body)

def allFin : {n : Nat} → (Fin n → Applicative.Formula) → Applicative.Formula
  | 0, _ => .implies .falsum .falsum
  | n+1, bodies => .conjunction (bodies 0) (allFin (fun i : Fin n => bodies i.succ))

variable {D : Type u} {R : Nat → Type v}

theorem existsMany_truth (M : Interpretation D R) (predicates : PredicateAssignment R)
    (n : Nat) (body : Applicative.Formula) (objects : ObjectAssignment D) :
    (existsMany n body).truth M objects predicates ↔
      ∃ values : Fin n → D, body.truth M (assignTuple n values objects) predicates := by
  induction n generalizing body with
  | zero => simp [existsMany, assignTuple]
  | succ n ih =>
    rw [existsMany, ih]
    constructor
    · rintro ⟨values, x, h⟩
      refine ⟨Fin.cases (motive := fun _ => D) x values, ?_⟩
      exact h
    · rintro ⟨values, h⟩
      exact ⟨fun i => values i.succ, values 0, h⟩

theorem allFin_truth (M : Interpretation D R) (predicates : PredicateAssignment R)
    {n : Nat} (bodies : Fin n → Applicative.Formula) (objects : ObjectAssignment D) :
    (allFin bodies).truth M objects predicates ↔ ∀ i, (bodies i).truth M objects predicates := by
  induction n with
  | zero => simp [allFin, Applicative.Formula.truth]
  | succ n ih =>
    simp only [allFin, Applicative.Formula.truth, ih]
    exact ⟨fun h i => Fin.cases h.1 h.2 i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

def relationAtom (slots : Slots) : {n : Nat} → Nat →
    (Fin n → Positive.Term) → Applicative.Formula
  | 0, symbol, _ => .relation 0 (slots.relations 0 symbol) (fun _ => .constantK)
  | n+1, symbol, arguments => .relation n (slots.relations (n+1) symbol) arguments

def relationHolds (M : Interpretation D R) (predicates : PredicateAssignment R)
    (slots : Slots) : {n : Nat} → Nat → (Fin n → D) → Prop
  | 0, symbol, _ => M.satisfies 0 (predicates 0 (slots.relations 0 symbol)) (fun _ => M.constantK)
  | n+1, symbol, arguments => M.satisfies n (predicates n (slots.relations (n+1) symbol)) arguments

theorem relationAtom_truth (M : Interpretation D R) (predicates : PredicateAssignment R)
    (slots : Slots) {n : Nat} (symbol : Nat) (arguments : Fin n → Positive.Term)
    (objects : ObjectAssignment D) :
    (relationAtom slots symbol arguments).truth M objects predicates ↔
      relationHolds M predicates slots symbol (fun i => (arguments i).value M objects) := by
  cases n <;> rfl

def termGraph (slots : Slots) {n : Nat} (varmap : Fin n → Positive.Term)
    (output : Positive.Term) : ClosedSemiterm Oracle.language n → Applicative.Formula
  | .bvar i => .equal output (varmap i)
  | .fvar i => Empty.elim i
  | .func (arity := arity) symbol arguments => existsMany arity (.conjunction
      (allFin (fun i => termGraph slots
        (fun j => renameTerm (fun k => arity+k) (varmap j)) (.var i) (arguments i)))
      (.relation arity (slots.functions arity symbol)
        (Fin.cases (renameTerm (fun k => arity+k) output) (fun i => .var i))))

structure Bindings (M : Interpretation D R) [source : Structure Oracle.language D]
    (predicates : PredicateAssignment R) (slots : Slots) : Prop where
  functions : ∀ n symbol (arguments : Fin n → D) output,
    M.satisfies n (predicates n (slots.functions n symbol)) (Fin.cases output arguments) ↔
      output = source.func symbol arguments
  relations : ∀ n symbol (arguments : Fin n → D),
    relationHolds M predicates slots symbol arguments ↔ source.rel symbol arguments

theorem termGraph_truth (M : Interpretation D R) [source : Structure Oracle.language D]
    (predicates : PredicateAssignment R) (slots : Slots) (bindings : Bindings M predicates slots)
    {n : Nat} (term : ClosedSemiterm Oracle.language n) (values : Fin n → D) :
    ∀ (varmap : Fin n → Positive.Term) (output : Positive.Term) (objects : ObjectAssignment D),
      (∀ i, (varmap i).value M objects = values i) →
      ((termGraph slots varmap output term).truth M objects predicates ↔
        output.value M objects = term.valb values) := by
  induction term with
  | bvar i =>
    intro varmap output objects assigned
    simp only [termGraph, Applicative.Formula.truth, Semiterm.valb, Semiterm.val_bvar, assigned]
  | fvar i => exact Empty.elim i
  | @func arity symbol arguments ih =>
    intro varmap output objects assigned
    simp only [termGraph, existsMany_truth, Applicative.Formula.truth, allFin_truth]
    have children (xs : Fin arity → D) (i : Fin arity) :=
      ih i (fun j => renameTerm (fun k => arity+k) (varmap j)) (.var i)
        (assignTuple arity xs objects)
        (by intro j; simpa only [renameTerm_value, assignTuple_after] using assigned j)
    have child_eq (xs : Fin arity → D) :
        (∀ i : Fin arity, (termGraph slots (fun j => renameTerm (fun k => arity+k) (varmap j))
          (.var i) (arguments i)).truth M (assignTuple arity xs objects) predicates) ↔
        xs = fun i => (arguments i).valb values := by
      simp only [children, Positive.Term.value, assignTuple_at]
      exact ⟨fun h => funext h, fun h i => congrFun h i⟩
    have final_eq (xs : Fin arity → D) :
        (fun i : Fin (arity+1) => (Fin.cases (motive := fun _ => Positive.Term)
          (renameTerm (fun k => arity+k) output)
          (fun j : Fin arity => Positive.Term.var j) i).value M (assignTuple arity xs objects)) =
        Fin.cases (output.value M objects) xs := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (renameTerm (fun k => arity+k) output).value M (assignTuple arity xs objects) = output.value M objects
        simp only [renameTerm_value, assignTuple_after]
      · exact assignTuple_at _ _ _ j
    simp only [child_eq, final_eq, bindings.functions, exists_eq_left]
    rfl

def atom (slots : Slots) {n arity : Nat} (varmap : Fin n → Positive.Term)
    (symbol : Nat) (arguments : Fin arity → ClosedSemiterm Oracle.language n) : Applicative.Formula :=
  existsMany arity (.conjunction
    (allFin (fun i => termGraph slots
      (fun j => renameTerm (fun k => arity+k) (varmap j)) (.var i) (arguments i)))
    (relationAtom slots symbol (fun i : Fin arity => .var i)))

theorem atom_truth (M : Interpretation D R) [source : Structure Oracle.language D]
    (predicates : PredicateAssignment R) (slots : Slots) (bindings : Bindings M predicates slots)
    {n arity : Nat} (varmap : Fin n → Positive.Term) (values : Fin n → D)
    (symbol : Nat) (arguments : Fin arity → ClosedSemiterm Oracle.language n)
    (objects : ObjectAssignment D) (assigned : ∀ i, (varmap i).value M objects = values i) :
    (atom slots varmap symbol arguments).truth M objects predicates ↔
      source.rel symbol (fun i => (arguments i).valb values) := by
  simp only [atom, existsMany_truth, Applicative.Formula.truth, allFin_truth]
  have children (xs : Fin arity → D) (i : Fin arity) :=
    termGraph_truth M predicates slots bindings (arguments i) values
      (fun j => renameTerm (fun k => arity+k) (varmap j)) (.var i)
      (assignTuple arity xs objects)
      (by intro j; simpa only [renameTerm_value, assignTuple_after] using assigned j)
  have child_eq (xs : Fin arity → D) :
      (∀ i : Fin arity, (termGraph slots (fun j => renameTerm (fun k => arity+k) (varmap j))
        (.var i) (arguments i)).truth M (assignTuple arity xs objects) predicates) ↔
      xs = fun i => (arguments i).valb values := by
    simp only [children, Positive.Term.value, assignTuple_at]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  simp only [child_eq, relationAtom_truth, Positive.Term.value, assignTuple_at,
    bindings.relations, exists_eq_left]

def translate (slots : Slots) {n : Nat} (varmap : Fin n → Positive.Term) :
    Semisentence Oracle.language n → Applicative.Formula
  | .verum => .implies .falsum .falsum
  | .falsum => .falsum
  | .rel symbol arguments => atom slots varmap symbol arguments
  | .nrel symbol arguments => .implies (atom slots varmap symbol arguments) .falsum
  | .and left right => .conjunction (translate slots varmap left) (translate slots varmap right)
  | .or left right => .disjunction (translate slots varmap left) (translate slots varmap right)
  | .all body => .forallObject (translate slots
      (Fin.cases (.var 0) (fun i => renameTerm Nat.succ (varmap i))) body)
  | .exs body => .existsObject (translate slots
      (Fin.cases (.var 0) (fun i => renameTerm Nat.succ (varmap i))) body)

theorem translation_truth (M : Interpretation D R) [source : Structure Oracle.language D]
    (predicates : PredicateAssignment R) (slots : Slots) (bindings : Bindings M predicates slots)
    {n : Nat} (formula : Semisentence Oracle.language n) :
    ∀ (varmap : Fin n → Positive.Term) (values : Fin n → D) (objects : ObjectAssignment D),
      (∀ i, (varmap i).value M objects = values i) →
      ((translate slots varmap formula).truth M objects predicates ↔ formula.Evalb values) := by
  induction formula with
  | verum => intros; change (False → False) ↔ True; tauto
  | falsum => intros; rfl
  | rel symbol arguments =>
    intro varmap values objects assigned
    exact atom_truth M predicates slots bindings varmap values symbol arguments objects assigned
  | nrel symbol arguments =>
    intro varmap values objects assigned
    exact not_congr (atom_truth M predicates slots bindings varmap values symbol arguments objects assigned)
  | and left right ihl ihr =>
    intro varmap values objects assigned
    exact and_congr (ihl _ _ _ assigned) (ihr _ _ _ assigned)
  | or left right ihl ihr =>
    intro varmap values objects assigned
    exact or_congr (ihl _ _ _ assigned) (ihr _ _ _ assigned)
  | all body ih =>
    intro varmap values objects assigned
    apply forall_congr'
    intro x
    apply ih
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    change (renameTerm Nat.succ (varmap j)).value M (pushObject objects x) = values j
    simpa only [renameTerm_value, pushObject] using assigned j
  | exs body ih =>
    intro varmap values objects assigned
    apply exists_congr
    intro x
    apply ih
    intro i
    refine Fin.cases rfl (fun j => ?_) i
    change (renameTerm Nat.succ (varmap j)).value M (pushObject objects x) = values j
    simpa only [renameTerm_value, pushObject] using assigned j

end FregeanECA.Part2.OracleTarget
