import FregeanECA.Part2.SecondOrderArithmetic
import FregeanECA.LogicBridge

/-! The actual two-sorted Z2 language encoded in Foundation's first-order
sequent calculus. All number and set quantifiers, including free-variable
universal closures, are guarded. Provability is Foundation provability. -/

namespace FregeanECA.Part2.ArithmeticEncoding
open FFL FFL.FirstOrder

inductive SortName where
  | number | set
  deriving DecidableEq

inductive Func : Nat → Type where
  | zero : Func 0
  | successor : Func 1
  | add : Func 2
  | multiply : Func 2

inductive Rel : Nat → Type where
  | equal : Rel 2
  | sort (kind : SortName) : Rel 1
  | member : Rel 2

def language : Language where
  Func := Func
  Rel := Rel

instance : language.Eq := ⟨Rel.equal⟩

abbrev Term (n : Nat) := Semiterm language Nat n
abbrev Formula (n : Nat) := Semiformula language Nat n
abbrev Map (n : Nat) := SortName → Nat → Term n

def variableCode : SortName → Nat → Nat
  | .number, i => 2 * i
  | .set, i => 2 * i + 1

def variableSort (i : Nat) : SortName := if i % 2 = 0 then .number else .set

@[simp] theorem variableCode_index (kind : SortName) (i : Nat) :
    variableCode kind i / 2 = i := by
  cases kind <;> simp only [variableCode] <;> omega

@[simp] theorem variableCode_sort (kind : SortName) (i : Nat) :
    variableSort (variableCode kind i) = kind := by
  cases kind <;> simp [variableSort, variableCode, Nat.add_mod]

theorem variableCode_recover (i : Nat) : variableCode (variableSort i) (i / 2) = i := by
  unfold variableSort
  split <;> simp only [variableCode] <;> omega

def initialMap : Map 0 := fun kind i => .fvar (variableCode kind i)

def bind (kind : SortName) (m : Map n) : Map (n + 1) := fun other i =>
  if other = kind then match i with
    | 0 => .bvar 0
    | j + 1 => Rew.bShift (m other j)
  else Rew.bShift (m other i)

def eqn (a b : Term n) : Formula n := .rel .equal ![a, b]
def guard (kind : SortName) (a : Term n) : Formula n := .rel (.sort kind) ![a]

def term (m : Map n) : SecondOrderArithmetic.Term → Term n
  | .var i => m .number i
  | .zero => .func .zero ![]
  | .successor t => .func .successor ![term m t]
  | .add s t => .func .add ![term m s, term m t]
  | .multiply s t => .func .multiply ![term m s, term m t]

def formula (m : Map n) : SecondOrderArithmetic.Formula → Formula n
  | .equal a b => eqn (term m a) (term m b)
  | .member t i => .rel .member ![term m t, m .set i]
  | .setEqual i j => eqn (m .set i) (m .set j)
  | .falsum => .falsum
  | .implies a b => formula m a 🡒 formula m b
  | .conjunction a b => .and (formula m a) (formula m b)
  | .disjunction a b => .or (formula m a) (formula m b)
  | .existsNumber p => .exs (.and (guard .number (.bvar 0)) (formula (bind .number m) p))
  | .forallNumber p => .all (guard .number (.bvar 0) 🡒 formula (bind .number m) p)
  | .existsSet p => .exs (.and (guard .set (.bvar 0)) (formula (bind .set m) p))
  | .forallSet p => .all (guard .set (.bvar 0) 🡒 formula (bind .set m) p)

universe u v
variable {D : Type u} {R : Nat → Type v}
variable {M : Positive.Interpretation D R} {N : R 0}

inductive Tagged (A : SecondOrderArithmetic.Operations M N) where
  | number (value : SecondOrderArithmetic.Number M N)
  | set (value : SecondOrderArithmetic.SetDomain M N)

def getNumber (A : SecondOrderArithmetic.Operations M N) : Tagged A → SecondOrderArithmetic.Number M N
  | .number x => x
  | .set _ => A.zero

@[instance_reducible] def taggedStructure (A : SecondOrderArithmetic.Operations M N) : Structure language (Tagged A) where
  func := fun {_} f args => match f with
    | .zero => .number A.zero
    | .successor => .number (A.successor (getNumber A (args 0)))
    | .add => .number (A.add (getNumber A (args 0)) (getNumber A (args 1)))
    | .multiply => .number (A.multiply (getNumber A (args 0)) (getNumber A (args 1)))
  rel := fun {_} r args => match r with
    | .equal => args 0 = args 1
    | .sort .number => ∃ x : SecondOrderArithmetic.Number M N, Tagged.number x = args 0
    | .sort .set => ∃ x : SecondOrderArithmetic.SetDomain M N, Tagged.set x = args 0
    | .member => match args 0, args 1 with
      | .number x, .set X => X.val x
      | _, _ => False

section Semantics
variable (A : SecondOrderArithmetic.Operations M N)
local instance : Structure language (Tagged A) := taggedStructure A

structure Maps (m : Map n) (bound : Fin n → Tagged A) (free : Nat → Tagged A)
    (numbers : Nat → SecondOrderArithmetic.Number M N) (sets : Nat → SecondOrderArithmetic.SetDomain M N) : Prop where
  numbers : ∀ i, (m .number i).val bound free = .number (numbers i)
  sets : ∀ i, (m .set i).val bound free = .set (sets i)

theorem Maps.bind_number {m : Map n} {bound : Fin n → Tagged A}
    {free : Nat → Tagged A} {numbers : Nat → SecondOrderArithmetic.Number M N}
    {sets : Nat → SecondOrderArithmetic.SetDomain M N} (h : Maps A m bound free numbers sets) (x : SecondOrderArithmetic.Number M N) :
    Maps A (bind .number m) (Tagged.number x :> bound) free (Positive.pushObject numbers x) sets := by
  constructor
  · intro i; cases i <;> simp [bind, Positive.pushObject, h.numbers]
  · intro i; simp [bind, h.sets]

theorem Maps.bind_set {m : Map n} {bound : Fin n → Tagged A}
    {free : Nat → Tagged A} {numbers : Nat → SecondOrderArithmetic.Number M N}
    {sets : Nat → SecondOrderArithmetic.SetDomain M N} (h : Maps A m bound free numbers sets) (X : SecondOrderArithmetic.SetDomain M N) :
    Maps A (bind .set m) (Tagged.set X :> bound) free numbers (Positive.pushObject sets X) := by
  constructor
  · intro i; simp [bind, h.numbers]
  · intro i; cases i <;> simp [bind, Positive.pushObject, h.sets]

theorem values_nil (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    (fun i : Fin 0 => Semiterm.val bound free ((![] : Fin 0 → Term n) i)) = ![] := by
  funext i; exact Fin.elim0 i

theorem values_one (a : Term n) (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    (fun i : Fin 1 => Semiterm.val bound free (![a] i)) = ![a.val bound free] := by
  funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem values_two (a b : Term n) (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    (fun i : Fin 2 => Semiterm.val bound free (![a,b] i)) = ![a.val bound free,b.val bound free] := by
  funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

theorem term_value (t : SecondOrderArithmetic.Term) {m : Map n} {bound : Fin n → Tagged A}
    {free : Nat → Tagged A} {numbers : Nat → SecondOrderArithmetic.Number M N}
    {sets : Nat → SecondOrderArithmetic.SetDomain M N} (h : Maps A m bound free numbers sets) :
    (term m t).val bound free = Tagged.number (t.value A numbers) := by
  induction t with
  | var i => exact h.numbers i
  | zero => rfl
  | successor t ih =>
      change Structure.func (L := language) (M := Tagged A) .successor _ = _
      rw [values_one, ih]
      rfl
  | add s t hs ht =>
      change Structure.func (L := language) (M := Tagged A) .add _ = _
      rw [values_two, hs, ht]
      rfl
  | multiply s t hs ht =>
      change Structure.func (L := language) (M := Tagged A) .multiply _ = _
      rw [values_two, hs, ht]
      rfl

@[simp] theorem eval_eqn (a b : Term n) (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    Semiformula.Eval bound free (eqn a b) ↔ a.val bound free = b.val bound free := by
  rfl

@[simp] theorem eval_guard (kind : SortName) (a : Term n)
    (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    Semiformula.Eval bound free (guard kind a) ↔
      Structure.rel (L := language) (M := Tagged A) (.sort kind) ![a.val bound free] := by
  change Structure.rel (L := language) (M := Tagged A) (.sort kind) _ ↔ _
  rw [values_one]

@[simp] theorem eval_and (a b : Formula n) (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    Semiformula.Eval bound free (.and a b) ↔
      Semiformula.Eval bound free a ∧ Semiformula.Eval bound free b := Iff.rfl

@[simp] theorem eval_or (a b : Formula n) (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    Semiformula.Eval bound free (.or a b) ↔
      Semiformula.Eval bound free a ∨ Semiformula.Eval bound free b := Iff.rfl

@[simp] theorem eval_implies (a b : Formula n) (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    Semiformula.Eval bound free (a 🡒 b) ↔
      (Semiformula.Eval bound free a → Semiformula.Eval bound free b) := by
  rw [LogicalConnective.HomClass.map_imply]; rfl

@[simp] theorem eval_forall (p : Formula (n+1)) (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    Semiformula.Eval bound free (.all p) ↔ ∀ x, Semiformula.Eval (x :> bound) free p := Iff.rfl

@[simp] theorem eval_exists (p : Formula (n+1)) (bound : Fin n → Tagged A) (free : Nat → Tagged A) :
    Semiformula.Eval bound free (.exs p) ↔ ∃ x, Semiformula.Eval (x :> bound) free p := Iff.rfl

theorem formula_truth (p : SecondOrderArithmetic.Formula) :
    ∀ {n} (m : Map n) (bound : Fin n → Tagged A) (free : Nat → Tagged A)
      (numbers : Nat → SecondOrderArithmetic.Number M N) (sets : Nat → SecondOrderArithmetic.SetDomain M N),
      Maps A m bound free numbers sets →
      (Semiformula.Eval bound free (formula m p) ↔ p.truth A numbers sets) := by
  induction p with
  | equal s t =>
      intro n m bound free numbers sets h
      simp only [formula, SecondOrderArithmetic.Formula.truth, eval_eqn, term_value A s h, term_value A t h,
        Tagged.number.injEq]
  | member t i =>
      intro n m bound free numbers sets h
      change (match (term m t).val bound free, (m .set i).val bound free with
        | .number x, .set X => X.val x
        | _, _ => False) ↔ _
      rw [term_value A t h, h.sets]
      rfl
  | setEqual i j =>
      intro n m bound free numbers sets h
      simp only [formula, SecondOrderArithmetic.Formula.truth, eval_eqn, h.sets, Tagged.set.injEq]
  | falsum => intros; exact Iff.rfl
  | implies p q hp hq =>
      intro n m bound free numbers sets h
      exact (eval_implies A _ _ _ _).trans (imp_congr (hp _ _ _ _ _ h) (hq _ _ _ _ _ h))
  | conjunction p q hp hq =>
      intro n m bound free numbers sets h
      exact (eval_and A _ _ _ _).trans (and_congr (hp _ _ _ _ _ h) (hq _ _ _ _ _ h))
  | disjunction p q hp hq =>
      intro n m bound free numbers sets h
      exact (eval_or A _ _ _ _).trans (or_congr (hp _ _ _ _ _ h) (hq _ _ _ _ _ h))
  | existsNumber p ih =>
      intro n m bound free numbers sets h
      change (∃ x, (∃ y : SecondOrderArithmetic.Number M N, Tagged.number y = x) ∧
        Semiformula.Eval (x :> bound) free (formula (bind .number m) p)) ↔ _
      constructor
      · rintro ⟨x, ⟨y, rfl⟩, holds⟩
        exact ⟨y, (ih _ _ _ _ _ (h.bind_number A y)).mp holds⟩
      · rintro ⟨y, holds⟩
        exact ⟨.number y, ⟨y, rfl⟩, (ih _ _ _ _ _ (h.bind_number A y)).mpr holds⟩
  | forallNumber p ih =>
      intro n m bound free numbers sets h
      simp only [formula, eval_forall, eval_implies, eval_guard, Semiterm.val_bvar,
        Matrix.cons_val_zero, SecondOrderArithmetic.Formula.truth]
      change (∀ x, (∃ y : SecondOrderArithmetic.Number M N, Tagged.number y = x) →
        Semiformula.Eval (x :> bound) free (formula (bind .number m) p)) ↔ _
      constructor
      · intro holds y
        exact (ih _ _ _ _ _ (h.bind_number A y)).mp (holds (.number y) ⟨y,rfl⟩)
      · intro holds x witness
        obtain ⟨y,rfl⟩ := witness
        exact (ih _ _ _ _ _ (h.bind_number A y)).mpr (holds y)
  | existsSet p ih =>
      intro n m bound free numbers sets h
      change (∃ x, (∃ Y : SecondOrderArithmetic.SetDomain M N, Tagged.set Y = x) ∧
        Semiformula.Eval (x :> bound) free (formula (bind .set m) p)) ↔ _
      constructor
      · rintro ⟨x, ⟨Y,rfl⟩, holds⟩
        exact ⟨Y, (ih _ _ _ _ _ (h.bind_set A Y)).mp holds⟩
      · rintro ⟨Y,holds⟩
        exact ⟨.set Y, ⟨Y,rfl⟩, (ih _ _ _ _ _ (h.bind_set A Y)).mpr holds⟩
  | forallSet p ih =>
      intro n m bound free numbers sets h
      simp only [formula, eval_forall, eval_implies, eval_guard, Semiterm.val_bvar,
        Matrix.cons_val_zero, SecondOrderArithmetic.Formula.truth]
      change (∀ x, (∃ Y : SecondOrderArithmetic.SetDomain M N, Tagged.set Y = x) →
        Semiformula.Eval (x :> bound) free (formula (bind .set m) p)) ↔ _
      constructor
      · intro holds Y
        exact (ih _ _ _ _ _ (h.bind_set A Y)).mp (holds (.set Y) ⟨Y,rfl⟩)
      · intro holds x witness
        obtain ⟨Y,rfl⟩ := witness
        exact (ih _ _ _ _ _ (h.bind_set A Y)).mpr (holds Y)

def encodedAssignment (numbers : Nat → SecondOrderArithmetic.Number M N)
    (sets : Nat → SecondOrderArithmetic.SetDomain M N) (i : Nat) : Tagged A :=
  match variableSort i with
  | .number => .number (numbers (i / 2))
  | .set => .set (sets (i / 2))

@[simp] theorem encodedAssignment_number (numbers : Nat → SecondOrderArithmetic.Number M N)
    (sets : Nat → SecondOrderArithmetic.SetDomain M N) (i : Nat) :
    encodedAssignment A numbers sets (variableCode .number i) = .number (numbers i) := by
  simp only [encodedAssignment, variableCode_sort, variableCode_index]

@[simp] theorem encodedAssignment_set (numbers : Nat → SecondOrderArithmetic.Number M N)
    (sets : Nat → SecondOrderArithmetic.SetDomain M N) (i : Nat) :
    encodedAssignment A numbers sets (variableCode .set i) = .set (sets i) := by
  simp only [encodedAssignment, variableCode_sort, variableCode_index]

theorem encodedAssignment_maps (numbers : Nat → SecondOrderArithmetic.Number M N)
    (sets : Nat → SecondOrderArithmetic.SetDomain M N) :
    Maps A initialMap ![] (encodedAssignment A numbers sets) numbers sets := by
  constructor <;> intro i <;> simp [initialMap]

theorem encodedAssignment_guarded (numbers : Nat → SecondOrderArithmetic.Number M N)
    (sets : Nat → SecondOrderArithmetic.SetDomain M N) (i : Nat) :
    Structure.rel (L := language) (M := Tagged A) (.sort (variableSort i))
      ![encodedAssignment A numbers sets i] := by
  cases kind : variableSort i with
  | number =>
      change ∃ x : SecondOrderArithmetic.Number M N,
        Tagged.number x = encodedAssignment A numbers sets i
      exact ⟨numbers (i/2), by simp [encodedAssignment, kind]⟩
  | set =>
      change ∃ X : SecondOrderArithmetic.SetDomain M N,
        Tagged.set X = encodedAssignment A numbers sets i
      exact ⟨sets (i/2), by simp [encodedAssignment, kind]⟩

def freeGuards : List Nat → Formula 0
  | [] => .verum
  | i :: rest => .and (guard (variableSort i) (.fvar i)) (freeGuards rest)

theorem freeGuards_truth (names : List Nat) (free : Nat → Tagged A) :
    Semiformula.Evalf free (freeGuards names) ↔
      ∀ i ∈ names, Structure.rel (L := language) (M := Tagged A) (.sort (variableSort i)) ![free i] := by
  induction names with
  | nil => change True ↔ _; simp
  | cons i rest ih =>
      simp only [freeGuards, eval_and, eval_guard, Semiterm.val_fvar]
      simpa only [List.mem_cons, forall_eq_or_imp] using and_congr Iff.rfl ih

/-- Guard exactly the free number/set variables before universal closure. -/
noncomputable def sentence (p : SecondOrderArithmetic.Formula) : Sentence language :=
  ((freeGuards (formula initialMap p).freeVariables.toList) 🡒 formula initialMap p).univCl

def getSet : Tagged A → SecondOrderArithmetic.SetDomain M N
  | .number _ => SecondOrderArithmetic.representedSet M N N
  | .set X => X

theorem guarded_assignment_recovery (free : Nat → Tagged A) :
    ∃ (numbers : Nat → SecondOrderArithmetic.Number M N)
      (sets : Nat → SecondOrderArithmetic.SetDomain M N),
      ∀ i, Structure.rel (L := language) (M := Tagged A) (.sort (variableSort i)) ![free i] →
        encodedAssignment A numbers sets i = free i := by
  let numbers := fun j => getNumber A (free (variableCode .number j))
  let sets := fun j => getSet A (free (variableCode .set j))
  refine ⟨numbers, sets, ?_⟩
  intro i guarded
  have code := variableCode_recover i
  cases kind : variableSort i with
  | number =>
      have code' : variableCode .number (i/2) = i := by simpa [kind] using code
      have witness : ∃ x : SecondOrderArithmetic.Number M N, Tagged.number x = free i := by
        simpa only [kind, Structure.rel, taggedStructure, Matrix.cons_val_zero] using guarded
      obtain ⟨x, hx⟩ := witness
      simp only [encodedAssignment, kind, numbers, code']
      rw [← hx]
      rfl
  | set =>
      have code' : variableCode .set (i/2) = i := by simpa [kind] using code
      have witness : ∃ X : SecondOrderArithmetic.SetDomain M N, Tagged.set X = free i := by
        simpa only [kind, Structure.rel, taggedStructure, Matrix.cons_val_zero] using guarded
      obtain ⟨X, hx⟩ := witness
      simp only [encodedAssignment, kind, sets, code']
      rw [← hx]
      rfl

/-- The Foundation sentence is equivalent to validity for all genuine sorted assignments. -/
theorem sentence_truth (p : SecondOrderArithmetic.Formula) :
    Semiformula.Realize (Tagged A) (sentence p) ↔ SecondOrderArithmetic.Valid A p := by
  let : Nonempty (Tagged A) := ⟨Tagged.number A.zero⟩
  rw [sentence, Semiformula.eval_univCl]
  constructor
  · intro holds numbers sets
    have guarded : Semiformula.Evalf (encodedAssignment A numbers sets)
        (freeGuards (formula initialMap p).freeVariables.toList) :=
      (freeGuards_truth A _ _).mpr (fun i _ => encodedAssignment_guarded A numbers sets i)
    have encoded := (eval_implies A _ _ ![] _).mp
      (holds (encodedAssignment A numbers sets)) guarded
    exact (formula_truth A p _ _ _ _ _ (encodedAssignment_maps A numbers sets)).mp encoded
  · intro holds free
    apply (eval_implies A _ _ ![] free).mpr
    intro guarded
    obtain ⟨numbers, sets, recovered⟩ := guarded_assignment_recovery A free
    have encoded : Semiformula.Evalf (encodedAssignment A numbers sets) (formula initialMap p) :=
      (formula_truth A p _ _ _ _ _ (encodedAssignment_maps A numbers sets)).mpr (holds numbers sets)
    apply (Semiformula.eval_iff_of_funEqOn (formula initialMap p) ?_).mp encoded
    intro i present
    apply recovered
    exact (freeGuards_truth A _ _).mp guarded i (by simpa using present)

end Semantics

noncomputable def nonemptySortAxiom (kind : SortName) : Sentence language :=
  (Semiformula.exs (guard kind (.bvar 0)) : Formula 0).univCl

noncomputable def zeroTyping : Sentence language :=
  (guard .number (.func .zero ![]) : Formula 0).univCl

noncomputable def successorTyping : Sentence language :=
  (guard .number (.fvar 0) 🡒 guard .number (.func .successor ![.fvar 0]) : Formula 0).univCl

noncomputable def binaryTyping (f : Func 2) : Sentence language :=
  (guard .number (.fvar 0) 🡒 (guard .number (.fvar 1) 🡒
    guard .number (.func f ![.fvar 0, .fvar 1])) : Formula 0).univCl

inductive StructuralAxiom : Sentence language → Prop where
  | nonempty (kind) : StructuralAxiom (nonemptySortAxiom kind)
  | zero : StructuralAxiom zeroTyping
  | successor : StructuralAxiom successorTyping
  | binary (f : Func 2) : StructuralAxiom (binaryTyping f)

/-- Equality, the ordinary sort-typing rules, and the actual Z2 axioms and scheme. -/
noncomputable def theory : Theory language :=
  Theory.eqAxiom language ∪ {p | StructuralAxiom p} ∪
    {p | ∃ q, SecondOrderArithmetic.Axiom q ∧ sentence q = p}

instance equalityIncluded : Theory.eqAxiom language ⪯ theory :=
  Entailment.Axiomatized.le_of_subset (fun _ h => Or.inl (Or.inl h))

section TheoryModels
variable (A : SecondOrderArithmetic.Operations M N)
local instance : Structure language (Tagged A) := taggedStructure A
local instance : Nonempty (Tagged A) := ⟨Tagged.number A.zero⟩

theorem tagged_equality : Structure.Eq language (Tagged A) :=
  ⟨fun _ _ => Iff.rfl⟩

private theorem function_value_has_number_sort (f : Func arity) (args : Fin arity → Term 0)
    (free : Nat → Tagged A) : Semiformula.Evalf free (guard .number (.func f args)) := by
  apply (eval_guard A _ _ ![] free).mpr
  change ∃ x, Tagged.number x = (.func f args : Term 0).val ![] free
  cases f <;> exact ⟨_, rfl⟩

theorem structural_axioms_valid (p : Sentence language) (sourceAxiom : StructuralAxiom p) :
    p.Realize (Tagged A) := by
  cases sourceAxiom with
  | nonempty kind =>
      rw [nonemptySortAxiom, Semiformula.eval_univCl]
      intro free
      cases kind with
      | number =>
          change ∃ x : Tagged A, ∃ y : SecondOrderArithmetic.Number M N, Tagged.number y = x
          exact ⟨Tagged.number A.zero, A.zero, rfl⟩
      | set =>
          change ∃ x : Tagged A, ∃ X : SecondOrderArithmetic.SetDomain M N, Tagged.set X = x
          exact ⟨Tagged.set (SecondOrderArithmetic.representedSet M N N),
            SecondOrderArithmetic.representedSet M N N, rfl⟩
  | zero =>
      rw [zeroTyping, Semiformula.eval_univCl]
      intro free
      exact function_value_has_number_sort A .zero ![] free
  | successor =>
      rw [successorTyping, Semiformula.eval_univCl]
      intro free
      exact (eval_implies A _ _ ![] free).mpr (fun _ =>
        function_value_has_number_sort A .successor ![.fvar 0] free)
  | binary f =>
      rw [binaryTyping, Semiformula.eval_univCl]
      intro free
      exact (eval_implies A _ _ ![] free).mpr (fun _ =>
        (eval_implies A _ _ ![] free).mpr (fun _ =>
          function_value_has_number_sort A f ![.fvar 0, .fvar 1] free))

theorem model_of_valid_axioms
    (axioms : ∀ p, SecondOrderArithmetic.Axiom p → SecondOrderArithmetic.Valid A p) :
    (Tagged A)↓[language] ⊧* theory := by
  let := tagged_equality A
  refine ⟨?_⟩
  intro p hp
  rcases hp with (equality | structural) | ⟨q, sourceAxiom, rfl⟩
  · exact (inferInstance : (Tagged A)↓[language] ⊧* Theory.eqAxiom language).models _ equality
  · exact structural_axioms_valid A p structural
  · exact (sentence_truth A q).mpr (axioms q sourceAxiom)

end TheoryModels

def taggedModel (A : SecondOrderArithmetic.Operations M N) : Struc.{u, 0} language :=
  @Structure.toStruc language (Tagged A) ⟨Tagged.number A.zero⟩ (taggedStructure A)

theorem taggedModel_truth (A : SecondOrderArithmetic.Operations M N) (p : SecondOrderArithmetic.Formula) :
    taggedModel A ⊧ sentence p ↔ SecondOrderArithmetic.Valid A p :=
  sentence_truth A p

theorem taggedModel_valid (A : SecondOrderArithmetic.Operations M N)
    (axioms : ∀ p, SecondOrderArithmetic.Axiom p → SecondOrderArithmetic.Valid A p) :
    taggedModel A ⊧* theory :=
  model_of_valid_axioms A axioms

theorem arithmetic_taggedModel_valid (G : Arithmetic.FullArithmetic M N)
    (full : HasFullComprehension M) :
    taggedModel (SecondOrderArithmetic.arithmeticOperations G) ⊧* theory :=
  taggedModel_valid _ (SecondOrderArithmetic.all_axioms_valid G full)

/-- Actual source proofs are sound in the arithmetic structure obtained from
full comprehension. No semantic replacement of the proof relation is used. -/
theorem arithmetic_proof_truth (G : Arithmetic.FullArithmetic M N)
    (full : HasFullComprehension M) (p : SecondOrderArithmetic.Formula)
    (proof : theory ⊢ sentence p) :
    SecondOrderArithmetic.Valid (SecondOrderArithmetic.arithmeticOperations G) p := by
  apply (taggedModel_truth _ p).mp
  exact Theory.Proof.sound proof (arithmetic_taggedModel_valid G full)

end FregeanECA.Part2.ArithmeticEncoding
