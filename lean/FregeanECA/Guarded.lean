import FregeanECA.Syntax
import Foundation.FirstOrder.Basic.Eq

/-! A genuine first-order encoding of the sorted languages. Sorts are unary
guards in Foundation's ordinary language; equality remains actual equality.
The guarded quantifiers do not quantify over predicates as metatheoretic Prop.
-/
namespace FregeanECA.Guarded
open FFL FFL.FirstOrder

inductive SortName where
  | object | function | relation (arity : Nat)
  deriving DecidableEq

def SortName.code : SortName → Nat
  | .object => 0
  | .function => 1
  | .relation n => n + 2

def SortName.ofCode : Nat → SortName
  | 0 => .object
  | 1 => .function
  | n + 2 => .relation n

@[simp] theorem SortName.ofCode_code (s : SortName) : SortName.ofCode s.code = s := by
  cases s <;> rfl

inductive Func : Nat → Type where
  | k : Func 0
  | s : Func 0
  | app : Func 2
  | eval : Func 2
  | delta : Func 1

inductive Rel : Nat → Type where
  | equal : Rel 2
  | sort (s : SortName) : Rel 1
  | member (n : Nat) : Rel (n + 2)

def language : Language where
  Func := Func
  Rel := Rel

instance : language.Eq := ⟨Rel.equal⟩

abbrev Term (n : Nat) := Semiterm language Nat n
abbrev Formula (n : Nat) := Semiformula language Nat n
abbrev Map (n : Nat) := SortName → Nat → Term n

def variableCode (s : SortName) (i : Nat) : Nat := Nat.pair s.code i

def initialMap : Map 0 := fun s i => .fvar (variableCode s i)

def bind (s : SortName) (m : Map n) : Map (n + 1) := fun t i =>
  if t = s then match i with
    | 0 => .bvar 0
    | j + 1 => Rew.bShift (m t j)
  else Rew.bShift (m t i)

def eqn (a b : Term n) : Formula n := .rel .equal ![a, b]
def guard (s : SortName) (a : Term n) : Formula n := .rel (.sort s) ![a]

def term (m : Map n) : Functional.Term → Term n
  | .var i => m .object i
  | .constantK => .func .k ![]
  | .constantS => .func .s ![]
  | .app f x => .func .app ![term m f, term m x]
  | .eval f x => .func .eval ![m .function f, term m x]
  | .delta f => .func .delta ![m .function f]

def formula (m : Map n) : Functional.Formula → Formula n
  | .equal a b => eqn (term m a) (term m b)
  | .relation arity index arguments =>
      .rel (.member arity) (Fin.cases (m (.relation arity) index) (fun i => term m (arguments i)))
  | .relationEqual arity a b => eqn (m (.relation arity) a) (m (.relation arity) b)
  | .functionEqual a b => eqn (m .function a) (m .function b)
  | .falsum => .falsum
  | .implies a b => (formula m a) 🡒 (formula m b)
  | .conjunction a b => .and (formula m a) (formula m b)
  | .disjunction a b => .or (formula m a) (formula m b)
  | .existsObject body => .exs (.and (guard .object (.bvar 0)) (formula (bind .object m) body))
  | .forallObject body => .all ((guard .object (.bvar 0)) 🡒 (formula (bind .object m) body))
  | .existsFunction body => .exs (.and (guard .function (.bvar 0)) (formula (bind .function m) body))
  | .forallFunction body => .all ((guard .function (.bvar 0)) 🡒 (formula (bind .function m) body))
  | .existsPredicate arity body => .exs (.and (guard (.relation arity) (.bvar 0))
      (formula (bind (.relation arity) m) body))
  | .forallPredicate arity body => .all ((guard (.relation arity) (.bvar 0)) 🡒
      (formula (bind (.relation arity) m) body))


universe u v w z

variable {D : Type u} {F : Type v} {R : Nat → Type w} {M : Type z}

/-- An exact realization of a sorted interpretation inside an ordinary structure.
No disjointness of the images is needed for semantic preservation. -/
structure Realization (typed : Functional.Interpretation D F R) (M : Type z)
    [Structure language M] where
  object : D → M
  function : F → M
  relation : (arity : Nat) → R arity → M
  object_injective : Function.Injective object
  function_injective : Function.Injective function
  relation_injective : ∀ arity, Function.Injective (relation arity)
  object_guard : ∀ (x : M), Structure.rel (L := language) (.sort .object) ![x] ↔ ∃ d, object d = x
  function_guard : ∀ (x : M), Structure.rel (L := language) (.sort .function) ![x] ↔ ∃ f, function f = x
  relation_guard : ∀ arity (x : M),
    Structure.rel (L := language) (.sort (.relation arity)) ![x] ↔ ∃ p, relation arity p = x
  equality : ∀ (x y : M), Structure.rel (L := language) .equal ![x, y] ↔ x = y
  constantK : Structure.func (L := language) (M := M) .k ![] = object typed.applicative.constantK
  constantS : Structure.func (L := language) (M := M) .s ![] = object typed.applicative.constantS
  application : ∀ a b, Structure.func (L := language) .app ![object a, object b] =
    object (typed.applicative.apply a b)
  evaluation : ∀ f a, Structure.func (L := language) .eval ![function f, object a] =
    object (typed.eval f a)
  representation : ∀ f, Structure.func (L := language) .delta ![function f] =
    object (typed.delta f)
  membership : ∀ arity (p : R arity) (arguments : Fin (arity + 1) → D),
    Structure.rel (L := language) (.member arity)
      (Fin.cases (relation arity p) (fun i => object (arguments i))) ↔
        typed.applicative.satisfies arity p arguments

variable {typed : Functional.Interpretation D F R} [Structure language M]

/-- The Foundation valuations realize all variables in a sorted assignment. -/
structure Maps (real : Realization typed M) (m : Map n) (bound : Fin n → M)
    (free : Nat → M) (objects : Nat → D) (functions : Nat → F)
    (predicates : Positive.PredicateAssignment R) : Prop where
  objects : ∀ i, (m .object i).val bound free = real.object (objects i)
  functions : ∀ i, (m .function i).val bound free = real.function (functions i)
  predicates : ∀ arity i, (m (.relation arity) i).val bound free =
    real.relation arity (predicates arity i)

theorem Maps.bind_object {real : Realization typed M} {m : Map n}
    {bound : Fin n → M} {free : Nat → M} {objects : Nat → D} {functions : Nat → F}
    {predicates : Positive.PredicateAssignment R}
    (compatible : Maps real m bound free objects functions predicates) (value : D) :
    Maps real (bind .object m) (real.object value :> bound) free
      (Positive.pushObject objects value) functions predicates := by
  constructor
  · intro i
    cases i <;> simp [bind, Positive.pushObject, compatible.objects]
  · intro i
    simp [bind, compatible.functions]
  · intro arity i
    simp [bind, compatible.predicates]

theorem Maps.bind_function {real : Realization typed M} {m : Map n}
    {bound : Fin n → M} {free : Nat → M} {objects : Nat → D} {functions : Nat → F}
    {predicates : Positive.PredicateAssignment R}
    (compatible : Maps real m bound free objects functions predicates) (value : F) :
    Maps real (bind .function m) (real.function value :> bound) free
      objects (Positive.pushObject functions value) predicates := by
  constructor
  · intro i
    simp [bind, compatible.objects]
  · intro i
    cases i <;> simp [bind, Positive.pushObject, compatible.functions]
  · intro arity i
    simp [bind, compatible.predicates]

theorem Maps.bind_predicate {real : Realization typed M} {m : Map n}
    {bound : Fin n → M} {free : Nat → M} {objects : Nat → D} {functions : Nat → F}
    {predicates : Positive.PredicateAssignment R}
    (compatible : Maps real m bound free objects functions predicates)
    (arity : Nat) (value : R arity) :
    Maps real (bind (.relation arity) m) (real.relation arity value :> bound) free
      objects functions (Positive.pushPredicate predicates arity value) := by
  constructor
  · intro i
    simp [bind, compatible.objects]
  · intro i
    simp [bind, compatible.functions]
  · intro other i
    by_cases same : other = arity
    · subst other
      cases i <;> simp [bind, Positive.pushPredicate, compatible.predicates]
    · simp [bind, Positive.pushPredicate, same, compatible.predicates]


theorem values_nil (bound : Fin n → M) (free : Nat → M) :
    (fun i : Fin 0 => Semiterm.val bound free ((![] : Fin 0 → Term n) i)) = ![] := by
  funext i
  exact Fin.elim0 i

theorem values_one (a : Term n) (bound : Fin n → M) (free : Nat → M) :
    (fun i : Fin 1 => Semiterm.val bound free (![a] i)) = ![a.val bound free] := by
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem values_two (a b : Term n) (bound : Fin n → M) (free : Nat → M) :
    (fun i : Fin 2 => Semiterm.val bound free (![a, b] i)) =
      ![a.val bound free, b.val bound free] := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i


theorem term_value (real : Realization typed M) (t : Functional.Term)
    (compatible : Maps real m bound free objects functions predicates) :
    (term m t).val bound free = real.object (t.value typed objects functions) := by
  induction t with
  | var i => exact compatible.objects i
  | constantK =>
      change Structure.func (L := language) .k _ = _
      rw [values_nil]
      exact real.constantK
  | constantS =>
      change Structure.func (L := language) .s _ = _
      rw [values_nil]
      exact real.constantS
  | app a b aIH bIH =>
      change Structure.func (L := language) .app _ = _
      rw [values_two, aIH, bIH]
      exact real.application _ _
  | eval f a aIH =>
      change Structure.func (L := language) .eval _ = _
      rw [values_two, compatible.functions, aIH]
      exact real.evaluation _ _
  | delta f =>
      change Structure.func (L := language) .delta _ = _
      rw [values_one, compatible.functions]
      exact real.representation _

@[simp] theorem eval_eqn (real : Realization typed M) (a b : Term n)
    (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (eqn a b) ↔ a.val bound free = b.val bound free := by
  change Structure.rel (L := language) .equal _ ↔ _
  rw [values_two]
  exact real.equality _ _

@[simp] theorem eval_guard (s : SortName) (a : Term n) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (guard s a) ↔
      Structure.rel (L := language) (.sort s) ![a.val bound free] := by
  change Structure.rel (L := language) (.sort s) _ ↔ _
  rw [values_one]


@[simp] theorem eval_and (a b : Formula n) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (.and a b) ↔
      Semiformula.Eval bound free a ∧ Semiformula.Eval bound free b := Iff.rfl

@[simp] theorem eval_or (a b : Formula n) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (.or a b) ↔
      Semiformula.Eval bound free a ∨ Semiformula.Eval bound free b := Iff.rfl

@[simp] theorem eval_implies (a b : Formula n) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (a 🡒 b) ↔
      (Semiformula.Eval bound free a → Semiformula.Eval bound free b) := by
  rw [LogicalConnective.HomClass.map_imply]
  rfl

@[simp] theorem eval_forall (a : Formula (n + 1)) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (.all a) ↔
      ∀ x, Semiformula.Eval (x :> bound) free a := Iff.rfl

@[simp] theorem eval_exists (a : Formula (n + 1)) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (.exs a) ↔
      ∃ x, Semiformula.Eval (x :> bound) free a := Iff.rfl


/-- Complete satisfaction preservation, including primitive equality on every sort. -/
theorem formula_truth (real : Realization typed M) (φ : Functional.Formula) :
    ∀ {n} (m : Map n) (bound : Fin n → M) (free : Nat → M)
      (objects : Nat → D) (functions : Nat → F) (predicates : Positive.PredicateAssignment R),
      Maps real m bound free objects functions predicates →
      (Semiformula.Eval bound free (formula m φ) ↔
        φ.truth typed objects functions predicates) := by
  induction φ with
  | equal a b =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, Functional.Formula.truth, eval_eqn real,
        term_value real a compatible, term_value real b compatible, real.object_injective.eq_iff]
  | relation arity index arguments =>
      intro n m bound free objects functions predicates compatible
      change Structure.rel (L := language) (.member arity)
        (fun i : Fin (arity + 2) => Semiterm.val bound free (Fin.cases
          (m (.relation arity) index) (fun j => term m (arguments j)) i)) ↔ _
      have values : (fun i : Fin (arity + 2) => Semiterm.val bound free (Fin.cases (m (.relation arity) index)
          (fun j => term m (arguments j)) i)) =
          Fin.cases (real.relation arity (predicates arity index))
            (fun j => real.object ((arguments j).value typed objects functions)) := by
        funext i
        exact Fin.cases (compatible.predicates arity index)
          (fun j => term_value real (arguments j) compatible) i
      rw [values]
      exact real.membership arity (predicates arity index) _
  | relationEqual arity a b =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, Functional.Formula.truth, eval_eqn real,
        compatible.predicates, (real.relation_injective arity).eq_iff]
  | functionEqual a b =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, Functional.Formula.truth, eval_eqn real,
        compatible.functions, real.function_injective.eq_iff]
  | falsum => intros; rfl
  | implies a b aIH bIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_implies, Functional.Formula.truth,
        aIH _ _ _ _ _ _ compatible, bIH _ _ _ _ _ _ compatible]
  | conjunction a b aIH bIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_and, Functional.Formula.truth,
        aIH _ _ _ _ _ _ compatible, bIH _ _ _ _ _ _ compatible]
  | disjunction a b aIH bIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_or, Functional.Formula.truth,
        aIH _ _ _ _ _ _ compatible, bIH _ _ _ _ _ _ compatible]
  | existsObject body bodyIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_exists, eval_and, eval_guard, Semiterm.val_bvar,
        Matrix.cons_val_zero, real.object_guard, Functional.Formula.truth]
      constructor
      · rintro ⟨x, ⟨value, rfl⟩, holds⟩
        exact ⟨value, (bodyIH _ _ _ _ _ _ (compatible.bind_object value)).mp holds⟩
      · rintro ⟨value, holds⟩
        exact ⟨real.object value, ⟨value, rfl⟩,
          (bodyIH _ _ _ _ _ _ (compatible.bind_object value)).mpr holds⟩
  | forallObject body bodyIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_forall, eval_implies, eval_guard, Semiterm.val_bvar,
        Matrix.cons_val_zero, real.object_guard, Functional.Formula.truth]
      constructor
      · intro holds value
        exact (bodyIH _ _ _ _ _ _ (compatible.bind_object value)).mp
          (holds (real.object value) ⟨value, rfl⟩)
      · intro holds x witness
        obtain ⟨value, rfl⟩ := witness
        exact (bodyIH _ _ _ _ _ _ (compatible.bind_object value)).mpr (holds value)
  | existsFunction body bodyIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_exists, eval_and, eval_guard, Semiterm.val_bvar,
        Matrix.cons_val_zero, real.function_guard, Functional.Formula.truth]
      constructor
      · rintro ⟨x, ⟨value, rfl⟩, holds⟩
        exact ⟨value, (bodyIH _ _ _ _ _ _ (compatible.bind_function value)).mp holds⟩
      · rintro ⟨value, holds⟩
        exact ⟨real.function value, ⟨value, rfl⟩,
          (bodyIH _ _ _ _ _ _ (compatible.bind_function value)).mpr holds⟩
  | forallFunction body bodyIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_forall, eval_implies, eval_guard, Semiterm.val_bvar,
        Matrix.cons_val_zero, real.function_guard, Functional.Formula.truth]
      constructor
      · intro holds value
        exact (bodyIH _ _ _ _ _ _ (compatible.bind_function value)).mp
          (holds (real.function value) ⟨value, rfl⟩)
      · intro holds x witness
        obtain ⟨value, rfl⟩ := witness
        exact (bodyIH _ _ _ _ _ _ (compatible.bind_function value)).mpr (holds value)
  | existsPredicate arity body bodyIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_exists, eval_and, eval_guard, Semiterm.val_bvar,
        Matrix.cons_val_zero, real.relation_guard, Functional.Formula.truth]
      constructor
      · rintro ⟨x, ⟨value, rfl⟩, holds⟩
        exact ⟨value, (bodyIH _ _ _ _ _ _ (compatible.bind_predicate arity value)).mp holds⟩
      · rintro ⟨value, holds⟩
        exact ⟨real.relation arity value, ⟨value, rfl⟩,
          (bodyIH _ _ _ _ _ _ (compatible.bind_predicate arity value)).mpr holds⟩
  | forallPredicate arity body bodyIH =>
      intro n m bound free objects functions predicates compatible
      simp only [formula, eval_forall, eval_implies, eval_guard, Semiterm.val_bvar,
        Matrix.cons_val_zero, real.relation_guard, Functional.Formula.truth]
      constructor
      · intro holds value
        exact (bodyIH _ _ _ _ _ _ (compatible.bind_predicate arity value)).mp
          (holds (real.relation arity value) ⟨value, rfl⟩)
      · intro holds x witness
        obtain ⟨value, rfl⟩ := witness
        exact (bodyIH _ _ _ _ _ _ (compatible.bind_predicate arity value)).mpr (holds value)


@[simp] theorem SortName.code_ofCode (i : Nat) : (SortName.ofCode i).code = i := by
  cases i with
  | zero => rfl
  | succ i => cases i <;> rfl

def encodedAssignment (real : Realization typed M) (objects : Nat → D)
    (functions : Nat → F) (predicates : Positive.PredicateAssignment R) (i : Nat) : M :=
  match SortName.ofCode (Nat.unpair i).1 with
  | .object => real.object (objects (Nat.unpair i).2)
  | .function => real.function (functions (Nat.unpair i).2)
  | .relation arity => real.relation arity (predicates arity (Nat.unpair i).2)

@[simp] theorem encodedAssignment_object (real : Realization typed M) (objects : Nat → D)
    (functions : Nat → F) (predicates : Positive.PredicateAssignment R) (i : Nat) :
    encodedAssignment real objects functions predicates (variableCode .object i) =
      real.object (objects i) := by
  simp [encodedAssignment, variableCode, SortName.code, SortName.ofCode, Nat.unpair_pair]

@[simp] theorem encodedAssignment_function (real : Realization typed M) (objects : Nat → D)
    (functions : Nat → F) (predicates : Positive.PredicateAssignment R) (i : Nat) :
    encodedAssignment real objects functions predicates (variableCode .function i) =
      real.function (functions i) := by
  simp [encodedAssignment, variableCode, SortName.code, SortName.ofCode, Nat.unpair_pair]

@[simp] theorem encodedAssignment_relation (real : Realization typed M) (objects : Nat → D)
    (functions : Nat → F) (predicates : Positive.PredicateAssignment R) (arity i : Nat) :
    encodedAssignment real objects functions predicates (variableCode (.relation arity) i) =
      real.relation arity (predicates arity i) := by
  simp [encodedAssignment, variableCode, SortName.code, SortName.ofCode, Nat.unpair_pair]

theorem encodedAssignment_maps (real : Realization typed M) (objects : Nat → D)
    (functions : Nat → F) (predicates : Positive.PredicateAssignment R) :
    Maps real initialMap ![] (encodedAssignment real objects functions predicates)
      objects functions predicates := by
  constructor <;> intros <;> simp [initialMap]

theorem encodedAssignment_guarded (real : Realization typed M) (objects : Nat → D)
    (functions : Nat → F) (predicates : Positive.PredicateAssignment R) (i : Nat) :
    Structure.rel (L := language) (.sort (SortName.ofCode (Nat.unpair i).1))
      ![encodedAssignment real objects functions predicates i] := by
  cases h : SortName.ofCode (Nat.unpair i).1 with
  | object =>
      simp only [encodedAssignment, h]
      exact (real.object_guard _).mpr ⟨_, rfl⟩
  | function =>
      simp only [encodedAssignment, h]
      exact (real.function_guard _).mpr ⟨_, rfl⟩
  | relation arity =>
      simp only [encodedAssignment, h]
      exact (real.relation_guard _ _).mpr ⟨_, rfl⟩

/-- Only free variables actually present in the encoded formula are guarded. -/
def freeGuards : List Nat → Formula 0
  | [] => .verum
  | i :: rest =>
      .and (guard (SortName.ofCode (Nat.unpair i).1) (.fvar i)) (freeGuards rest)

theorem freeGuards_truth (names : List Nat) (free : Nat → M) :
    Semiformula.Evalf free (freeGuards names) ↔
      ∀ i ∈ names, Structure.rel (L := language)
        (.sort (SortName.ofCode (Nat.unpair i).1)) ![free i] := by
  induction names with
  | nil => change True ↔ _; simp
  | cons i rest ih =>
      simp only [freeGuards, eval_and, eval_guard, Semiterm.val_fvar]
      simpa only [List.mem_cons, forall_eq_or_imp] using and_congr Iff.rfl ih

/-- Universal closure of the guarded encoding, a genuine Foundation sentence. -/
noncomputable def sentence (φ : Functional.Formula) : Sentence language :=
  ((freeGuards (formula initialMap φ).freeVariables.toList) 🡒 formula initialMap φ).univCl

private noncomputable def recover {X : Type*} (embed : X → M) (fallback : X) (x : M) : X := by
  classical
  exact if witness : ∃ value, embed value = x then Classical.choose witness else fallback

omit [Structure language M] in
private theorem recover_spec {X : Type*} (embed : X → M) (fallback : X) (x : M)
    (witness : ∃ value, embed value = x) : embed (recover embed fallback x) = x := by
  simp only [recover, dif_pos witness]
  exact Classical.choose_spec witness

/-- Fill irrelevant or incorrectly sorted free variables with typed defaults;
guarded variables are preserved exactly. -/
theorem guarded_assignment_recovery (real : Realization typed M)
    (function_nonempty : Nonempty F) (relation_nonempty : ∀ arity, Nonempty (R arity))
    (free : Nat → M) :
    ∃ (objects : Nat → D) (functions : Nat → F) (predicates : Positive.PredicateAssignment R),
      ∀ i, Structure.rel (L := language) (.sort (SortName.ofCode (Nat.unpair i).1)) ![free i] →
        encodedAssignment real objects functions predicates i = free i := by
  classical
  let objects : Nat → D := fun j =>
    recover real.object typed.applicative.constantK (free (variableCode .object j))
  let functions : Nat → F := fun j =>
    recover real.function (Classical.choice function_nonempty) (free (variableCode .function j))
  let predicates : Positive.PredicateAssignment R := fun arity j =>
    recover (real.relation arity) (Classical.choice (relation_nonempty arity))
      (free (variableCode (.relation arity) j))
  refine ⟨objects, functions, predicates, ?_⟩
  intro i guarded
  have code : variableCode (SortName.ofCode (Nat.unpair i).1) (Nat.unpair i).2 = i := by
    simp only [variableCode, SortName.code_ofCode, Nat.pair_unpair]
  cases kind : SortName.ofCode (Nat.unpair i).1 with
  | object =>
      have code' : variableCode .object (Nat.unpair i).2 = i := by simpa [kind] using code
      have witness : ∃ x, real.object x = free i :=
        (real.object_guard _).mp (by simpa [kind] using guarded)
      simp only [encodedAssignment, kind, objects, code']
      exact recover_spec _ _ _ witness
  | function =>
      have code' : variableCode .function (Nat.unpair i).2 = i := by simpa [kind] using code
      have witness : ∃ x, real.function x = free i :=
        (real.function_guard _).mp (by simpa [kind] using guarded)
      simp only [encodedAssignment, kind, functions, code']
      exact recover_spec _ _ _ witness
  | relation arity =>
      have code' : variableCode (.relation arity) (Nat.unpair i).2 = i := by simpa [kind] using code
      have witness : ∃ x, real.relation arity x = free i :=
        (real.relation_guard _ _).mp (by simpa [kind] using guarded)
      simp only [encodedAssignment, kind, predicates, code']
      exact recover_spec _ _ _ witness

/-- The closed first-order sentence expresses validity under every sorted assignment. -/
theorem sentence_truth (real : Realization typed M)
    (function_nonempty : Nonempty F) (relation_nonempty : ∀ arity, Nonempty (R arity))
    (φ : Functional.Formula) :
    Semiformula.Realize M (sentence φ) ↔
      ∀ (objects : Nat → D) (functions : Nat → F) (predicates : Positive.PredicateAssignment R),
        φ.truth typed objects functions predicates := by
  let : Nonempty M := ⟨real.object typed.applicative.constantK⟩
  rw [sentence, Semiformula.eval_univCl]
  constructor
  · intro holds objects functions predicates
    have guarded : Semiformula.Evalf (encodedAssignment real objects functions predicates)
        (freeGuards (formula initialMap φ).freeVariables.toList) :=
      (freeGuards_truth _ _).mpr (fun i _ => encodedAssignment_guarded real objects functions predicates i)
    have encoded := (eval_implies _ _ ![] _).mp
      (holds (encodedAssignment real objects functions predicates)) guarded
    exact (formula_truth real φ _ _ _ _ _ _
      (encodedAssignment_maps real objects functions predicates)).mp encoded
  · intro holds free
    apply (eval_implies _ _ ![] free).mpr
    intro guarded
    obtain ⟨objects, functions, predicates, recovered⟩ :=
      guarded_assignment_recovery real function_nonempty relation_nonempty free
    have encoded : Semiformula.Evalf (encodedAssignment real objects functions predicates)
        (formula initialMap φ) :=
      (formula_truth real φ _ _ _ _ _ _
        (encodedAssignment_maps real objects functions predicates)).mpr
          (holds objects functions predicates)
    apply (Semiformula.eval_iff_of_funEqOn (formula initialMap φ) ?_).mp encoded
    intro i present
    apply recovered
    exact (freeGuards_truth _ _).mp guarded i (by simpa using present)


end FregeanECA.Guarded
