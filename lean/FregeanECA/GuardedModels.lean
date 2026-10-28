import FregeanECA.Guarded

/-! Concrete models in both directions for the guarded first-order encoding.
The typing theory below consists of explicit first-order sentences. -/
namespace FregeanECA.Guarded
open FFL FFL.FirstOrder

universe u v w z

def HasSort (M : Type z) [Structure language M] (s : SortName) (x : M) : Prop :=
  Structure.rel (L := language) (.sort s) ![x]

class SortCorrect (M : Type z) [Structure language M] : Prop where
  inhabited : ∀ s, ∃ x : M, HasSort M s x
  constantK : HasSort M .object (Structure.func (L := language) .k ![])
  constantS : HasSort M .object (Structure.func (L := language) .s ![])
  application : ∀ a b, HasSort M .object a → HasSort M .object b →
    HasSort M .object (Structure.func (L := language) .app ![a, b])
  evaluation : ∀ f a, HasSort M .function f → HasSort M .object a →
    HasSort M .object (Structure.func (L := language) .eval ![f, a])
  representation : ∀ f, HasSort M .function f →
    HasSort M .object (Structure.func (L := language) .delta ![f])

private def sortAtom (s : SortName) (t : Semiterm language Empty n) :
    Semiformula language Empty n := .rel (.sort s) ![t]

def nonemptySortAxiom (s : SortName) : Sentence language :=
  .exs (sortAtom s (.bvar 0))

def typedKAxiom : Sentence language := sortAtom .object (.func .k ![])
def typedSAxiom : Sentence language := sortAtom .object (.func .s ![])

def typedApplicationAxiom : Sentence language :=
  .all (.all ((sortAtom .object (.bvar 1)) 🡒
    ((sortAtom .object (.bvar 0)) 🡒
      sortAtom .object (.func .app ![.bvar 1, .bvar 0]))))

def typedEvaluationAxiom : Sentence language :=
  .all (.all ((sortAtom .function (.bvar 1)) 🡒
    ((sortAtom .object (.bvar 0)) 🡒
      sortAtom .object (.func .eval ![.bvar 1, .bvar 0]))))

def typedRepresentationAxiom : Sentence language :=
  .all ((sortAtom .function (.bvar 0)) 🡒
    sortAtom .object (.func .delta ![.bvar 0]))

inductive SortAxiom : Sentence language → Prop where
  | nonempty (s) : SortAxiom (nonemptySortAxiom s)
  | constantK : SortAxiom typedKAxiom
  | constantS : SortAxiom typedSAxiom
  | application : SortAxiom typedApplicationAxiom
  | evaluation : SortAxiom typedEvaluationAxiom
  | representation : SortAxiom typedRepresentationAxiom

def sortTheory : Theory language := {φ | SortAxiom φ}

variable {M : Type z} [Structure language M]

private theorem eval_allE (φ : Semiformula language Empty (n + 1)) (b : Fin n → M) :
    Semiformula.Eval b Empty.elim (.all φ) ↔
      ∀ x, Semiformula.Eval (x :> b) Empty.elim φ := Iff.rfl

private theorem eval_exE (φ : Semiformula language Empty (n + 1)) (b : Fin n → M) :
    Semiformula.Eval b Empty.elim (.exs φ) ↔
      ∃ x, Semiformula.Eval (x :> b) Empty.elim φ := Iff.rfl

private theorem eval_impE (φ ψ : Semiformula language Empty n) (b : Fin n → M) :
    Semiformula.Eval b Empty.elim (φ 🡒 ψ) ↔
      (Semiformula.Eval b Empty.elim φ → Semiformula.Eval b Empty.elim ψ) := by
  rw [LogicalConnective.HomClass.map_imply]
  rfl

private theorem eval_sortAtom (s : SortName) (t : Semiterm language Empty n) (b : Fin n → M) :
    Semiformula.Eval b Empty.elim (sortAtom s t) ↔ HasSort M s (t.val b Empty.elim) := by
  change Structure.rel (L := language) (.sort s) _ ↔ Structure.rel (L := language) (.sort s) _
  have h : (fun i : Fin 1 => Semiterm.val b Empty.elim (![t] i)) = ![t.val b Empty.elim] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [h]

private theorem val_nilE (f : Func 0) (b : Fin n → M) :
    Semiterm.val b Empty.elim (.func f ![] : Semiterm language Empty n) =
      Structure.func (L := language) f ![] := by
  change Structure.func (L := language) f _ = _
  congr 1
  funext i
  exact Fin.elim0 i

private theorem val_oneE (f : Func 1) (t : Semiterm language Empty n) (b : Fin n → M) :
    Semiterm.val b Empty.elim (.func f ![t]) =
      Structure.func (L := language) f ![t.val b Empty.elim] := by
  change Structure.func (L := language) f _ = _
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem val_twoE (f : Func 2) (t r : Semiterm language Empty n) (b : Fin n → M) :
    Semiterm.val b Empty.elim (.func f ![t, r]) =
      Structure.func (L := language) f ![t.val b Empty.elim, r.val b Empty.elim] := by
  change Structure.func (L := language) f _ = _
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

@[simp] theorem realize_nonemptySortAxiom (s : SortName) :
    (nonemptySortAxiom s).Realize M ↔ ∃ x : M, HasSort M s x := by
  simp only [nonemptySortAxiom, Semiformula.Realize, eval_exE, eval_sortAtom,
    Semiterm.val_bvar, Matrix.cons_val_zero]

@[simp] theorem realize_typedKAxiom :
    typedKAxiom.Realize M ↔ HasSort M .object (Structure.func (L := language) .k ![]) := by
  simp only [typedKAxiom, Semiformula.Realize, eval_sortAtom, val_nilE]

@[simp] theorem realize_typedSAxiom :
    typedSAxiom.Realize M ↔ HasSort M .object (Structure.func (L := language) .s ![]) := by
  simp only [typedSAxiom, Semiformula.Realize, eval_sortAtom, val_nilE]

@[simp] theorem realize_typedApplicationAxiom :
    typedApplicationAxiom.Realize M ↔
      ∀ a b : M, HasSort M .object a → HasSort M .object b →
        HasSort M .object (Structure.func (L := language) .app ![a, b]) := by
  simp only [typedApplicationAxiom, Semiformula.Realize, eval_allE, eval_impE,
    eval_sortAtom, val_twoE, Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]

@[simp] theorem realize_typedEvaluationAxiom :
    typedEvaluationAxiom.Realize M ↔
      ∀ f a : M, HasSort M .function f → HasSort M .object a →
        HasSort M .object (Structure.func (L := language) .eval ![f, a]) := by
  simp only [typedEvaluationAxiom, Semiformula.Realize, eval_allE, eval_impE,
    eval_sortAtom, val_twoE, Semiterm.val_bvar, Matrix.cons_val_zero, Matrix.cons_val_one]

@[simp] theorem realize_typedRepresentationAxiom :
    typedRepresentationAxiom.Realize M ↔
      ∀ f : M, HasSort M .function f →
        HasSort M .object (Structure.func (L := language) .delta ![f]) := by
  simp only [typedRepresentationAxiom, Semiformula.Realize, eval_allE, eval_impE,
    eval_sortAtom, val_oneE, Semiterm.val_bvar, Matrix.cons_val_zero]

theorem models_sortTheory_iff [Nonempty M] :
    M↓[language] ⊧* sortTheory ↔ SortCorrect M := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s
      exact (realize_nonemptySortAxiom s).mp (h.models _ (SortAxiom.nonempty s))
    · exact realize_typedKAxiom.mp (h.models _ SortAxiom.constantK)
    · exact realize_typedSAxiom.mp (h.models _ SortAxiom.constantS)
    · exact realize_typedApplicationAxiom.mp (h.models _ SortAxiom.application)
    · exact realize_typedEvaluationAxiom.mp (h.models _ SortAxiom.evaluation)
    · exact realize_typedRepresentationAxiom.mp (h.models _ SortAxiom.representation)
  · intro h
    refine ⟨?_⟩
    intro φ hφ
    cases hφ with
    | nonempty s => exact (realize_nonemptySortAxiom s).mpr (h.inhabited s)
    | constantK => exact realize_typedKAxiom.mpr h.constantK
    | constantS => exact realize_typedSAxiom.mpr h.constantS
    | application => exact realize_typedApplicationAxiom.mpr h.application
    | evaluation => exact realize_typedEvaluationAxiom.mpr h.evaluation
    | representation => exact realize_typedRepresentationAxiom.mpr h.representation

def Sorted (M : Type z) [Structure language M] (s : SortName) :=
  {x : M // HasSort M s x}

instance sorted_nonempty [SortCorrect M] (s : SortName) : Nonempty (Sorted M s) := by
  obtain ⟨x, hx⟩ := SortCorrect.inhabited (M := M) s
  exact ⟨⟨x, hx⟩⟩

def extracted (M : Type z) [Structure language M] [SortCorrect M] :
    Functional.Interpretation (Sorted M .object) (Sorted M .function)
      (fun n => Sorted M (.relation n)) where
  applicative := {
    apply := fun a b => ⟨Structure.func (L := language) .app ![a.val, b.val],
      SortCorrect.application _ _ a.property b.property⟩
    constantK := ⟨Structure.func (L := language) .k ![], SortCorrect.constantK⟩
    constantS := ⟨Structure.func (L := language) .s ![], SortCorrect.constantS⟩
    satisfies := fun n p args => Structure.rel (L := language) (.member n)
      (Fin.cases p.val (fun i => (args i).val)) }
  eval := fun f a => ⟨Structure.func (L := language) .eval ![f.val, a.val],
    SortCorrect.evaluation _ _ f.property a.property⟩
  delta := fun f => ⟨Structure.func (L := language) .delta ![f.val],
    SortCorrect.representation _ f.property⟩

def extractedRealization (M : Type z) [Structure language M] [SortCorrect M]
    [Structure.Eq language M] : Realization (extracted M) M where
  object := Subtype.val
  function := Subtype.val
  relation := fun _ => Subtype.val
  object_injective := Subtype.val_injective
  function_injective := Subtype.val_injective
  relation_injective := fun _ => Subtype.val_injective
  object_guard := by intro x; exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.property⟩
  function_guard := by intro x; exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.property⟩
  relation_guard := by intro n x; exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact a.property⟩
  equality := by intro x y; exact Structure.eq_lang
  constantK := rfl
  constantS := rfl
  application := by intros; rfl
  evaluation := by intros; rfl
  representation := by intros; rfl
  membership := by intros; rfl

section Tagged

variable {D : Type u} {F : Type v} {R : Nat → Type w}

abbrev Tagged (D : Type u) (F : Type v) (R : Nat → Type w) := D ⊕ (F ⊕ Sigma R)

def tagObject (x : D) : Tagged D F R := Sum.inl x
def tagFunction (f : F) : Tagged D F R := Sum.inr (Sum.inl f)
def tagRelation (n : Nat) (p : R n) : Tagged D F R := Sum.inr (Sum.inr ⟨n, p⟩)

@[simp] theorem tagObject_inj {a b : D} :
    (tagObject a : Tagged D F R) = tagObject b ↔ a = b := Sum.inl.inj_iff
@[simp] theorem tagFunction_inj {a b : F} :
    (tagFunction a : Tagged D F R) = tagFunction b ↔ a = b := by simp [tagFunction]
@[simp] theorem tagRelation_inj {n : Nat} {a b : R n} :
    (tagRelation n a : Tagged D F R) = tagRelation n b ↔ a = b := by simp [tagRelation]

noncomputable def untagObject [Nonempty D] : Tagged D F R → D
  | .inl x => x
  | .inr _ => Classical.choice inferInstance

noncomputable def untagFunction [Nonempty F] : Tagged D F R → F
  | .inr (.inl f) => f
  | _ => Classical.choice inferInstance

@[instance_reducible] noncomputable def taggedStructure (typed : Functional.Interpretation D F R)
    [Nonempty D] [Nonempty F] : Structure language (Tagged D F R) where
  func := fun {_} f xs => match f with
    | .k => tagObject typed.applicative.constantK
    | .s => tagObject typed.applicative.constantS
    | .app => tagObject (typed.applicative.apply (untagObject (xs 0)) (untagObject (xs 1)))
    | .eval => tagObject (typed.eval (untagFunction (xs 0)) (untagObject (xs 1)))
    | .delta => tagObject (typed.delta (untagFunction (xs 0)))
  rel := fun {_} r xs => match r with
    | .equal => xs 0 = xs 1
    | .sort .object => ∃ x : D, tagObject x = xs 0
    | .sort .function => ∃ f : F, tagFunction f = xs 0
    | .sort (.relation n) => ∃ p : R n, tagRelation n p = xs 0
    | .member n => ∃ p : R n, tagRelation n p = xs 0 ∧
      ∃ args : Fin (n + 1) → D,
        (∀ i, tagObject (args i) = xs i.succ) ∧ typed.applicative.satisfies n p args

noncomputable def taggedRealization (typed : Functional.Interpretation D F R)
    [Nonempty D] [Nonempty F] :
    letI := taggedStructure typed
    Realization typed (Tagged D F R) := by
  letI := taggedStructure typed
  exact {
  object := tagObject
  function := tagFunction
  relation := tagRelation
  object_injective := fun _ _ h => tagObject_inj.mp h
  function_injective := fun _ _ h => tagFunction_inj.mp h
  relation_injective := fun _ _ _ h => tagRelation_inj.mp h
  object_guard := by intro x; rfl
  function_guard := by intro x; rfl
  relation_guard := by intro n x; rfl
  equality := by intro x y; rfl
  constantK := rfl
  constantS := rfl
  application := by intros; rfl
  evaluation := by intros; rfl
  representation := by intros; rfl
  membership := by
    intro n p args
    change (∃ q : R n, tagRelation n q = tagRelation n p ∧
      ∃ vals : Fin (n + 1) → D,
        (∀ i, tagObject (vals i) = tagObject (args i)) ∧
          typed.applicative.satisfies n q vals) ↔ _
    simp only [tagRelation_inj, tagObject_inj, exists_eq_left]
    constructor
    · rintro ⟨vals, same, holds⟩
      have : vals = args := funext same
      simpa [this] using holds
    · intro holds
      exact ⟨args, fun _ => rfl, holds⟩ }

theorem tagged_equality (typed : Functional.Interpretation D F R)
    [Nonempty D] [Nonempty F] :
    letI := taggedStructure typed
    Structure.Eq language (Tagged D F R) := by
  letI := taggedStructure typed
  exact ⟨fun _ _ => Iff.rfl⟩

theorem tagged_sortCorrect (typed : Functional.Interpretation D F R)
    [Nonempty D] [Nonempty F] [∀ n, Nonempty (R n)] :
    letI := taggedStructure typed
    SortCorrect (Tagged D F R) := by
  letI := taggedStructure typed
  constructor
  · intro s
    cases s with
    | object => exact ⟨tagObject typed.applicative.constantK, typed.applicative.constantK, rfl⟩
    | function => exact ⟨tagFunction (Classical.choice inferInstance), Classical.choice inferInstance, rfl⟩
    | relation n => exact ⟨tagRelation n (Classical.choice inferInstance), Classical.choice inferInstance, rfl⟩
  · exact ⟨typed.applicative.constantK, rfl⟩
  · exact ⟨typed.applicative.constantS, rfl⟩
  · intro a b _ _; exact ⟨_, rfl⟩
  · intro f a _ _; exact ⟨_, rfl⟩
  · intro f _; exact ⟨_, rfl⟩

end Tagged
end FregeanECA.Guarded
