import FregeanECA.Part2.ArithmeticEncoding

/-!
Native two-sorted arithmetic semantics and extraction from arbitrary models of
the existing guarded Z2 theory. The number carrier is not assumed to be `Nat`,
and the set carrier contains only sets available in the source model.

This is infrastructure for a reverse interpretation, not that interpretation.
-/

namespace FregeanECA.Research.Z2Reverse.ArithmeticModel

open FFL FFL.FirstOrder
open Part2
open ArithmeticEncoding

universe u v

structure ArithmeticStructure (N : Type u) (S : Type v) where
  zero : N
  successor : N → N
  add : N → N → N
  multiply : N → N → N
  member : N → S → Prop

def termValue (A : ArithmeticStructure N S) (numbers : Nat → N) :
    SecondOrderArithmetic.Term → N
  | .var i => numbers i
  | .zero => A.zero
  | .successor t => A.successor (termValue A numbers t)
  | .add s t => A.add (termValue A numbers s) (termValue A numbers t)
  | .multiply s t => A.multiply (termValue A numbers s) (termValue A numbers t)

def truth (A : ArithmeticStructure N S) (numbers : Nat → N) (sets : Nat → S) :
    SecondOrderArithmetic.Formula → Prop
  | .equal s t => termValue A numbers s = termValue A numbers t
  | .member t i => A.member (termValue A numbers t) (sets i)
  | .setEqual i j => sets i = sets j
  | .falsum => False
  | .implies p q => truth A numbers sets p → truth A numbers sets q
  | .conjunction p q => truth A numbers sets p ∧ truth A numbers sets q
  | .disjunction p q => truth A numbers sets p ∨ truth A numbers sets q
  | .existsNumber p => ∃ x, truth A (Positive.pushObject numbers x) sets p
  | .forallNumber p => ∀ x, truth A (Positive.pushObject numbers x) sets p
  | .existsSet p => ∃ X, truth A numbers (Positive.pushObject sets X) p
  | .forallSet p => ∀ X, truth A numbers (Positive.pushObject sets X) p

def ModelsZ2 (A : ArithmeticStructure N S) : Prop :=
  ∀ p, SecondOrderArithmetic.Axiom p → ∀ numbers sets, truth A numbers sets p

section Extraction

variable (M : Type u) [Structure language M]

def HasSort (kind : SortName) (x : M) : Prop :=
  Structure.rel (L := language) (.sort kind) ![x]

abbrev Number := {x : M // HasSort M .number x}
abbrev SetObject := {x : M // HasSort M .set x}

structure SortCorrect : Prop where
  inhabited : ∀ kind, ∃ x : M, HasSort M kind x
  zero : HasSort M .number (Structure.func (L := language) .zero ![])
  successor : ∀ x, HasSort M .number x →
    HasSort M .number (Structure.func (L := language) .successor ![x])
  binary : ∀ (f : Func 2) x y, HasSort M .number x → HasSort M .number y →
    HasSort M .number (Structure.func (L := language) f ![x,y])

def extracted (typing : SortCorrect M) : ArithmeticStructure (Number M) (SetObject M) where
  zero := ⟨_, typing.zero⟩
  successor x := ⟨_, typing.successor x.val x.property⟩
  add x y := ⟨_, typing.binary .add x.val y.val x.property y.property⟩
  multiply x y := ⟨_, typing.binary .multiply x.val y.val x.property y.property⟩
  member x X := Structure.rel (L := language) .member ![x.val,X.val]

private theorem values_nil (bound : Fin n → M) (free : Nat → M) :
    (fun i : Fin 0 => Semiterm.val bound free ((![] : Fin 0 → Term n) i)) = ![] := by
  funext i; exact Fin.elim0 i

private theorem values_one (a : Term n) (bound : Fin n → M) (free : Nat → M) :
    (fun i : Fin 1 => Semiterm.val bound free (![a] i)) = ![a.val bound free] := by
  funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i

private theorem values_two (a b : Term n) (bound : Fin n → M) (free : Nat → M) :
    (fun i : Fin 2 => Semiterm.val bound free (![a,b] i)) = ![a.val bound free,b.val bound free] := by
  funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

private theorem eval_guard (kind : SortName) (a : Term n)
    (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (guard kind a) ↔ HasSort M kind (a.val bound free) := by
  change Structure.rel (L := language) (.sort kind) _ ↔ _
  rw [values_one]
  rfl

private theorem eval_implies (a b : Formula n) (bound : Fin n → M) (free : Nat → M) :
    Semiformula.Eval bound free (a 🡒 b) ↔
      (Semiformula.Eval bound free a → Semiformula.Eval bound free b) := by
  rw [LogicalConnective.HomClass.map_imply]; rfl

private theorem val_zero (bound : Fin n → M) (free : Nat → M) :
    (.func .zero ![] : Term n).val bound free = Structure.func (L := language) .zero ![] := by
  change Structure.func (L := language) .zero _ = _
  rw [values_nil]

private theorem val_successor (a : Term n) (bound : Fin n → M) (free : Nat → M) :
    (.func .successor ![a] : Term n).val bound free =
      Structure.func (L := language) .successor ![a.val bound free] := by
  change Structure.func (L := language) .successor _ = _
  rw [values_one]

private theorem val_binary (f : Func 2) (a b : Term n) (bound : Fin n → M) (free : Nat → M) :
    (.func f ![a,b] : Term n).val bound free =
      Structure.func (L := language) f ![a.val bound free,b.val bound free] := by
  change Structure.func (L := language) f _ = _
  rw [values_two]

theorem sortCorrect_of_model [Nonempty M] (model : M↓[language] ⊧* theory) : SortCorrect M := by
  have structural : ∀ p, StructuralAxiom p → p.Realize M := by
    intro p hp
    exact model.models_set (Or.inl (Or.inr hp))
  constructor
  · intro kind
    have h := structural _ (StructuralAxiom.nonempty kind)
    rw [nonemptySortAxiom, Semiformula.eval_univCl] at h
    let free : Nat → M := fun _ => Classical.choice (inferInstance : Nonempty M)
    have h' : ∃ x : M, Semiformula.Eval (x :> ![]) free (guard kind (.bvar 0)) := h free
    obtain ⟨x,hx⟩ := h'
    exact ⟨x, (eval_guard M kind (.bvar 0) (x :> ![]) free).mp hx⟩
  · have h := structural _ StructuralAxiom.zero
    rw [zeroTyping, Semiformula.eval_univCl] at h
    simpa only [eval_guard, val_zero] using
      h (fun _ => Classical.choice (inferInstance : Nonempty M))
  · intro x hx
    have h := structural _ StructuralAxiom.successor
    rw [successorTyping, Semiformula.eval_univCl] at h
    have h' := (eval_implies M _ _ ![] (fun _ => x)).mp (h (fun _ => x))
    have hx' : Semiformula.Eval ![] (fun _ => x) (guard .number (.fvar 0)) :=
      (eval_guard M _ _ _ _).mpr hx
    simpa only [eval_guard, val_successor, Semiterm.val_fvar] using h' hx'
  · intro f x y hx hy
    have h := structural _ (StructuralAxiom.binary f)
    rw [binaryTyping, Semiformula.eval_univCl] at h
    let free : Nat → M := fun i => if i = 0 then x else y
    have h' := (eval_implies M _ _ ![] free).mp (h free)
    have h'' := (eval_implies M _ _ ![] free).mp (h' (by simpa [eval_guard, free] using hx))
    have hy' : Semiformula.Eval ![] free (guard .number (.fvar 1)) := by
      simpa [eval_guard, free] using hy
    simpa only [eval_guard, val_binary, Semiterm.val_fvar,
      free, if_pos rfl, if_neg (by decide : ¬ (1 : Nat) = 0), if_true] using h'' hy'

variable {M}

structure Maps (m : Map n) (bound : Fin n → M) (free : Nat → M)
    (numbers : Nat → Number M) (sets : Nat → SetObject M) : Prop where
  numbers : ∀ i, (m .number i).val bound free = (numbers i).val
  sets : ∀ i, (m .set i).val bound free = (sets i).val

theorem Maps.bind_number {m : Map n} {bound : Fin n → M} {free : Nat → M}
    {numbers : Nat → Number M} {sets : Nat → SetObject M}
    (h : Maps m bound free numbers sets) (x : Number M) :
    Maps (bind .number m) (x.val :> bound) free (Positive.pushObject numbers x) sets := by
  constructor
  · intro i; cases i <;> simp [ArithmeticEncoding.bind, Positive.pushObject, h.numbers]
  · intro i; simp [ArithmeticEncoding.bind, h.sets]

theorem Maps.bind_set {m : Map n} {bound : Fin n → M} {free : Nat → M}
    {numbers : Nat → Number M} {sets : Nat → SetObject M}
    (h : Maps m bound free numbers sets) (X : SetObject M) :
    Maps (bind .set m) (X.val :> bound) free numbers (Positive.pushObject sets X) := by
  constructor
  · intro i; simp [ArithmeticEncoding.bind, h.numbers]
  · intro i; cases i <;> simp [ArithmeticEncoding.bind, Positive.pushObject, h.sets]

theorem term_value (typing : SortCorrect M) (t : SecondOrderArithmetic.Term)
    {m : Map n} {bound : Fin n → M} {free : Nat → M}
    {numbers : Nat → Number M} {sets : Nat → SetObject M}
    (h : Maps m bound free numbers sets) :
    (term m t).val bound free = (termValue (extracted M typing) numbers t).val := by
  induction t with
  | var i => exact h.numbers i
  | zero =>
      change Structure.func (L := language) .zero _ = _
      rw [values_nil]
      rfl
  | successor t ih =>
      change Structure.func (L := language) .successor _ = _
      rw [values_one, ih]
      rfl
  | add s t hs ht =>
      change Structure.func (L := language) .add _ = _
      rw [values_two, hs, ht]
      rfl
  | multiply s t hs ht =>
      change Structure.func (L := language) .multiply _ = _
      rw [values_two, hs, ht]
      rfl

end Extraction
end FregeanECA.Research.Z2Reverse.ArithmeticModel
