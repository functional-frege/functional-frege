import FregeanECA.Part2.SecondOrderArithmetic

/-! Finite guards on precisely the free number-variable prefix. Irrelevant
target object variables are not assumed to lie in the interpreted number domain. -/
namespace FregeanECA.Part2.SecondOrderArithmetic
open Positive Arithmetic
universe u v
variable {D : Type u} {R : Nat → Type v}

def Term.numberBound : Term → Nat
  | .var i => i+1
  | .zero => 0
  | .successor t => t.numberBound
  | .add s t => max s.numberBound t.numberBound
  | .multiply s t => max s.numberBound t.numberBound

def Formula.numberBound : Formula → Nat
  | .equal s t => max s.numberBound t.numberBound
  | .member t _ => t.numberBound
  | .setEqual _ _ => 0
  | .falsum => 0
  | .implies p q => max p.numberBound q.numberBound
  | .conjunction p q => max p.numberBound q.numberBound
  | .disjunction p q => max p.numberBound q.numberBound
  | .existsNumber p => p.numberBound - 1
  | .forallNumber p => p.numberBound - 1
  | .existsSet p => p.numberBound
  | .forallSet p => p.numberBound

theorem Term.graph_truth_partial {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (addition multiplication : Nat)
    (predicates : PredicateAssignment R) (graphs : GraphBindings A addition multiplication predicates)
    (term : Term) (numbers : Nat → Number M N) :
    ∀ (variables : Nat → Positive.Term) (output : Positive.Term) (objects : ObjectAssignment D),
      (∀ i, i < term.numberBound → (variables i).value M objects = (numbers i).val) →
      ((term.graph addition multiplication variables output).truth M objects predicates ↔
        output.value M objects = (term.value A numbers).val) := by
  induction term with
  | var i =>
      intro variables output objects assigned
      simp only [Term.graph, Applicative.Formula.truth, Term.value, assigned i (Nat.lt_succ_self i)]
  | zero => intros; exact Iff.rfl
  | successor term ih =>
      intro variables output objects assigned
      have inner (x : D) := ih (fun i => renameTerm Nat.succ (variables i)) (.var 0)
        (pushObject objects x) (by intro i hi; simpa only [renameTerm_value, pushObject] using assigned i hi)
      simp only [Term.graph, Applicative.Formula.truth, inner, renameTerm_value,
        Positive.Term.value, successorTerm, pushObject, Term.value, Operations.successor]
      constructor
      · rintro ⟨x, rfl, h⟩; exact h
      · intro h; exact ⟨_, rfl, h⟩
  | add s t hs ht =>
      intro variables output objects assigned
      have left (x y : D) := hs (fun i => renameTerm (fun n => n+2) (variables i)) (.var 1)
        (pushObject (pushObject objects x) y)
        (by intro i hi; simpa only [renameTerm_value, pushObject] using
          assigned i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)))
      have right (x y : D) := ht (fun i => renameTerm (fun n => n+2) (variables i)) (.var 0)
        (pushObject (pushObject objects x) y)
        (by intro i hi; simpa only [renameTerm_value, pushObject] using
          assigned i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _)))
      simp only [Term.graph, Applicative.Formula.truth, left, right, value_triple,
        renameTerm_value, Positive.Term.value, pushObject, Term.value]
      constructor
      · rintro ⟨x, y, rfl, rfl, h⟩; exact (graphs.add _ _ _).mp h
      · intro h; exact ⟨_, _, rfl, rfl, (graphs.add _ _ _).mpr h⟩
  | multiply s t hs ht =>
      intro variables output objects assigned
      have left (x y : D) := hs (fun i => renameTerm (fun n => n+2) (variables i)) (.var 1)
        (pushObject (pushObject objects x) y)
        (by intro i hi; simpa only [renameTerm_value, pushObject] using
          assigned i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)))
      have right (x y : D) := ht (fun i => renameTerm (fun n => n+2) (variables i)) (.var 0)
        (pushObject (pushObject objects x) y)
        (by intro i hi; simpa only [renameTerm_value, pushObject] using
          assigned i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _)))
      simp only [Term.graph, Applicative.Formula.truth, left, right, value_triple,
        renameTerm_value, Positive.Term.value, pushObject, Term.value]
      constructor
      · rintro ⟨x, y, rfl, rfl, h⟩; exact (graphs.multiply _ _ _).mp h
      · intro h; exact ⟨_, _, rfl, rfl, (graphs.multiply _ _ _).mpr h⟩

structure PartialBindings {M : Interpretation D R} {N : R 0} (A : Operations M N)
    (bound natural addition multiplication : Nat) (nm sm : Nat → Nat)
    (numbers : Nat → Number M N) (sets : Nat → SetDomain M N)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R) : Prop where
  natural : predicates 0 natural = N
  numbers : ∀ i, i < bound → objects (nm i) = (numbers i).val
  sets : ∀ i, representedSet M N (predicates 0 (sm i)) = sets i
  graphs : GraphBindings A addition multiplication predicates

theorem PartialBindings.restrict {M : Interpretation D R} {N : R 0} {A : Operations M N}
    {bound natural addition multiplication : Nat} {nm sm : Nat → Nat}
    {numbers : Nat → Number M N} {sets : Nat → SetDomain M N}
    {objects : ObjectAssignment D} {predicates : PredicateAssignment R}
    (b : PartialBindings A bound natural addition multiplication nm sm numbers sets objects predicates)
    (small : Nat) (le : small ≤ bound) :
    PartialBindings A small natural addition multiplication nm sm numbers sets objects predicates where
  natural := b.natural
  numbers := fun i hi => b.numbers i (Nat.lt_of_lt_of_le hi le)
  sets := b.sets
  graphs := b.graphs

theorem PartialBindings.member {M : Interpretation D R} {N : R 0} {A : Operations M N}
    {bound natural addition multiplication : Nat} {nm sm : Nat → Nat}
    {numbers : Nat → Number M N} {sets : Nat → SetDomain M N}
    {objects : ObjectAssignment D} {predicates : PredicateAssignment R}
    (b : PartialBindings A bound natural addition multiplication nm sm numbers sets objects predicates)
    (i : Nat) (x : Number M N) : member M (predicates 0 (sm i)) x.val ↔ (sets i).val x := by
  change (representedSet M N (predicates 0 (sm i))).val x ↔ _
  rw [b.sets i]

theorem PartialBindings.numberBinder {M : Interpretation D R} {N : R 0} {A : Operations M N}
    {bound natural addition multiplication : Nat} {nm sm : Nat → Nat}
    {numbers : Nat → Number M N} {sets : Nat → SetDomain M N}
    {objects : ObjectAssignment D} {predicates : PredicateAssignment R}
    (b : PartialBindings A (bound-1) natural addition multiplication nm sm numbers sets objects predicates)
    (x : Number M N) :
    PartialBindings A bound natural addition multiplication (Functional.bindMap nm) sm
      (pushObject numbers x) sets (pushObject objects x.val) predicates where
  natural := b.natural
  numbers := by
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact b.numbers i (by omega)
  sets := b.sets
  graphs := b.graphs

theorem PartialBindings.setBinder {M : Interpretation D R} {N : R 0} {A : Operations M N}
    {bound natural addition multiplication : Nat} {nm sm : Nat → Nat}
    {numbers : Nat → Number M N} {sets : Nat → SetDomain M N}
    {objects : ObjectAssignment D} {predicates : PredicateAssignment R}
    (b : PartialBindings A bound natural addition multiplication nm sm numbers sets objects predicates)
    (P : R 0) :
    PartialBindings A bound (natural+1) addition multiplication nm (Functional.bindMap sm)
      numbers (pushObject sets (representedSet M N P)) objects (pushPredicate predicates 0 P) where
  natural := by simpa [pushPredicate] using b.natural
  numbers := b.numbers
  sets := by
    intro i
    cases i with
    | zero => simp [Functional.bindMap, pushPredicate, pushObject]
    | succ i => simpa [Functional.bindMap, pushPredicate, pushObject] using b.sets i
  graphs := {
    add := by intro x y z; simpa [pushPredicate] using b.graphs.add x y z
    multiply := by intro x y z; simpa [pushPredicate] using b.graphs.multiply x y z }

theorem Formula.translation_preserves_truth_partial {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (p : Formula) :
    ∀ natural addition multiplication nm sm numbers sets objects predicates,
      PartialBindings A p.numberBound natural addition multiplication nm sm numbers sets objects predicates →
      ((p.translate natural addition multiplication nm sm).truth M objects predicates ↔
        p.truth A numbers sets) := by
  induction p with
  | equal s t =>
      intro natural addition multiplication nm sm numbers sets objects predicates bindings
      have hs (x : D) := s.graph_truth_partial A addition multiplication predicates bindings.graphs numbers
        (fun i => .var (nm i+1)) (.var 0) (pushObject objects x)
        (fun i hi => bindings.numbers i (Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _)))
      have ht (x : D) := t.graph_truth_partial A addition multiplication predicates bindings.graphs numbers
        (fun i => .var (nm i+1)) (.var 0) (pushObject objects x)
        (fun i hi => bindings.numbers i (Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _)))
      simp only [Formula.translate, Applicative.Formula.truth, hs, ht, Positive.Term.value,
        pushObject, Formula.truth]
      constructor
      · rintro ⟨x, hs, ht⟩; exact Subtype.ext (hs.symm.trans ht)
      · intro same; exact ⟨_, rfl, congrArg Subtype.val same⟩
  | member t i =>
      intro natural addition multiplication nm sm numbers sets objects predicates bindings
      have ht (x : D) := t.graph_truth_partial A addition multiplication predicates bindings.graphs numbers
        (fun i => .var (nm i+1)) (.var 0) (pushObject objects x) bindings.numbers
      simp only [Formula.translate, Applicative.Formula.truth, ht, unary, Positive.Term.value,
        pushObject, Formula.truth]
      constructor
      · rintro ⟨x, rfl, h⟩; exact (bindings.member i _).mp h
      · intro h; exact ⟨_, rfl, (bindings.member i _).mpr h⟩
  | setEqual i j =>
      intro natural addition multiplication nm sm numbers sets objects predicates bindings
      simp only [Formula.translate, Applicative.Formula.truth, unary, Positive.Term.value,
        pushObject, Formula.truth, bindings.natural]
      rw [set_identity_iff_coextension]
      constructor
      · intro h x
        have hx := h x.val x.property
        exact (bindings.member i x).symm.trans ((Iff.intro hx.1 hx.2).trans (bindings.member j x))
      · intro h x hx
        have eq := (bindings.member i ⟨x,hx⟩).trans ((h ⟨x,hx⟩).trans (bindings.member j ⟨x,hx⟩).symm)
        exact ⟨eq.mp, eq.mpr⟩
  | falsum => intros; exact Iff.rfl
  | implies p q hp hq =>
      intro n a m nm sm ns ss os ps b
      exact imp_congr (hp _ _ _ _ _ _ _ _ _ (b.restrict p.numberBound (Nat.le_max_left _ _))) (hq _ _ _ _ _ _ _ _ _ (b.restrict q.numberBound (Nat.le_max_right _ _)))
  | conjunction p q hp hq =>
      intro n a m nm sm ns ss os ps b
      exact and_congr (hp _ _ _ _ _ _ _ _ _ (b.restrict p.numberBound (Nat.le_max_left _ _))) (hq _ _ _ _ _ _ _ _ _ (b.restrict q.numberBound (Nat.le_max_right _ _)))
  | disjunction p q hp hq =>
      intro n a m nm sm ns ss os ps b
      exact or_congr (hp _ _ _ _ _ _ _ _ _ (b.restrict p.numberBound (Nat.le_max_left _ _))) (hq _ _ _ _ _ _ _ _ _ (b.restrict q.numberBound (Nat.le_max_right _ _)))
  | existsNumber p ih =>
      intro n a m nm sm ns ss os ps b
      simp only [Formula.translate, Applicative.Formula.truth, unary, Positive.Term.value,
        pushObject, Formula.truth, b.natural]
      constructor
      · rintro ⟨x, hx, h⟩
        exact ⟨⟨x,hx⟩, (ih _ _ _ _ _ _ _ _ _ (b.numberBinder ⟨x,hx⟩)).mp h⟩
      · rintro ⟨x, h⟩
        exact ⟨x.val, x.property, (ih _ _ _ _ _ _ _ _ _ (b.numberBinder x)).mpr h⟩
  | forallNumber p ih =>
      intro n a m nm sm ns ss os ps b
      simp only [Formula.translate, Applicative.Formula.truth, unary, Positive.Term.value,
        pushObject, Formula.truth, b.natural]
      constructor
      · intro h x
        exact (ih _ _ _ _ _ _ _ _ _ (b.numberBinder x)).mp (h x.val x.property)
      · intro h x hx
        exact (ih _ _ _ _ _ _ _ _ _ (b.numberBinder ⟨x,hx⟩)).mpr (h ⟨x,hx⟩)
  | existsSet p ih =>
      intro n a m nm sm ns ss os ps b
      constructor
      · rintro ⟨P, h⟩
        exact ⟨representedSet M N P, (ih _ _ _ _ _ _ _ _ _ (b.setBinder P)).mp h⟩
      · rintro ⟨X, h⟩
        obtain ⟨P, rfl⟩ := representedSet_surjective M N X
        exact ⟨P, (ih _ _ _ _ _ _ _ _ _ (b.setBinder P)).mpr h⟩
  | forallSet p ih =>
      intro n a m nm sm ns ss os ps b
      constructor
      · intro h X
        obtain ⟨P, rfl⟩ := representedSet_surjective M N X
        exact (ih _ _ _ _ _ _ _ _ _ (b.setBinder P)).mp (h P)
      · intro h P
        exact (ih _ _ _ _ _ _ _ _ _ (b.setBinder P)).mpr (h (representedSet M N P))

/-- A finite conjunction guarding the free-number prefix. Bound variables are
already relativised by Formula.translate. The empty conjunction is truth. -/
def numberGuards (natural : Nat) : Nat → Applicative.Formula
  | 0 => .implies .falsum .falsum
  | bound+1 => .conjunction (numberGuards natural bound) (unary natural (.var bound))

theorem numberGuards_truth (M : Interpretation D R) (natural bound : Nat)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R) :
    (numberGuards natural bound).truth M objects predicates ↔
      ∀ i, i < bound → member M (predicates 0 natural) (objects i) := by
  induction bound with
  | zero => simp [numberGuards, Applicative.Formula.truth]
  | succ bound ih =>
      simp only [numberGuards, Applicative.Formula.truth, ih, unary, Positive.Term.value]
      constructor
      · rintro ⟨initial, last⟩ i hi
        by_cases earlier : i < bound
        · exact initial i earlier
        · have same : i = bound := by omega
          exact same ▸ last
      · intro all
        exact ⟨fun i hi => all i (Nat.lt_succ_of_lt hi), all bound (Nat.lt_succ_self bound)⟩

def guardedTranslation (p : Formula) : Applicative.Formula :=
  .implies (numberGuards 0 p.numberBound) (p.translate 0 0 1 id Nat.succ)

/-- Fill irrelevant source variables with zero. Only the finitely many source
free number positions need natural target values; target set parameters are
automatically represented sets. -/
theorem translated_valid_of_number_guards {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (p : Formula) (valid : Valid A p)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R)
    (natural : predicates 0 0 = N) (graphs : GraphBindings A 0 1 predicates)
    (guards : ∀ i, i < p.numberBound → member M N (objects i)) :
    (p.translate 0 0 1 id Nat.succ).truth M objects predicates := by
  classical
  let numbers : Nat → Number M N := fun i =>
    if hi : i < p.numberBound then ⟨objects i, guards i hi⟩ else A.zero
  let sets : Nat → SetDomain M N := fun i => representedSet M N (predicates 0 (i+1))
  have bindings : PartialBindings A p.numberBound 0 0 1 id Nat.succ
      numbers sets objects predicates := {
    natural := natural
    numbers := by intro i hi; simp [numbers, hi]
    sets := fun _ => rfl
    graphs := graphs }
  exact (p.translation_preserves_truth_partial A _ _ _ _ _ _ _ _ _ bindings).mpr
    (valid numbers sets)

/-- This formula may safely be universally closed over arbitrary target
object assignments. N and the two arithmetic graphs still have their explicit
semantic premises; the canonical guard module discharges those premises. -/
theorem guarded_translation_of_valid {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (p : Formula) (valid : Valid A p)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R)
    (natural : predicates 0 0 = N) (graphs : GraphBindings A 0 1 predicates) :
    (guardedTranslation p).truth M objects predicates := by
  intro guards
  apply translated_valid_of_number_guards A p valid objects predicates natural graphs
  simpa only [natural] using (numberGuards_truth M 0 p.numberBound objects predicates).mp guards

end FregeanECA.Part2.SecondOrderArithmetic
