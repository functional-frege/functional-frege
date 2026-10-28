import FregeanECA.Part2.ArithmeticGraphs

/-! Available successor order on the interpreted arithmetic domain.
Every represented predicate used here is supplied by an explicit instance of
the actual comprehension grammar; no identification with standard Nat occurs.
This is infrastructure for the internal Hume interpretation, not that result.
-/

namespace FregeanECA.Part2.HumeOrder
open Positive Arithmetic
universe u v
variable {D : Type u} {R : Nat → Type v}

def pair {α : Type u} (x y : α) : Fin 2 → α := Fin.cases x (fun _ => y)

def member2 (M : Interpretation D R) (P : R 1) (x y : D) : Prop :=
  M.satisfies 1 P (pair x y)

def binary (index : Nat) (x y : Positive.Term) : Applicative.Formula :=
  .relation 1 index (pair x y)

theorem binary_truth (M : Interpretation D R) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) (i : Nat) (x y : Positive.Term) :
    (binary i x y).truth M objects predicates ↔
      member2 M (predicates 1 i) (x.value M objects) (y.value M objects) := by
  have values : (fun j => (pair x y j).value M objects) =
      pair (x.value M objects) (y.value M objects) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp only [binary, Applicative.Formula.truth, values, member2]

/-- The successor ancestral, quantified over the available unary predicates. -/
def Le (M : Interpretation D R) (x y : D) : Prop :=
  ∀ P : R 0, member M P x →
    (∀ z, member M P z → member M P (modelSuccessor M z)) → member M P y

def leFormula : Applicative.Formula :=
  .forallPredicate 0 (.implies
    (.conjunction (unary 0 (.var 0))
      (.forallObject (.implies (unary 0 (.var 0))
        (unary 0 (successorTerm (.var 0))))))
    (unary 0 (.var 1)))

theorem le_formula_truth (M : Interpretation D R) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) :
    leFormula.truth M objects predicates ↔ Le M (objects 0) (objects 1) := by
  simp only [leFormula, Applicative.Formula.truth, unary, successorTerm,
    Positive.Term.value, pushPredicate, pushObject, Le, member, modelSuccessor,
    dite_true, and_imp]

def RepresentsLe (M : Interpretation D R) (L : R 1) : Prop :=
  ∀ x y, member2 M L x y ↔ Le M x y

/-- Full comprehension supplies the order in the existing binary relation sort. -/
theorem full_has_order (M : Interpretation D R) (full : HasFullComprehension M) :
    ∃ L : R 1, RepresentsLe M L := by
  let predicates := basePredicates M full
  obtain ⟨L, law⟩ := full.comprehend 1 leFormula (fun _ => M.constantK) predicates
  refine ⟨L, ?_⟩
  intro x y
  exact (law (pair x y)).trans (le_formula_truth M _ predicates)

theorem le_refl (M : Interpretation D R) (x : D) : Le M x x :=
  fun _ hx _ => hx

theorem le_trans (M : Interpretation D R) {x y z : D}
    (xy : Le M x y) (yz : Le M y z) : Le M x z :=
  fun P hx closed => yz P (xy P hx closed) closed

theorem le_successor (M : Interpretation D R) {x y : D}
    (xy : Le M x y) : Le M x (modelSuccessor M y) :=
  fun P hx closed => closed y (xy P hx closed)

theorem le_self_successor (M : Interpretation D R) (x : D) :
    Le M x (modelSuccessor M x) := le_successor M (le_refl M x)

theorem zero_le (M : Interpretation D R) {N : R 0} (domain : PeanoDomain M N)
    {x : D} (nx : member M N x) : Le M (modelZero M) x := by
  intro P base step
  exact (domain.represents_least x).mp nx P ⟨base, step⟩

theorem le_preserves_natural (M : Interpretation D R) {N : R 0}
    (domain : PeanoDomain M N) {x y : D} (nx : member M N x) (xy : Le M x y) :
    member M N y := xy N nx domain.successor_closed

/-- The available one-step closure used to invert the ancestral. Its free
object variables are the output y at zero and the starting point x at one. -/
def stepFormula : Applicative.Formula :=
  .disjunction (.equal (.var 0) (.var 1))
    (.existsObject (.conjunction (binary 0 (.var 2) (.var 0))
      (.equal (.var 1) (successorTerm (.var 0)))))

theorem step_formula_truth (M : Interpretation D R) (objects : ObjectAssignment D)
    (predicates : PredicateAssignment R) :
    stepFormula.truth M objects predicates ↔
      objects 0 = objects 1 ∨ ∃ z,
        member2 M (predicates 1 0) (objects 1) z ∧ objects 0 = modelSuccessor M z := by
  simp only [stepFormula, Applicative.Formula.truth, binary_truth,
    Positive.Term.value, pushObject, successorTerm, modelSuccessor]

theorem le_inversion (M : Interpretation D R) (full : HasFullComprehension M)
    (x y : D) : Le M x y ↔ y = x ∨ ∃ z, Le M x z ∧ y = modelSuccessor M z := by
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  let predicates := pushPredicate (basePredicates M full) 1 L
  obtain ⟨P, describes⟩ := full_comprehension_represents_unary_formula M full
    stepFormula (fun _ => x) predicates
  have law : ∀ y, member M P y ↔
      y = x ∨ ∃ z, Le M x z ∧ y = modelSuccessor M z := by
    intro y
    simpa [step_formula_truth, predicates, pushPredicate, pushObject, orderLaw] using describes y
  have included : ∀ y, member M P y → Le M x y := by
    intro y hy
    rcases (law y).mp hy with rfl | ⟨z, hz, rfl⟩
    · exact le_refl M _
    · exact le_successor M hz
  constructor
  · intro xy
    apply (law y).mp
    apply xy P ((law x).mpr (Or.inl rfl))
    intro z hz
    exact (law _).mpr (Or.inr ⟨z, included z hz, rfl⟩)
  · intro hy
    exact included y ((law y).mpr hy)

theorem le_zero_iff (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (x : D) :
    Le M x (modelZero M) ↔ x = modelZero M := by
  rw [le_inversion M full]
  constructor
  · rintro (h | ⟨z, _, impossible⟩)
    · exact h.symm
    · exact False.elim (domain.zero_not_successor z impossible)
  · intro h
    exact Or.inl h.symm

theorem le_successor_iff (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (x y : D) :
    Le M x (modelSuccessor M y) ↔ Le M x y ∨ x = modelSuccessor M y := by
  rw [le_inversion M full]
  constructor
  · rintro (h | ⟨z, xz, same⟩)
    · exact Or.inr h.symm
    · have yz := domain.successor_injective y z same
      exact Or.inl (yz ▸ xz)
  · rintro (xy | same)
    · exact Or.inr ⟨y, xy, rfl⟩
    · exact Or.inl same.symm

/-- A convenience wrapper; the property is justified by a displayed formula,
not supplied as an unrestricted induction instance. -/
theorem induction_of_formula (M : Interpretation D R) {N : R 0}
    (domain : PeanoDomain M N) (formula : Applicative.Formula)
    (parameters : ObjectAssignment D) (predicates : PredicateAssignment R)
    (property : D → Prop)
    (law : ∀ x, formula.truth M (pushObject parameters x) predicates ↔ property x)
    (base : property (modelZero M))
    (step : ∀ x, member M N x → property x → property (modelSuccessor M x)) :
    ∀ x, member M N x → property x := by
  intro x nx
  apply (law x).mp
  exact domain.formula_induction formula parameters predicates ((law _).mpr base)
    (fun y ny hy => (law _).mpr (step y ny ((law _).mp hy))) x nx

def successorOrderFormula : Applicative.Formula :=
  binary 0 (successorTerm (.var 1)) (successorTerm (.var 0))

theorem successor_le_successor (M : Interpretation D R) (full : HasFullComprehension M)
    {x y : D} (xy : Le M x y) : Le M (modelSuccessor M x) (modelSuccessor M y) := by
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  let predicates := pushPredicate (basePredicates M full) 1 L
  obtain ⟨P, describes⟩ := full_comprehension_represents_unary_formula M full
    successorOrderFormula (fun _ => x) predicates
  have law : ∀ z, member M P z ↔ Le M (modelSuccessor M x) (modelSuccessor M z) := by
    intro z
    simpa [successorOrderFormula, binary_truth, successorTerm, Positive.Term.value,
      predicates, pushPredicate, pushObject, modelSuccessor, orderLaw] using describes z
  apply (law y).mp
  apply xy P ((law x).mpr (le_refl M _))
  intro z hz
  exact (law _).mpr (le_successor M ((law z).mp hz))

def noSuccessorBackFormula : Applicative.Formula :=
  .implies (binary 0 (successorTerm (.var 0)) (.var 0)) .falsum

theorem not_successor_le_self (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) :
    ∀ x, member M N x → ¬ Le M (modelSuccessor M x) x := by
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  let predicates := pushPredicate (basePredicates M full) 1 L
  apply induction_of_formula M domain noSuccessorBackFormula (fun _ => M.constantK)
    predicates (fun x => ¬ Le M (modelSuccessor M x) x)
  · intro x
    simp [noSuccessorBackFormula, Applicative.Formula.truth, binary_truth,
      successorTerm, Positive.Term.value, predicates, pushPredicate, pushObject,
      modelSuccessor, orderLaw]
  · intro impossible
    exact domain.zero_not_successor _ ((le_zero_iff M full domain _).mp impossible).symm
  · intro x _ ih impossible
    rcases (le_successor_iff M full domain _ _).mp impossible with h | h
    · exact ih (le_trans M (le_self_successor M _) h)
    · have same := domain.successor_injective _ _ h
      apply ih
      rw [same]
      exact le_refl M x

theorem successor_le_of_le_ne (M : Interpretation D R) (full : HasFullComprehension M)
    {x y : D} (xy : Le M x y) (different : x ≠ y) : Le M (modelSuccessor M x) y := by
  rcases (le_inversion M full x y).mp xy with same | ⟨z, xz, rfl⟩
  · exact False.elim (different same.symm)
  · exact successor_le_successor M full xz

theorem le_antisymm (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) {x y : D}
    (nx : member M N x) (xy : Le M x y) (yx : Le M y x) : x = y := by
  classical
  by_cases same : x = y
  · exact same
  · exact False.elim (not_successor_le_self M full domain x nx
      (le_trans M (successor_le_of_le_ne M full xy same) yx))

/-- The induction formula compares its current argument with all natural
objects. The graph and natural-domain predicates are explicit parameters. -/
def comparisonFormula : Applicative.Formula :=
  .forallObject (.implies (unary 0 (.var 0))
    (.disjunction (binary 0 (.var 1) (.var 0)) (binary 0 (.var 0) (.var 1))))

theorem le_total (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) :
    ∀ x, member M N x → ∀ y, member M N y → Le M x y ∨ Le M y x := by
  classical
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  let predicates := pushPredicate (withNatural (basePredicates M full) N) 1 L
  apply induction_of_formula M domain comparisonFormula (fun _ => M.constantK)
    predicates (fun x => ∀ y, member M N y → Le M x y ∨ Le M y x)
  · intro x
    simp [comparisonFormula, Applicative.Formula.truth, binary_truth, unary,
      Positive.Term.value, predicates, withNatural, pushPredicate, pushObject,
      member, orderLaw]
  · intro y ny
    exact Or.inl (zero_le M domain ny)
  · intro x _ ih y ny
    rcases ih y ny with xy | yx
    · by_cases same : x = y
      · exact Or.inr (same ▸ le_self_successor M x)
      · exact Or.inl (successor_le_of_le_ne M full xy same)
    · exact Or.inr (le_successor M yx)

/-- Natural numbers are zero or the successor of another natural number.
The predecessor is proved internally, not found by external Nat recursion. -/
def predecessorFormula : Applicative.Formula :=
  .disjunction (.equal (.var 0) zeroTerm)
    (.existsObject (.conjunction (unary 0 (.var 0))
      (.equal (.var 1) (successorTerm (.var 0)))))

theorem zero_or_successor (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) :
    ∀ x, member M N x → x = modelZero M ∨
      ∃ y, member M N y ∧ x = modelSuccessor M y := by
  let predicates := withNatural (basePredicates M full) N
  apply induction_of_formula M domain predecessorFormula (fun _ => M.constantK)
    predicates (fun x => x = modelZero M ∨ ∃ y, member M N y ∧ x = modelSuccessor M y)
  · intro x
    simp [predecessorFormula, Applicative.Formula.truth, unary, Positive.Term.value,
      zeroTerm, successorTerm, predicates, withNatural, pushPredicate, pushObject,
      modelZero, modelSuccessor, member]
  · exact Or.inl rfl
  · intro x nx _
    exact Or.inr ⟨x, nx, rfl⟩

/-- Predicate zero is P, predicate one is N, and binary predicate zero is
the available order. This formula states that P has no natural member ≤ x. -/
def noMemberBelowFormula : Applicative.Formula :=
  .forallObject (.implies (unary 1 (.var 0))
    (.implies (binary 0 (.var 0) (.var 1))
      (.implies (unary 0 (.var 0)) .falsum)))

/-- Every inhabited available predicate on the interpreted numbers has a least
member. The induction instance is the explicit noMemberBelowFormula. -/
theorem least_available_member (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (P : R 0)
    (inhabited : ∃ x, member M N x ∧ member M P x) :
    ∃ x, member M N x ∧ member M P x ∧
      ∀ y, member M N y → member M P y → Le M x y := by
  classical
  by_cases least : ∃ x, member M N x ∧ member M P x ∧
      ∀ y, member M N y → member M P y → Le M x y
  · exact least
  · obtain ⟨L, orderLaw⟩ := full_has_order M full
    change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
    let predicates := pushPredicate (pushPredicate
      (withNatural (basePredicates M full) N) 0 P) 1 L
    have absent : ∀ x, member M N x →
        ∀ y, member M N y → Le M y x → ¬ member M P y := by
      apply induction_of_formula M domain noMemberBelowFormula (fun _ => M.constantK)
        predicates (fun x => ∀ y, member M N y → Le M y x → ¬ member M P y)
      · intro x
        simp [noMemberBelowFormula, Applicative.Formula.truth, binary_truth,
          unary, Positive.Term.value, predicates, withNatural, pushPredicate,
          pushObject, member, orderLaw]
      · intro y _ below py
        have yz := (le_zero_iff M full domain y).mp below
        subst y
        exact least ⟨modelZero M, domain.zero_member, py,
          fun z nz _ => zero_le M domain nz⟩
      · intro x nx ih y ny below py
        rcases (le_successor_iff M full domain y x).mp below with yx | same
        · exact ih y ny yx py
        · subst y
          apply least
          refine ⟨modelSuccessor M x, domain.successor_closed x nx, py, ?_⟩
          intro z nz pz
          rcases le_total M full domain z nz x nx with zx | xz
          · exact False.elim (ih z nz zx pz)
          · apply successor_le_of_le_ne M full xz
            intro same
            subst z
            exact ih x nx (le_refl M x) pz
    obtain ⟨x, nx, px⟩ := inhabited
    exact False.elim (absent x nx x nx (le_refl M x) px)

end FregeanECA.Part2.HumeOrder
