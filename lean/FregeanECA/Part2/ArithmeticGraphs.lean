import FregeanECA.Part2.ArithmeticFromFull
import Mathlib.Logic.ExistsUnique

/-! Addition and multiplication are available relations, constructed using
actual formulas of full comprehension. They are not assumed native maps. -/

namespace FregeanECA.Part2.Arithmetic

universe u v
variable {D : Type u} {R : Nat → Type v}

def triple {α : Type u} (x y z : α) : Fin 3 → α :=
  Fin.cases x (Fin.cases y (fun _ => z))

@[simp] theorem triple_zero {α : Type u} (x y z : α) : triple x y z 0 = x := rfl
@[simp] theorem triple_one {α : Type u} (x y z : α) : triple x y z 1 = y := rfl
@[simp] theorem triple_two {α : Type u} (x y z : α) : triple x y z 2 = z := rfl

def member3 (M : Positive.Interpretation D R) (P : R 2) (x y z : D) : Prop :=
  M.satisfies 2 P (triple x y z)

def ternary (index : Nat) (x y z : Positive.Term) : Applicative.Formula :=
  .relation 2 index (triple x y z)

def AdditionClosed (M : Positive.Interpretation D R) (N : R 0) (A : R 2) : Prop :=
  (∀ y, member M N y → member3 M A (modelZero M) y y) ∧
  (∀ x y z, member3 M A x y z → member3 M A (modelSuccessor M x) y (modelSuccessor M z))

structure LeastAddition (M : Positive.Interpretation D R) (N : R 0) (A : R 2) : Prop where
  closed : AdditionClosed M N A
  least : ∀ P : R 2, AdditionClosed M N P →
    ∀ x y z, member3 M A x y z → member3 M P x y z

def additionClosedFormula : Applicative.Formula :=
  .conjunction
    (.forallObject (.implies (unary 0 (.var 0)) (ternary 0 zeroTerm (.var 0) (.var 0))))
    (.forallObject (.forallObject (.forallObject
      (.implies (ternary 0 (.var 2) (.var 1) (.var 0))
        (ternary 0 (successorTerm (.var 2)) (.var 1) (successorTerm (.var 0)))))))

def leastAdditionFormula : Applicative.Formula :=
  .forallPredicate 2 (.implies additionClosedFormula
    (ternary 0 (.var 0) (.var 1) (.var 2)))

def additionStepFormula : Applicative.Formula :=
  .disjunction
    (.conjunction (.equal (.var 0) zeroTerm)
      (.conjunction (unary 0 (.var 1)) (.equal (.var 2) (.var 1))))
    (.existsObject (.existsObject
      (.conjunction (ternary 0 (.var 1) (.var 3) (.var 0))
        (.conjunction (.equal (.var 2) (successorTerm (.var 1)))
          (.equal (.var 4) (successorTerm (.var 0)))))))

def naturalCubeFormula : Applicative.Formula :=
  .conjunction (unary 0 (.var 0))
    (.conjunction (unary 0 (.var 1)) (unary 0 (.var 2)))

def uniqueOutputFormula : Applicative.Formula :=
  .forallObject (.implies (unary 0 (.var 0))
    (.existsObject (.conjunction (ternary 0 (.var 2) (.var 1) (.var 0))
      (.forallObject (.implies (ternary 0 (.var 3) (.var 2) (.var 0))
        (.equal (.var 0) (.var 1)))))))

private theorem ternary_value (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (x y z : Positive.Term) :
    (fun i => (triple x y z i).value M objects) =
      triple (x.value M objects) (y.value M objects) (z.value M objects) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact Fin.cases rfl (fun _ => rfl) j

theorem ternary_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R)
    (index : Nat) (x y z : Positive.Term) :
    (ternary index x y z).truth M objects predicates ↔
      member3 M (predicates 2 index) (x.value M objects) (y.value M objects) (z.value M objects) := by
  simp only [ternary, Applicative.Formula.truth, ternary_value, member3]

theorem addition_closed_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    additionClosedFormula.truth M objects predicates ↔
      AdditionClosed M (predicates 0 0) (predicates 2 0) := by
  simp only [additionClosedFormula, Applicative.Formula.truth, unary, ternary_truth,
    Positive.Term.value, Positive.pushObject, zeroTerm, successorTerm,
    AdditionClosed, member, modelZero, modelSuccessor]

theorem least_addition_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    leastAdditionFormula.truth M objects predicates ↔
      ∀ P : R 2, AdditionClosed M (predicates 0 0) P →
        member3 M P (objects 0) (objects 1) (objects 2) := by
  simp [leastAdditionFormula, Applicative.Formula.truth, addition_closed_formula_truth,
    ternary_truth, Positive.Term.value, Positive.pushPredicate]

theorem addition_step_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    additionStepFormula.truth M objects predicates ↔
      (objects 0 = modelZero M ∧ member M (predicates 0 0) (objects 1) ∧ objects 2 = objects 1) ∨
      ∃ a b, member3 M (predicates 2 0) a (objects 1) b ∧
        objects 0 = modelSuccessor M a ∧ objects 2 = modelSuccessor M b := by
  simp only [additionStepFormula, Applicative.Formula.truth, ternary_truth, unary,
    Positive.Term.value, Positive.pushObject, zeroTerm, successorTerm,
    member, modelZero, modelSuccessor]

theorem natural_cube_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    naturalCubeFormula.truth M objects predicates ↔
      member M (predicates 0 0) (objects 0) ∧ member M (predicates 0 0) (objects 1) ∧
        member M (predicates 0 0) (objects 2) := Iff.rfl

theorem unique_output_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    uniqueOutputFormula.truth M objects predicates ↔
      ∀ y, member M (predicates 0 0) y → ∃! z, member3 M (predicates 2 0) (objects 0) y z := by
  simp only [uniqueOutputFormula, Applicative.Formula.truth, ternary_truth, unary,
    Positive.Term.value, Positive.pushObject, member, ExistsUnique]

noncomputable def basePredicates (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) : Positive.PredicateAssignment R :=
  fun n _ => Classical.choice (full.relations_nonempty n)

def withNatural (predicates : Positive.PredicateAssignment R) (N : R 0) :=
  Positive.pushPredicate predicates 0 N

def withGraph (predicates : Positive.PredicateAssignment R) (A : R 2) :=
  Positive.pushPredicate predicates 2 A

theorem full_represents_ternary_formula (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) (formula : Applicative.Formula)
    (predicates : Positive.PredicateAssignment R) :
    ∃ P : R 2, ∀ x y z, member3 M P x y z ↔
      formula.truth M (Positive.assignTuple 3 (triple x y z) (fun _ => M.constantK)) predicates := by
  obtain ⟨P, law⟩ := full.comprehend 2 formula (fun _ => M.constantK) predicates
  exact ⟨P, fun x y z => law (triple x y z)⟩

theorem full_has_least_addition (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) (N : R 0) : ∃ A : R 2, LeastAddition M N A := by
  let predicates := withNatural (basePredicates M full) N
  obtain ⟨A, describes⟩ := full_represents_ternary_formula M full leastAdditionFormula predicates
  have law : ∀ x y z, member3 M A x y z ↔
      ∀ P : R 2, AdditionClosed M N P → member3 M P x y z := by
    intro x y z
    simpa [least_addition_formula_truth, predicates, withNatural, Positive.pushPredicate,
      Positive.assignTuple, Positive.pushObject] using describes x y z
  refine ⟨A, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro y ny
    exact (law _ _ _).mpr (fun P closed => closed.1 y ny)
  · intro x y z h
    exact (law _ _ _).mpr (fun P closed => closed.2 x y z ((law _ _ _).mp h P closed))
  · intro P closed x y z h
    exact (law _ _ _).mp h P closed

theorem addition_inversion (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} {A : R 2} (least : LeastAddition M N A) :
    ∀ x y z, member3 M A x y z ↔
      (x = modelZero M ∧ member M N y ∧ z = y) ∨
      ∃ a b, member3 M A a y b ∧ x = modelSuccessor M a ∧ z = modelSuccessor M b := by
  let predicates := withGraph (withNatural (basePredicates M full) N) A
  obtain ⟨Q, describes⟩ := full_represents_ternary_formula M full additionStepFormula predicates
  have law : ∀ x y z, member3 M Q x y z ↔
      (x = modelZero M ∧ member M N y ∧ z = y) ∨
      ∃ a b, member3 M A a y b ∧ x = modelSuccessor M a ∧ z = modelSuccessor M b := by
    intro x y z
    simpa [addition_step_formula_truth, predicates, withGraph, withNatural,
      Positive.pushPredicate, Positive.assignTuple, Positive.pushObject] using describes x y z
  have included : ∀ x y z, member3 M Q x y z → member3 M A x y z := by
    intro x y z h
    rcases (law x y z).mp h with ⟨rfl, ny, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩
    · exact least.closed.1 _ ny
    · exact least.closed.2 a y b hab
  have closed : AdditionClosed M N Q := by
    constructor
    · intro y ny
      exact (law _ _ _).mpr (Or.inl ⟨rfl, ny, rfl⟩)
    · intro x y z h
      exact (law _ _ _).mpr (Or.inr ⟨x, z, included x y z h, rfl, rfl⟩)
  intro x y z
  exact ⟨fun h => (law _ _ _).mp (least.least Q closed x y z h),
    fun h => included x y z ((law _ _ _).mpr h)⟩

theorem addition_support (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A : R 2} (least : LeastAddition M N A) :
    ∀ x y z, member3 M A x y z → member M N x ∧ member M N y ∧ member M N z := by
  let predicates := withNatural (basePredicates M full) N
  obtain ⟨Q, describes⟩ := full_represents_ternary_formula M full naturalCubeFormula predicates
  have law : ∀ x y z, member3 M Q x y z ↔ member M N x ∧ member M N y ∧ member M N z := by
    intro x y z
    simpa [natural_cube_formula_truth, predicates, withNatural, Positive.pushPredicate,
      Positive.assignTuple, Positive.pushObject] using describes x y z
  have closed : AdditionClosed M N Q := by
    constructor
    · intro y ny
      exact (law _ _ _).mpr ⟨domain.zero_member, ny, ny⟩
    · intro x y z h
      obtain ⟨nx, ny, nz⟩ := (law x y z).mp h
      exact (law _ _ _).mpr ⟨domain.successor_closed x nx, ny, domain.successor_closed z nz⟩
  intro x y z h
  exact (law _ _ _).mp (least.least Q closed x y z h)

theorem addition_zero_recursion (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A : R 2} (least : LeastAddition M N A) (y z : D) :
    member3 M A (modelZero M) y z ↔ member M N y ∧ z = y := by
  rw [addition_inversion M full least]
  constructor
  · rintro (⟨_, ny, zy⟩ | ⟨a, b, _, impossible, _⟩)
    · exact ⟨ny, zy⟩
    · exact False.elim (domain.zero_not_successor a impossible)
  · intro h
    exact Or.inl ⟨rfl, h⟩

theorem addition_successor_recursion (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A : R 2} (least : LeastAddition M N A) (x y z : D) :
    member3 M A (modelSuccessor M x) y z ↔
      ∃ b, member3 M A x y b ∧ z = modelSuccessor M b := by
  rw [addition_inversion M full least]
  constructor
  · rintro (⟨impossible, _, _⟩ | ⟨a, b, hab, same, out⟩)
    · exact False.elim (domain.zero_not_successor x impossible.symm)
    · have xa := domain.successor_injective x a same
      exact ⟨b, xa ▸ hab, out⟩
  · rintro ⟨b, hab, out⟩
    exact Or.inr ⟨x, b, hab, rfl, out⟩

theorem addition_total_unique (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A : R 2} (least : LeastAddition M N A) :
    ∀ x y, member M N x → member M N y → ∃! z, member3 M A x y z := by
  let predicates := withGraph (withNatural (basePredicates M full) N) A
  let parameters : Positive.ObjectAssignment D := fun _ => M.constantK
  have law : ∀ x, uniqueOutputFormula.truth M (Positive.pushObject parameters x) predicates ↔
      ∀ y, member M N y → ∃! z, member3 M A x y z := by
    intro x
    simpa [unique_output_formula_truth, predicates, withGraph, withNatural,
      Positive.pushPredicate, Positive.pushObject] using
      unique_output_formula_truth M (Positive.pushObject parameters x) predicates
  have base : ∀ y, member M N y → ∃! z, member3 M A (modelZero M) y z := by
    intro y ny
    exact ⟨y, least.closed.1 y ny,
      fun z hz => ((addition_zero_recursion M full domain least y z).mp hz).2⟩
  have step : ∀ x, member M N x →
      (∀ y, member M N y → ∃! z, member3 M A x y z) →
      ∀ y, member M N y → ∃! z, member3 M A (modelSuccessor M x) y z := by
    intro x _ ih y ny
    obtain ⟨z, hz, unique⟩ := ih y ny
    refine ⟨modelSuccessor M z, least.closed.2 x y z hz, ?_⟩
    intro w hw
    obtain ⟨b, hb, output⟩ := (addition_successor_recursion M full domain least x y w).mp hw
    exact output.trans (congrArg (modelSuccessor M) (unique b hb))
  have inductionResult := domain.formula_induction uniqueOutputFormula parameters predicates
    ((law _).mpr base)
    (fun x nx hx => (law _).mpr (step x nx ((law x).mp hx)))
  intro x y nx ny
  exact (law x).mp (inductionResult x nx) y ny

def MultiplicationClosed (M : Positive.Interpretation D R) (N : R 0)
    (A P : R 2) : Prop :=
  (∀ y, member M N y → member3 M P (modelZero M) y (modelZero M)) ∧
  (∀ x y z w, member3 M P x y z → member3 M A z y w →
    member3 M P (modelSuccessor M x) y w)

structure LeastMultiplication (M : Positive.Interpretation D R)
    (N : R 0) (A P : R 2) : Prop where
  closed : MultiplicationClosed M N A P
  least : ∀ Q : R 2, MultiplicationClosed M N A Q →
    ∀ x y z, member3 M P x y z → member3 M Q x y z

def multiplicationClosedFormula : Applicative.Formula :=
  .conjunction
    (.forallObject (.implies (unary 0 (.var 0)) (ternary 0 zeroTerm (.var 0) zeroTerm)))
    (.forallObject (.forallObject (.forallObject (.forallObject
      (.implies
        (.conjunction (ternary 0 (.var 3) (.var 2) (.var 1))
          (ternary 1 (.var 1) (.var 2) (.var 0)))
        (ternary 0 (successorTerm (.var 3)) (.var 2) (.var 0)))))))

def leastMultiplicationFormula : Applicative.Formula :=
  .forallPredicate 2 (.implies multiplicationClosedFormula
    (ternary 0 (.var 0) (.var 1) (.var 2)))

def multiplicationStepFormula : Applicative.Formula :=
  .disjunction
    (.conjunction (.equal (.var 0) zeroTerm)
      (.conjunction (unary 0 (.var 1)) (.equal (.var 2) zeroTerm)))
    (.existsObject (.existsObject
      (.conjunction (ternary 0 (.var 1) (.var 3) (.var 0))
        (.conjunction (.equal (.var 2) (successorTerm (.var 1)))
          (ternary 1 (.var 0) (.var 3) (.var 4))))))

theorem multiplication_closed_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    multiplicationClosedFormula.truth M objects predicates ↔
      MultiplicationClosed M (predicates 0 0) (predicates 2 1) (predicates 2 0) := by
  simp only [multiplicationClosedFormula, Applicative.Formula.truth, unary, ternary_truth,
    Positive.Term.value, Positive.pushObject, zeroTerm, successorTerm,
    MultiplicationClosed, member, modelZero, modelSuccessor, and_imp]

theorem least_multiplication_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    leastMultiplicationFormula.truth M objects predicates ↔
      ∀ P : R 2, MultiplicationClosed M (predicates 0 0) (predicates 2 0) P →
        member3 M P (objects 0) (objects 1) (objects 2) := by
  simp [leastMultiplicationFormula, Applicative.Formula.truth, multiplication_closed_formula_truth,
    ternary_truth, Positive.Term.value, Positive.pushPredicate]

theorem multiplication_step_formula_truth (M : Positive.Interpretation D R)
    (objects : Positive.ObjectAssignment D) (predicates : Positive.PredicateAssignment R) :
    multiplicationStepFormula.truth M objects predicates ↔
      (objects 0 = modelZero M ∧ member M (predicates 0 0) (objects 1) ∧ objects 2 = modelZero M) ∨
      ∃ a b, member3 M (predicates 2 0) a (objects 1) b ∧
        objects 0 = modelSuccessor M a ∧ member3 M (predicates 2 1) b (objects 1) (objects 2) := by
  simp only [multiplicationStepFormula, Applicative.Formula.truth, ternary_truth, unary,
    Positive.Term.value, Positive.pushObject, zeroTerm, successorTerm,
    member, modelZero, modelSuccessor]

theorem full_has_least_multiplication (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) (N : R 0) (A : R 2) :
    ∃ P : R 2, LeastMultiplication M N A P := by
  let predicates := withGraph (withNatural (basePredicates M full) N) A
  obtain ⟨P, describes⟩ := full_represents_ternary_formula M full leastMultiplicationFormula predicates
  have law : ∀ x y z, member3 M P x y z ↔
      ∀ Q : R 2, MultiplicationClosed M N A Q → member3 M Q x y z := by
    intro x y z
    simpa [least_multiplication_formula_truth, predicates, withGraph, withNatural,
      Positive.pushPredicate, Positive.assignTuple, Positive.pushObject] using describes x y z
  refine ⟨P, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro y ny
    exact (law _ _ _).mpr (fun Q closed => closed.1 y ny)
  · intro x y z w h add
    exact (law _ _ _).mpr (fun Q closed => closed.2 x y z w ((law _ _ _).mp h Q closed) add)
  · intro Q closed x y z h
    exact (law _ _ _).mp h Q closed

theorem multiplication_inversion (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} {A P : R 2}
    (least : LeastMultiplication M N A P) :
    ∀ x y z, member3 M P x y z ↔
      (x = modelZero M ∧ member M N y ∧ z = modelZero M) ∨
      ∃ a b, member3 M P a y b ∧ x = modelSuccessor M a ∧ member3 M A b y z := by
  let predicates := withGraph (withGraph (withNatural (basePredicates M full) N) A) P
  obtain ⟨Q, describes⟩ := full_represents_ternary_formula M full multiplicationStepFormula predicates
  have law : ∀ x y z, member3 M Q x y z ↔
      (x = modelZero M ∧ member M N y ∧ z = modelZero M) ∨
      ∃ a b, member3 M P a y b ∧ x = modelSuccessor M a ∧ member3 M A b y z := by
    intro x y z
    simpa [multiplication_step_formula_truth, predicates, withGraph, withNatural,
      Positive.pushPredicate, Positive.assignTuple, Positive.pushObject] using describes x y z
  have included : ∀ x y z, member3 M Q x y z → member3 M P x y z := by
    intro x y z h
    rcases (law x y z).mp h with ⟨rfl, ny, rfl⟩ | ⟨a, b, hab, rfl, add⟩
    · exact least.closed.1 _ ny
    · exact least.closed.2 a y b z hab add
  have closed : MultiplicationClosed M N A Q := by
    constructor
    · intro y ny
      exact (law _ _ _).mpr (Or.inl ⟨rfl, ny, rfl⟩)
    · intro x y z w h add
      exact (law _ _ _).mpr (Or.inr ⟨x, z, included x y z h, rfl, add⟩)
  intro x y z
  exact ⟨fun h => (law _ _ _).mp (least.least Q closed x y z h),
    fun h => included x y z ((law _ _ _).mpr h)⟩

theorem multiplication_support (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A P : R 2} (addition : LeastAddition M N A) (least : LeastMultiplication M N A P) :
    ∀ x y z, member3 M P x y z → member M N x ∧ member M N y ∧ member M N z := by
  let predicates := withNatural (basePredicates M full) N
  obtain ⟨Q, describes⟩ := full_represents_ternary_formula M full naturalCubeFormula predicates
  have law : ∀ x y z, member3 M Q x y z ↔ member M N x ∧ member M N y ∧ member M N z := by
    intro x y z
    simpa [natural_cube_formula_truth, predicates, withNatural, Positive.pushPredicate,
      Positive.assignTuple, Positive.pushObject] using describes x y z
  have closed : MultiplicationClosed M N A Q := by
    constructor
    · intro y ny
      exact (law _ _ _).mpr ⟨domain.zero_member, ny, domain.zero_member⟩
    · intro x y z w h add
      obtain ⟨nx, ny, _⟩ := (law x y z).mp h
      have nw := (addition_support M full domain addition z y w add).2.2
      exact (law _ _ _).mpr ⟨domain.successor_closed x nx, ny, nw⟩
  intro x y z h
  exact (law _ _ _).mp (least.least Q closed x y z h)

theorem multiplication_zero_recursion (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A P : R 2} (least : LeastMultiplication M N A P) (y z : D) :
    member3 M P (modelZero M) y z ↔ member M N y ∧ z = modelZero M := by
  rw [multiplication_inversion M full least]
  constructor
  · rintro (⟨_, ny, zy⟩ | ⟨a, b, _, impossible, _⟩)
    · exact ⟨ny, zy⟩
    · exact False.elim (domain.zero_not_successor a impossible)
  · intro h
    exact Or.inl ⟨rfl, h⟩

theorem multiplication_successor_recursion (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A P : R 2} (least : LeastMultiplication M N A P) (x y z : D) :
    member3 M P (modelSuccessor M x) y z ↔
      ∃ b, member3 M P x y b ∧ member3 M A b y z := by
  rw [multiplication_inversion M full least]
  constructor
  · rintro (⟨impossible, _, _⟩ | ⟨a, b, hab, same, add⟩)
    · exact False.elim (domain.zero_not_successor x impossible.symm)
    · have xa := domain.successor_injective x a same
      exact ⟨b, xa ▸ hab, add⟩
  · rintro ⟨b, hab, add⟩
    exact Or.inr ⟨x, b, hab, rfl, add⟩

theorem multiplication_total_unique (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    {A P : R 2} (addition : LeastAddition M N A) (least : LeastMultiplication M N A P) :
    ∀ x y, member M N x → member M N y → ∃! z, member3 M P x y z := by
  let predicates := withGraph (withNatural (basePredicates M full) N) P
  let parameters : Positive.ObjectAssignment D := fun _ => M.constantK
  have law : ∀ x, uniqueOutputFormula.truth M (Positive.pushObject parameters x) predicates ↔
      ∀ y, member M N y → ∃! z, member3 M P x y z := by
    intro x
    simpa [unique_output_formula_truth, predicates, withGraph, withNatural,
      Positive.pushPredicate, Positive.pushObject] using
      unique_output_formula_truth M (Positive.pushObject parameters x) predicates
  have base : ∀ y, member M N y → ∃! z, member3 M P (modelZero M) y z := by
    intro y ny
    exact ⟨modelZero M, least.closed.1 y ny,
      fun z hz => ((multiplication_zero_recursion M full domain least y z).mp hz).2⟩
  have step : ∀ x, member M N x →
      (∀ y, member M N y → ∃! z, member3 M P x y z) →
      ∀ y, member M N y → ∃! z, member3 M P (modelSuccessor M x) y z := by
    intro x _ ih y ny
    obtain ⟨z, hz, unique⟩ := ih y ny
    have nz := (multiplication_support M full domain addition least x y z hz).2.2
    obtain ⟨w, hw, uniqueAdd⟩ := addition_total_unique M full domain addition z y nz ny
    refine ⟨w, least.closed.2 x y z w hz hw, ?_⟩
    intro out hout
    obtain ⟨b, hb, add⟩ :=
      (multiplication_successor_recursion M full domain least x y out).mp hout
    have bz := unique b hb
    exact uniqueAdd out (bz ▸ add)
  have inductionResult := domain.formula_induction uniqueOutputFormula parameters predicates
    ((law _).mpr base)
    (fun x nx hx => (law _).mpr (step x nx ((law x).mp hx)))
  intro x y nx ny
  exact (law x).mp (inductionResult x nx) y ny

/-- All arithmetic operations below are available ternary graph relations.
The recursion orientation matches the manuscript: the first argument recurses. -/
structure FullArithmetic (M : Positive.Interpretation D R) (N : R 0) where
  domain : PeanoDomain M N
  addition : R 2
  multiplication : R 2
  addition_support : ∀ x y z, member3 M addition x y z →
    member M N x ∧ member M N y ∧ member M N z
  multiplication_support : ∀ x y z, member3 M multiplication x y z →
    member M N x ∧ member M N y ∧ member M N z
  addition_total_unique : ∀ x y, member M N x → member M N y → ∃! z, member3 M addition x y z
  multiplication_total_unique : ∀ x y, member M N x → member M N y → ∃! z, member3 M multiplication x y z
  addition_zero_recursion : ∀ y z, member3 M addition (modelZero M) y z ↔ member M N y ∧ z = y
  addition_successor_recursion : ∀ x y z, member3 M addition (modelSuccessor M x) y z ↔
    ∃ b, member3 M addition x y b ∧ z = modelSuccessor M b
  multiplication_zero_recursion : ∀ y z,
    member3 M multiplication (modelZero M) y z ↔ member M N y ∧ z = modelZero M
  multiplication_successor_recursion : ∀ x y z, member3 M multiplication (modelSuccessor M x) y z ↔
    ∃ b, member3 M multiplication x y b ∧ member3 M addition b y z

theorem full_comprehension_supplies_arithmetic (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N) :
    Nonempty (FullArithmetic M N) := by
  obtain ⟨A, addition⟩ := full_has_least_addition M full N
  obtain ⟨P, multiplication⟩ := full_has_least_multiplication M full N A
  exact ⟨{ domain := domain
           addition := A
           multiplication := P
           addition_support := addition_support M full domain addition
           multiplication_support := multiplication_support M full domain addition multiplication
           addition_total_unique := addition_total_unique M full domain addition
           multiplication_total_unique := multiplication_total_unique M full domain addition multiplication
           addition_zero_recursion := addition_zero_recursion M full domain addition
           addition_successor_recursion := addition_successor_recursion M full domain addition
           multiplication_zero_recursion := multiplication_zero_recursion M full domain multiplication
           multiplication_successor_recursion := multiplication_successor_recursion M full domain multiplication }⟩

theorem full_ts_has_arithmetic (M : Positive.Interpretation D R) (full : FullTSConditions M) :
    ∃ N : R 0, Nonempty (FullArithmetic M N) := by
  obtain ⟨N, domain⟩ := full_ts_has_peano_domain M full
  exact ⟨N, full_comprehension_supplies_arithmetic M full.full_comprehension domain⟩

end FregeanECA.Part2.Arithmetic
