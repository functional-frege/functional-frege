import FregeanECA.Part2.HumeOrder
import FregeanECA.Part2.HumeBijections

/-! Predicate counting on an arbitrary Henkin Peano domain. The count graph
is supplied by a displayed full-comprehension formula and characterized by
least closure. No external Nat recursion, cardinality, or enumeration is used.
This is infrastructure for internal HP, not a claim that HP is yet proved. -/

namespace FregeanECA.Part2.HumeCounting
open Positive Arithmetic HumeOrder HumeFinite HumeBijections
universe u v
variable {D : Type u} {R : Nat → Type v}

@[simp] theorem count_pair_zero {α : Type u} (x y : α) : pair x y 0 = x := rfl
@[simp] theorem count_pair_one {α : Type u} (x y : α) : pair x y 1 = y := rfl

def CountClosed (M : Interpretation D R) (P : R 0) (C : R 1) : Prop :=
  member2 M C (modelZero M) (modelZero M) ∧
  (∀ x y, member2 M C x y → member M P x →
    member2 M C (modelSuccessor M x) (modelSuccessor M y)) ∧
  (∀ x y, member2 M C x y → ¬ member M P x →
    member2 M C (modelSuccessor M x) y)

structure LeastCount (M : Interpretation D R) (P : R 0) (C : R 1) : Prop where
  closed : CountClosed M P C
  least : ∀ Q : R 1, CountClosed M P Q →
    ∀ x y, member2 M C x y → member2 M Q x y

def countClosedFormula : Applicative.Formula :=
  .conjunction (binary 0 zeroTerm zeroTerm)
    (.conjunction
      (.forallObject (.forallObject (.implies (binary 0 (.var 1) (.var 0))
        (.implies (unary 0 (.var 1))
          (binary 0 (successorTerm (.var 1)) (successorTerm (.var 0)))))))
      (.forallObject (.forallObject (.implies (binary 0 (.var 1) (.var 0))
        (.implies (.implies (unary 0 (.var 1)) .falsum)
          (binary 0 (successorTerm (.var 1)) (.var 0)))))))

def leastCountFormula : Applicative.Formula :=
  .forallPredicate 1 (.implies countClosedFormula (binary 0 (.var 0) (.var 1)))

def countStepFormula : Applicative.Formula :=
  .disjunction
    (.conjunction (.equal (.var 0) zeroTerm) (.equal (.var 1) zeroTerm))
    (.existsObject (.existsObject
      (.conjunction (binary 0 (.var 1) (.var 0))
        (.conjunction (.equal (.var 2) (successorTerm (.var 1)))
          (.disjunction
            (.conjunction (unary 0 (.var 1))
              (.equal (.var 3) (successorTerm (.var 0))))
            (.conjunction (.implies (unary 0 (.var 1)) .falsum)
              (.equal (.var 3) (.var 0))))))))

def naturalSquareFormula : Applicative.Formula :=
  .conjunction (unary 0 (.var 0)) (unary 0 (.var 1))

def uniqueCountFormula : Applicative.Formula :=
  .existsObject (.conjunction (binary 0 (.var 1) (.var 0))
    (.forallObject (.implies (binary 0 (.var 2) (.var 0))
      (.equal (.var 0) (.var 1)))))

theorem count_closed_formula_truth (M : Interpretation D R)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R) :
    countClosedFormula.truth M objects predicates ↔
      CountClosed M (predicates 0 0) (predicates 1 0) := by
  simp only [countClosedFormula, Applicative.Formula.truth, binary_truth, unary,
    Positive.Term.value, pushObject, zeroTerm, successorTerm, CountClosed,
    member, modelZero, modelSuccessor]

theorem least_count_formula_truth (M : Interpretation D R)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R) :
    leastCountFormula.truth M objects predicates ↔
      ∀ C : R 1, CountClosed M (predicates 0 0) C →
        member2 M C (objects 0) (objects 1) := by
  simp [leastCountFormula, Applicative.Formula.truth, count_closed_formula_truth,
    binary_truth, Positive.Term.value, pushPredicate]

theorem count_step_formula_truth (M : Interpretation D R)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R) :
    countStepFormula.truth M objects predicates ↔
      (objects 0 = modelZero M ∧ objects 1 = modelZero M) ∨
      ∃ a b, member2 M (predicates 1 0) a b ∧ objects 0 = modelSuccessor M a ∧
        ((member M (predicates 0 0) a ∧ objects 1 = modelSuccessor M b) ∨
         (¬ member M (predicates 0 0) a ∧ objects 1 = b)) := by
  simp only [countStepFormula, Applicative.Formula.truth, binary_truth, unary,
    Positive.Term.value, pushObject, zeroTerm, successorTerm,
    member, modelZero, modelSuccessor]

theorem full_represents_binary_formula (M : Interpretation D R)
    (full : HasFullComprehension M) (formula : Applicative.Formula)
    (predicates : PredicateAssignment R) :
    ∃ C : R 1, ∀ x y, member2 M C x y ↔
      formula.truth M (assignTuple 2 (pair x y) (fun _ => M.constantK)) predicates := by
  obtain ⟨C, law⟩ := full.comprehend 1 formula (fun _ => M.constantK) predicates
  exact ⟨C, fun x y => law (pair x y)⟩

theorem full_has_least_count (M : Interpretation D R)
    (full : HasFullComprehension M) (P : R 0) : ∃ C : R 1, LeastCount M P C := by
  let predicates := pushPredicate (basePredicates M full) 0 P
  obtain ⟨C, describes⟩ := full_represents_binary_formula M full leastCountFormula predicates
  have law : ∀ x y, member2 M C x y ↔
      ∀ Q : R 1, CountClosed M P Q → member2 M Q x y := by
    intro x y
    simpa [least_count_formula_truth, predicates, pushPredicate, assignTuple, pushObject]
      using describes x y
  refine ⟨C, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · exact (law _ _).mpr (fun Q closed => closed.1)
  · intro x y cxy px
    exact (law _ _).mpr (fun Q closed => closed.2.1 x y ((law _ _).mp cxy Q closed) px)
  · intro x y cxy px
    exact (law _ _).mpr (fun Q closed => closed.2.2 x y ((law _ _).mp cxy Q closed) px)
  · intro Q closed x y cxy
    exact (law _ _).mp cxy Q closed

theorem count_inversion (M : Interpretation D R) (full : HasFullComprehension M)
    {P : R 0} {C : R 1} (least : LeastCount M P C) (x y : D) :
    member2 M C x y ↔ (x = modelZero M ∧ y = modelZero M) ∨
      ∃ a b, member2 M C a b ∧ x = modelSuccessor M a ∧
        ((member M P a ∧ y = modelSuccessor M b) ∨ (¬ member M P a ∧ y = b)) := by
  let predicates := pushPredicate (pushPredicate (basePredicates M full) 0 P) 1 C
  obtain ⟨Q, describes⟩ := full_represents_binary_formula M full countStepFormula predicates
  have law : ∀ x y, member2 M Q x y ↔ (x = modelZero M ∧ y = modelZero M) ∨
      ∃ a b, member2 M C a b ∧ x = modelSuccessor M a ∧
        ((member M P a ∧ y = modelSuccessor M b) ∨ (¬ member M P a ∧ y = b)) := by
    intro x y
    simpa [count_step_formula_truth, predicates, pushPredicate, assignTuple, pushObject]
      using describes x y
  have included : ∀ x y, member2 M Q x y → member2 M C x y := by
    intro x y qxy
    rcases (law _ _).mp qxy with ⟨rfl, rfl⟩ | ⟨a, b, cab, rfl, output⟩
    · exact least.closed.1
    · rcases output with ⟨pa, rfl⟩ | ⟨pa, rfl⟩
      · exact least.closed.2.1 a b cab pa
      · exact least.closed.2.2 a _ cab pa
  have closed : CountClosed M P Q := by
    refine ⟨(law _ _).mpr (Or.inl ⟨rfl, rfl⟩), ?_, ?_⟩
    · intro a b qab pa
      exact (law _ _).mpr (Or.inr ⟨a, b, included a b qab, rfl, Or.inl ⟨pa, rfl⟩⟩)
    · intro a b qab pa
      exact (law _ _).mpr (Or.inr ⟨a, b, included a b qab, rfl, Or.inr ⟨pa, rfl⟩⟩)
  exact ⟨fun cxy => (law _ _).mp (least.least Q closed x y cxy),
    fun rhs => included x y ((law _ _).mpr rhs)⟩

theorem count_support (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C) :
    ∀ x y, member2 M C x y → member M N x ∧ member M N y := by
  let predicates := pushPredicate (basePredicates M full) 0 N
  obtain ⟨Q, describes⟩ := full_represents_binary_formula M full naturalSquareFormula predicates
  have law : ∀ x y, member2 M Q x y ↔ member M N x ∧ member M N y := by
    intro x y
    simpa [naturalSquareFormula, Applicative.Formula.truth, unary, Positive.Term.value,
      predicates, pushPredicate, assignTuple, pushObject, member] using describes x y
  have closed : CountClosed M P Q := by
    refine ⟨(law _ _).mpr ⟨domain.zero_member, domain.zero_member⟩, ?_, ?_⟩
    · intro x y qxy _
      obtain ⟨nx, ny⟩ := (law _ _).mp qxy
      exact (law _ _).mpr ⟨domain.successor_closed x nx, domain.successor_closed y ny⟩
    · intro x y qxy _
      obtain ⟨nx, ny⟩ := (law _ _).mp qxy
      exact (law _ _).mpr ⟨domain.successor_closed x nx, ny⟩
  intro x y cxy
  exact (law _ _).mp (least.least Q closed x y cxy)

theorem count_zero (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C) (y : D) :
    member2 M C (modelZero M) y ↔ y = modelZero M := by
  rw [count_inversion M full least]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨a, b, _, impossible, _⟩)
    · rfl
    · exact False.elim (domain.zero_not_successor a impossible)
  · intro same
    exact Or.inl ⟨rfl, same⟩

theorem count_successor (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C) (x y : D) :
    member2 M C (modelSuccessor M x) y ↔ ∃ b, member2 M C x b ∧
      ((member M P x ∧ y = modelSuccessor M b) ∨ (¬ member M P x ∧ y = b)) := by
  rw [count_inversion M full least]
  constructor
  · rintro (⟨impossible, _⟩ | ⟨a, b, cab, same, output⟩)
    · exact False.elim (domain.zero_not_successor x impossible.symm)
    · have same' := domain.successor_injective x a same
      subst a
      exact ⟨b, cab, output⟩
  · rintro ⟨b, cab, output⟩
    exact Or.inr ⟨x, b, cab, rfl, output⟩

theorem count_total_unique (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C) :
    ∀ x, member M N x → ∃! y, member2 M C x y := by
  classical
  let predicates := pushPredicate (basePredicates M full) 1 C
  let parameters : ObjectAssignment D := fun _ => M.constantK
  have law : ∀ x, uniqueCountFormula.truth M (pushObject parameters x) predicates ↔
      ∃! y, member2 M C x y := by
    intro x
    simp only [uniqueCountFormula, Applicative.Formula.truth, binary_truth,
      Positive.Term.value, predicates, pushPredicate, pushObject, ExistsUnique, dite_true]
  apply induction_of_formula M domain uniqueCountFormula parameters predicates
    (fun x => ∃! y, member2 M C x y) law
  · exact ⟨modelZero M, least.closed.1,
      fun y cy => (count_zero M full domain least y).mp cy⟩
  · intro x _ ih
    obtain ⟨y, cxy, unique⟩ := ih
    by_cases px : member M P x
    · refine ⟨modelSuccessor M y, least.closed.2.1 x y cxy px, ?_⟩
      intro z csz
      obtain ⟨b, cxb, output⟩ := (count_successor M full domain least x z).mp csz
      rcases output with ⟨_, same⟩ | ⟨notpx, _⟩
      · exact same.trans (congrArg (modelSuccessor M) (unique b cxb))
      · exact False.elim (notpx px)
    · refine ⟨y, least.closed.2.2 x y cxy px, ?_⟩
      intro z csz
      obtain ⟨b, cxb, output⟩ := (count_successor M full domain least x z).mp csz
      rcases output with ⟨ispx, _⟩ | ⟨_, same⟩
      · exact False.elim (px ispx)
      · exact same.trans (unique b cxb)

/-- A new, proved arbitrary-Henkin-model checkpoint. It assumes only the
already constructed Peano domain and the actual full-comprehension schema. -/
theorem full_has_count_graph (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (P : R 0) :
    ∃ C : R 1, LeastCount M P C ∧
      (∀ x y, member2 M C x y → member M N x ∧ member M N y) ∧
      (∀ x, member M N x → ∃! y, member2 M C x y) := by
  obtain ⟨C, least⟩ := full_has_least_count M full P
  exact ⟨C, least, count_support M full domain least, count_total_unique M full domain least⟩

def countAtLeastFormula : Applicative.Formula :=
  .existsObject (.conjunction (binary 0 (.var 1) (.var 0))
    (binary 1 (.var 2) (.var 0)))

/-- Counts do not decrease along the available successor order. -/
theorem count_monotone (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C)
    {x y a b : D} (cxa : member2 M C x a) (cyb : member2 M C y b)
    (xy : Le M x y) : Le M a b := by
  classical
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  let predicates := pushPredicate (pushPredicate (basePredicates M full) 1 L) 1 C
  obtain ⟨Q, describes⟩ := full_comprehension_represents_unary_formula M full
    countAtLeastFormula (fun _ => a) predicates
  have law : ∀ z, member M Q z ↔ ∃ r, member2 M C z r ∧ Le M a r := by
    intro z
    simpa [countAtLeastFormula, Applicative.Formula.truth, binary_truth,
      Positive.Term.value, predicates, pushPredicate, pushObject, orderLaw] using describes z
  have closed : ∀ z, member M Q z → member M Q (modelSuccessor M z) := by
    intro z qz
    obtain ⟨r, czr, ar⟩ := (law z).mp qz
    by_cases pz : member M P z
    · exact (law _).mpr ⟨modelSuccessor M r, least.closed.2.1 z r czr pz, le_successor M ar⟩
    · exact (law _).mpr ⟨r, least.closed.2.2 z r czr pz, ar⟩
  obtain ⟨r, cyr, ar⟩ := (law y).mp (xy Q ((law x).mpr ⟨a, cxa, le_refl M a⟩) closed)
  obtain ⟨w, _, unique⟩ := count_total_unique M full domain least y
    (count_support M full domain least y b cyb).1
  have rb : r = b := (unique r cyr).trans (unique b cyb).symm
  exact rb ▸ ar

/-- Passing a predicate member strictly increases its count. -/
theorem count_strict_at_member (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C)
    {x y a b : D} (cxa : member2 M C x a) (cyb : member2 M C y b)
    (px : member M P x) (xy : Le M x y) (different : x ≠ y) :
    Le M (modelSuccessor M a) b :=
  count_monotone M full domain least (least.closed.2.1 x a cxa px) cyb
    (successor_le_of_le_ne M full xy different)

/-- The count before a member is its unique rank among all predicate members. -/
theorem rank_injective (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C)
    {x y a : D} (cxa : member2 M C x a) (cya : member2 M C y a)
    (px : member M P x) (py : member M P y) : x = y := by
  classical
  by_cases different : x = y
  · exact different
  apply False.elim
  have nx := (count_support M full domain least x a cxa).1
  have ny := (count_support M full domain least y a cya).1
  have na := (count_support M full domain least x a cxa).2
  rcases le_total M full domain x nx y ny with xy | yx
  · exact not_successor_le_self M full domain a na
      (count_strict_at_member M full domain least cxa cya px xy different)
  · exact not_successor_le_self M full domain a na
      (count_strict_at_member M full domain least cya cxa py yx (Ne.symm different))

def RanksBelow (M : Interpretation D R) (N P : R 0) (C : R 1) (x a : D) : Prop :=
  ∀ b, member M N b → Le M b a → b ≠ a →
    ∃ y, member M N y ∧ Le M y x ∧ y ≠ x ∧ member M P y ∧ member2 M C y b

def ranksBelowFormula : Applicative.Formula :=
  .forallObject (.implies (unary 1 (.var 0))
    (.implies (binary 1 (.var 0) (.var 2))
      (.implies (.implies (.equal (.var 0) (.var 2)) .falsum)
        (.existsObject (.conjunction (unary 1 (.var 0))
          (.conjunction (binary 1 (.var 0) (.var 2))
            (.conjunction (.implies (.equal (.var 0) (.var 2)) .falsum)
              (.conjunction (unary 0 (.var 0)) (binary 0 (.var 0) (.var 1))))))))))

theorem ranks_below_formula_truth (M : Interpretation D R)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R)
    {L : R 1} (orderLaw : RepresentsLe M L) (hl : predicates 1 1 = L) :
    ranksBelowFormula.truth M objects predicates ↔
      RanksBelow M (predicates 0 1) (predicates 0 0) (predicates 1 0) (objects 0) (objects 1) := by
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  simp only [ranksBelowFormula, Applicative.Formula.truth, unary, binary_truth,
    Positive.Term.value, pushObject, hl, orderLaw, RanksBelow, member]

/-- Every smaller count is attained exactly at an earlier predicate member. -/
theorem ranks_below (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C)
    {x a : D} (cxa : member2 M C x a) : RanksBelow M N P C x a := by
  classical
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  let predicates := pushPredicate (pushPredicate
    (pushPredicate (pushPredicate (basePredicates M full) 0 N) 0 P) 1 L) 1 C
  obtain ⟨Q, describes⟩ := full_represents_binary_formula M full
    (.conjunction (binary 0 (.var 0) (.var 1)) ranksBelowFormula) predicates
  have law : ∀ z b, member2 M Q z b ↔ member2 M C z b ∧ RanksBelow M N P C z b := by
    intro z b
    have evaluated := describes z b
    rw [Applicative.Formula.truth, binary_truth,
      ranks_below_formula_truth M _ predicates orderLaw rfl] at evaluated
    simpa [predicates, pushPredicate, assignTuple, pushObject, Positive.Term.value] using evaluated
  have liftWitness : ∀ z b, member M N z → RanksBelow M N P C z b →
      RanksBelow M N P C (modelSuccessor M z) b := by
    intro z b nz range r nr rb different
    obtain ⟨y, ny, yz, different', py, cyr⟩ := range r nr rb different
    refine ⟨y, ny, le_successor M yz, ?_, py, cyr⟩
    intro same
    exact not_successor_le_self M full domain z nz (same ▸ yz)
  have closed : CountClosed M P Q := by
    refine ⟨(law _ _).mpr ⟨least.closed.1, ?_⟩, ?_, ?_⟩
    · intro b _ bz different
      exact False.elim (different ((le_zero_iff M full domain b).mp bz))
    · intro z b qzb pz
      obtain ⟨czb, range⟩ := (law _ _).mp qzb
      have nz := (count_support M full domain least z b czb).1
      refine (law _ _).mpr ⟨least.closed.2.1 z b czb pz, ?_⟩
      intro r nr rsb different
      have rb : Le M r b := by
        rcases (le_successor_iff M full domain r b).mp rsb with rb | same
        · exact rb
        · exact False.elim (different same)
      by_cases same : r = b
      · subst r
        refine ⟨z, nz, le_self_successor M z, ?_, pz, czb⟩
        intro impossible
        exact not_successor_le_self M full domain z nz (impossible ▸ le_refl M z)
      · exact liftWitness z b nz range r nr rb same
    · intro z b qzb notpz
      obtain ⟨czb, range⟩ := (law _ _).mp qzb
      exact (law _ _).mpr ⟨least.closed.2.2 z b czb notpz,
        liftWitness z b (count_support M full domain least z b czb).1 range⟩
  exact ((law x a).mp (least.least Q closed x a cxa)).2

def Cofinal (M : Interpretation D R) (N P : R 0) : Prop :=
  ∀ x, member M N x → ∃ y, member M N y ∧ Le M x y ∧ member M P y

def memberAboveFormula : Applicative.Formula :=
  .conjunction (unary 0 (.var 0)) (binary 0 (.var 1) (.var 0))

/-- Any attained count is the rank of the next available predicate member.
The next member is obtained by the proved internal least-element principle. -/
theorem cofinal_rank_after_count (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C)
    (cofinal : Cofinal M N P) {x a : D} (cxa : member2 M C x a) :
    ∃ y, member M N y ∧ member M P y ∧ member2 M C y a := by
  classical
  have nx := (count_support M full domain least x a cxa).1
  have na := (count_support M full domain least x a cxa).2
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  let predicates := pushPredicate (pushPredicate (basePredicates M full) 0 P) 1 L
  obtain ⟨Q, describes⟩ := full_comprehension_represents_unary_formula M full
    memberAboveFormula (fun _ => x) predicates
  have law : ∀ y, member M Q y ↔ member M P y ∧ Le M x y := by
    intro y
    simpa [memberAboveFormula, Applicative.Formula.truth, unary, binary_truth,
      member, Positive.Term.value, predicates, pushPredicate, pushObject, orderLaw] using describes y
  obtain ⟨w, nw, xw, pw⟩ := cofinal x nx
  obtain ⟨y, ny, qy, minimum⟩ := least_available_member M full domain Q
    ⟨w, nw, (law w).mpr ⟨pw, xw⟩⟩
  obtain ⟨py, xy⟩ := (law y).mp qy
  obtain ⟨b, cyb, _⟩ := count_total_unique M full domain least y ny
  have ab := count_monotone M full domain least cxa cyb xy
  have same : a = b := by
    by_cases same : a = b
    · exact same
    apply False.elim
    obtain ⟨z, nz, zy, different, pz, cza⟩ := ranks_below M full domain least cyb a na ab same
    have xz : Le M x z := by
      rcases le_total M full domain x nx z nz with xz | zx
      · exact xz
      · by_cases same' : z = x
        · exact same' ▸ le_refl M z
        · exact False.elim (not_successor_le_self M full domain a na
            (count_strict_at_member M full domain least cza cxa pz zx same'))
    have yz := minimum z nz ((law z).mpr ⟨pz, xz⟩)
    exact different (le_antisymm M full domain nz zy yz)
  exact ⟨y, ny, py, same ▸ cyb⟩

def countOutputFormula : Applicative.Formula :=
  .existsObject (binary 0 (.var 0) (.var 1))

/-- For an unbounded available predicate, every internal natural is a count. -/
theorem cofinal_count_surjective (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C)
    (cofinal : Cofinal M N P) : ∀ a, member M N a → ∃ x, member2 M C x a := by
  let predicates := pushPredicate (basePredicates M full) 1 C
  let parameters : ObjectAssignment D := fun _ => M.constantK
  apply induction_of_formula M domain countOutputFormula parameters predicates
    (fun a => ∃ x, member2 M C x a)
  · intro a
    simp only [countOutputFormula, Applicative.Formula.truth, binary_truth,
      Positive.Term.value, predicates, pushPredicate, pushObject, dite_true]
  · exact ⟨modelZero M, least.closed.1⟩
  · intro a _ ih
    obtain ⟨x, cxa⟩ := ih
    obtain ⟨y, _, py, cya⟩ := cofinal_rank_after_count M full domain least cofinal cxa
    exact ⟨modelSuccessor M y, least.closed.2.1 y a cya py⟩

/-- The rank graph of an unbounded predicate is onto the entire interpreted
number domain; the witnessing graph is still the available count relation. -/
theorem cofinal_rank_surjective (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {C : R 1} (least : LeastCount M P C)
    (cofinal : Cofinal M N P) : ∀ a, member M N a →
      ∃ x, member M N x ∧ member M P x ∧ member2 M C x a := by
  intro a na
  obtain ⟨x, cxa⟩ := cofinal_count_surjective M full domain least cofinal a na
  exact cofinal_rank_after_count M full domain least cofinal cxa

def rankGraphFormula : Applicative.Formula :=
  .conjunction (unary 0 (.var 0)) (binary 0 (.var 0) (.var 1))

theorem full_has_rank_graph (M : Interpretation D R) (full : HasFullComprehension M)
    (P : R 0) (C : R 1) :
    ∃ G : R 1, ∀ x y, member2 M G x y ↔ member M P x ∧ member2 M C x y := by
  let predicates := pushPredicate (pushPredicate (basePredicates M full) 0 P) 1 C
  obtain ⟨G, describes⟩ := full_represents_binary_formula M full rankGraphFormula predicates
  refine ⟨G, ?_⟩
  intro x y
  simpa [rankGraphFormula, Applicative.Formula.truth, binary_truth, unary,
    predicates, pushPredicate, assignTuple, pushObject, Positive.Term.value, member]
    using describes x y

theorem cofinal_rank_bijection (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) (cofinal : Cofinal M N P) :
    ∃ G : R 1, GraphBijection M (OnNumbers M N P) (member M N) G := by
  obtain ⟨C, least⟩ := full_has_least_count M full P
  obtain ⟨G, law⟩ := full_has_rank_graph M full P C
  refine ⟨G, ?_⟩
  constructor
  · intro x y gxy
    obtain ⟨px, cxy⟩ := (law x y).mp gxy
    obtain ⟨nx, ny⟩ := count_support M full domain least x y cxy
    exact ⟨⟨nx, px⟩, ny⟩
  · rintro x ⟨nx, px⟩
    obtain ⟨y, cxy, _⟩ := count_total_unique M full domain least x nx
    exact ⟨y, (law x y).mpr ⟨px, cxy⟩⟩
  · intro y ny
    obtain ⟨x, _, px, cxy⟩ := cofinal_rank_surjective M full domain least cofinal y ny
    exact ⟨x, (law x y).mpr ⟨px, cxy⟩⟩
  · intro x y z gxy gxz
    obtain ⟨_, cxy⟩ := (law x y).mp gxy
    obtain ⟨_, cxz⟩ := (law x z).mp gxz
    obtain ⟨w, _, unique⟩ := count_total_unique M full domain least x
      (count_support M full domain least x y cxy).1
    exact (unique y cxy).trans (unique z cxz).symm
  · intro x y z gxz gyz
    obtain ⟨px, cxz⟩ := (law x z).mp gxz
    obtain ⟨py, cyz⟩ := (law y z).mp gyz
    exact rank_injective M full domain least cxz cyz px py

def Bounded (M : Interpretation D R) (N P : R 0) : Prop :=
  ∃ b, member M N b ∧ ∀ x, OnNumbers M N P x → Lt M x b

theorem bounded_has_finite_size (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) (bounded : Bounded M N P) :
    ∃ n, FiniteSize M N P n := by
  obtain ⟨b, nb, bound⟩ := bounded
  obtain ⟨C, least⟩ := full_has_least_count M full P
  obtain ⟨a, cba, _⟩ := count_total_unique M full domain least b nb
  have na := (count_support M full domain least b a cba).2
  obtain ⟨G, law⟩ := full_has_rank_graph M full P C
  refine ⟨a, na, G, ?_⟩
  constructor
  · intro x y gxy
    obtain ⟨px, cxy⟩ := (law x y).mp gxy
    obtain ⟨nx, ny⟩ := count_support M full domain least x y cxy
    obtain ⟨xb, different⟩ := bound x ⟨nx, px⟩
    have sya := count_strict_at_member M full domain least cxy cba px xb different
    refine ⟨⟨nx, px⟩, ny, le_trans M (le_self_successor M y) sya, ?_⟩
    intro same
    exact not_successor_le_self M full domain y ny (same ▸ sya)
  · rintro x ⟨nx, px⟩
    obtain ⟨y, cxy, _⟩ := count_total_unique M full domain least x nx
    exact ⟨y, (law x y).mpr ⟨px, cxy⟩⟩
  · rintro y ⟨ny, ya, different⟩
    obtain ⟨x, _, _, _, px, cxy⟩ := ranks_below M full domain least cba y ny ya different
    exact ⟨x, (law x y).mpr ⟨px, cxy⟩⟩
  · intro x y z gxy gxz
    obtain ⟨_, cxy⟩ := (law x y).mp gxy
    obtain ⟨_, cxz⟩ := (law x z).mp gxz
    obtain ⟨w, _, unique⟩ := count_total_unique M full domain least x
      (count_support M full domain least x y cxy).1
    exact (unique y cxy).trans (unique z cxz).symm
  · intro x y z gxz gyz
    obtain ⟨px, cxz⟩ := (law x z).mp gxz
    obtain ⟨py, cyz⟩ := (law y z).mp gyz
    exact rank_injective M full domain least cxz cyz px py

theorem bounded_or_cofinal (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) : Bounded M N P ∨ Cofinal M N P := by
  classical
  by_cases bounded : Bounded M N P
  · exact Or.inl bounded
  right
  intro x nx
  by_cases found : ∃ y, member M N y ∧ Le M x y ∧ member M P y
  · exact found
  apply False.elim
  apply bounded
  refine ⟨x, nx, ?_⟩
  rintro y ⟨ny, py⟩
  have notxy : ¬ Le M x y := fun xy => found ⟨y, ny, xy, py⟩
  refine ⟨?_, ?_⟩
  · rcases le_total M full domain x nx y ny with xy | yx
    · exact False.elim (notxy xy)
    · exact yx
  · intro same
    exact notxy (same ▸ le_refl M y)

/-- Every available predicate on the internal numbers has either an internal
finite size or an available bijection with all internal numbers. -/
theorem predicate_cardinality_cases (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (P : R 0) :
    (∃ n, FiniteSize M N P n) ∨
      ∃ G : R 1, GraphBijection M (OnNumbers M N P) (member M N) G := by
  rcases bounded_or_cofinal M full domain (P := P) with bounded | cofinal
  · exact Or.inl (bounded_has_finite_size M full domain bounded)
  · exact Or.inr (cofinal_rank_bijection M full domain cofinal)

end FregeanECA.Part2.HumeCounting
