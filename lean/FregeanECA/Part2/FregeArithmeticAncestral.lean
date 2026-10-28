import FregeanECA.Part2.FregeArithmeticPredecessor

/-! Frege's natural-number domain is the reflexive ancestral of predecession
from the number of the empty concept. All ancestral and induction predicates
are supplied by actual source-language comprehension instances. -/
namespace FregeanECA.Part2.FregeArithmetic
open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

def Ancestral (M : Interpretation D R) (a b : D) : Prop :=
  ∀ X : R 0, member M X a →
    (∀ x y, member M X x → Precedes M x y → member M X y) → member M X b

def ancestralFormula : Formula :=
  .forallPredicate 0 (.implies
    (.conjunction (unary 0 (.var 0))
      (.forallObject (.forallObject
        (.implies (.conjunction (unary 0 (.var 1)) (binary 0 (.var 1) (.var 0)))
          (unary 0 (.var 0))))))
    (unary 0 (.var 1)))

theorem ancestral_formula_truth (M : Interpretation D R)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R)
    (law : ∀ x y, member2 M (predicates 1 0) x y ↔ Precedes M x y) :
    ancestralFormula.truth M objects predicates ↔ Ancestral M (objects 0) (objects 1) := by
  simp [ancestralFormula, Formula.truth, unary, binary_truth, Term.value,
    pushPredicate, pushObject, Ancestral, member, and_imp, law]

theorem full_has_ancestral (M : Interpretation D R) (full : HasFullComprehension M) :
    ∃ A : R 1, ∀ x y, member2 M A x y ↔ Ancestral M x y := by
  obtain ⟨P, precedes⟩ := full_has_predecession M full
  let predicates := pushPredicate (basePredicates M full) 1 P
  obtain ⟨A, law⟩ := full_represents_binary M full ancestralFormula (baseObjects M full) predicates
  refine ⟨A, ?_⟩
  intro x y
  exact (law x y).trans (ancestral_formula_truth M _ predicates precedes)

theorem ancestral_refl (M : Interpretation D R) (x : D) : Ancestral M x x :=
  fun _ hx _ => hx

theorem ancestral_step (M : Interpretation D R) {x y z : D}
    (xy : Ancestral M x y) (yz : Precedes M y z) : Ancestral M x z :=
  fun P px closed => closed y z (xy P px closed) yz

theorem ancestral_edge (M : Interpretation D R) {x y : D}
    (xy : Precedes M x y) : Ancestral M x y :=
  ancestral_step M (ancestral_refl M x) xy

theorem ancestral_trans (M : Interpretation D R) {x y z : D}
    (xy : Ancestral M x y) (yz : Ancestral M y z) : Ancestral M x z :=
  fun P px closed => yz P (xy P px closed) closed

def rollbackFormula : Formula :=
  .disjunction (.equal (.var 0) (.var 1))
    (.existsObject (.conjunction (binary 0 (.var 2) (.var 0))
      (binary 1 (.var 0) (.var 1))))

theorem ancestral_rollback (M : Interpretation D R) (full : HasFullComprehension M)
    (a b : D) : Ancestral M a b ↔ b = a ∨ ∃ x, Ancestral M a x ∧ Precedes M x b := by
  obtain ⟨A, ancestral⟩ := full_has_ancestral M full
  obtain ⟨P, precedes⟩ := full_has_predecession M full
  let predicates := pushPredicate (pushPredicate (basePredicates M full) 1 P) 1 A
  obtain ⟨Q, describes⟩ := full_represents_unary M full rollbackFormula (fun _ => a) predicates
  have law : ∀ b, member M Q b ↔ b = a ∨ ∃ x, Ancestral M a x ∧ Precedes M x b := by
    intro b
    simpa [rollbackFormula, Formula.truth, binary_truth, Term.value, predicates,
      pushPredicate, pushObject, ancestral, precedes] using describes b
  have included : ∀ b, member M Q b → Ancestral M a b := by
    intro b qb
    rcases (law b).mp qb with rfl | ⟨x, ax, xb⟩
    · exact ancestral_refl M _
    · exact ancestral_step M ax xb
  constructor
  · intro ab
    apply (law b).mp
    apply ab Q ((law a).mpr (Or.inl rfl))
    intro x y qx xy
    exact (law y).mpr (Or.inr ⟨x, included x qx, xy⟩)
  · intro rhs
    exact included b ((law b).mpr rhs)

def Natural (M : Interpretation D R) (full : HasFullComprehension M) (n : D) : Prop :=
  Ancestral M (zero M full) n

theorem natural_zero (M : Interpretation D R) (full : HasFullComprehension M) :
    Natural M full (zero M full) := ancestral_refl M _

theorem natural_successor (M : Interpretation D R) (full : HasFullComprehension M)
    {x y : D} (nx : Natural M full x) (xy : Precedes M x y) : Natural M full y :=
  ancestral_step M nx xy

theorem full_has_natural (M : Interpretation D R) (full : HasFullComprehension M) :
    ∃ N : R 0, ∀ n, member M N n ↔ Natural M full n := by
  obtain ⟨A, ancestral⟩ := full_has_ancestral M full
  let predicates := pushPredicate (basePredicates M full) 1 A
  obtain ⟨N, law⟩ := full_represents_unary M full (binary 0 (.var 1) (.var 0))
    (fun _ => zero M full) predicates
  refine ⟨N, ?_⟩
  intro n
  simpa [binary_truth, Term.value, predicates, pushPredicate, pushObject, ancestral, Natural]
    using law n

theorem natural_predicate_induction (M : Interpretation D R) (full : HasFullComprehension M)
    (Q : R 0) (base : member M Q (zero M full))
    (step : ∀ x y, Natural M full x → member M Q x → Precedes M x y → member M Q y) :
    ∀ n, Natural M full n → member M Q n := by
  obtain ⟨N, natural⟩ := full_has_natural M full
  let predicates := pushPredicate (pushPredicate (basePredicates M full) 0 N) 0 Q
  obtain ⟨H, law⟩ := full_represents_unary M full
    (.conjunction (unary 1 (.var 0)) (unary 0 (.var 0))) (baseObjects M full) predicates
  have describes : ∀ n, member M H n ↔ Natural M full n ∧ member M Q n := by
    intro n
    have h := law n
    change member M H n ↔ member M N n ∧ member M Q n at h
    exact h.trans (and_congr (natural n) Iff.rfl)
  have closed : ∀ x y, member M H x → Precedes M x y → member M H y := by
    intro x y hx xy
    obtain ⟨nx, qx⟩ := (describes x).mp hx
    exact (describes y).mpr ⟨natural_successor M full nx xy, step x y nx qx xy⟩
  intro n nn
  exact ((describes n).mp (nn H ((describes _).mpr ⟨natural_zero M full, base⟩) closed)).2

theorem natural_formula_induction (M : Interpretation D R) (full : HasFullComprehension M)
    (formula : Formula) (objects : ObjectAssignment D) (predicates : PredicateAssignment R)
    (property : D → Prop)
    (law : ∀ x, formula.truth M (pushObject objects x) predicates ↔ property x)
    (base : property (zero M full))
    (step : ∀ x y, Natural M full x → property x → Precedes M x y → property y) :
    ∀ x, Natural M full x → property x := by
  obtain ⟨Q, describes⟩ := full_represents_unary M full formula objects predicates
  have qlaw : ∀ x, member M Q x ↔ property x := fun x => (describes x).trans (law x)
  intro x nx
  exact (qlaw x).mp (natural_predicate_induction M full Q ((qlaw _).mpr base)
    (fun a b na qa ab => (qlaw b).mpr (step a b na ((qlaw a).mp qa) ab)) x nx)

theorem ancestral_to_zero (M : Interpretation D R) (full : FullConditions M) (x : D) :
    Ancestral M x (zero M full.comprehension) ↔ x = zero M full.comprehension := by
  rw [ancestral_rollback M full.comprehension]
  constructor
  · rintro (same | ⟨y, _, impossible⟩)
    · exact same.symm
    · exact False.elim (zero_has_no_predecessor M full y impossible)
  · intro same
    exact Or.inl same.symm

def noBackEdgeFormula : Formula :=
  .forallObject (.implies (binary 0 (.var 1) (.var 0))
    (notFormula (binary 1 (.var 0) (.var 1))))

theorem natural_no_back_edge (M : Interpretation D R) (full : FullConditions M) :
    ∀ x, Natural M full.comprehension x →
      ∀ y, Precedes M x y → ¬ Ancestral M y x := by
  obtain ⟨P, precedes⟩ := full_has_predecession M full.comprehension
  obtain ⟨A, ancestral⟩ := full_has_ancestral M full.comprehension
  let predicates := pushPredicate (pushPredicate (basePredicates M full.comprehension) 1 A) 1 P
  apply natural_formula_induction M full.comprehension noBackEdgeFormula
    (baseObjects M full.comprehension) predicates
    (fun x => ∀ y, Precedes M x y → ¬ Ancestral M y x)
  · intro x
    simp [noBackEdgeFormula, Formula.truth, notFormula, binary_truth, Term.value,
      predicates, pushPredicate, pushObject, ancestral, precedes]
  · intro y zy yz
    have same := (ancestral_to_zero M full y).mp yz
    exact zero_has_no_predecessor M full _ (same ▸ zy)
  · intro x y _ ih xy z yz zy
    rcases (ancestral_rollback M full.comprehension z y).mp zy with same | ⟨w, zw, wy⟩
    · have same' : x = y := predecession_injective M full (same ▸ xy) yz
      subst x
      exact ih y xy (ancestral_refl M y)
    · have wx : w = x := predecession_injective M full wy xy
      exact ih y xy (ancestral_trans M (ancestral_edge M yz) (wx ▸ zw))

end FregeanECA.Part2.FregeArithmetic
