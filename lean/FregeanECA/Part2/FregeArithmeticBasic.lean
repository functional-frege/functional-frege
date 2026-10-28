import FregeanECA.Part2.FregeArithmeticSyntax

/-! Generic first steps of Frege's theorem, from source-language full
comprehension and HP alone. The object domain need not be an arithmetic
domain; none of the results assumes a pre-existing successor or induction. -/

namespace FregeanECA.Part2.FregeArithmetic
open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

noncomputable def basePredicates (M : Interpretation D R)
    (full : HasFullComprehension M) : PredicateAssignment R :=
  fun n _ => Classical.choice (full.relations_nonempty n)

noncomputable def baseObjects (M : Interpretation D R)
    (full : HasFullComprehension M) : ObjectAssignment D :=
  fun _ => M.number (basePredicates M full 0 0)

theorem full_represents_unary (M : Interpretation D R) (full : HasFullComprehension M)
    (formula : Formula) (objects : ObjectAssignment D) (predicates : PredicateAssignment R) :
    ∃ P : R 0, ∀ x, member M P x ↔ formula.truth M (pushObject objects x) predicates := by
  obtain ⟨P, law⟩ := full.comprehend 0 formula objects predicates
  exact ⟨P, fun x => law (fun _ => x)⟩

theorem full_represents_binary (M : Interpretation D R) (full : HasFullComprehension M)
    (formula : Formula) (objects : ObjectAssignment D) (predicates : PredicateAssignment R) :
    ∃ G : R 1, ∀ x y, member2 M G x y ↔
      formula.truth M (assignTuple 2 (pair x y) objects) predicates := by
  obtain ⟨G, law⟩ := full.comprehend 1 formula objects predicates
  exact ⟨G, fun x y => law (pair x y)⟩

theorem full_has_empty (M : Interpretation D R) (full : HasFullComprehension M) (n : Nat) :
    ∃ E : R n, ∀ arguments, ¬ M.satisfies n E arguments := by
  obtain ⟨E, law⟩ := full.comprehend n .falsum (baseObjects M full) (basePredicates M full)
  exact ⟨E, fun arguments h => (law arguments).mp h⟩

noncomputable def emptyPredicate (M : Interpretation D R) (full : HasFullComprehension M) : R 0 :=
  Classical.choose (full_has_empty M full 0)

theorem empty_predicate (M : Interpretation D R) (full : HasFullComprehension M) (x : D) :
    ¬ member M (emptyPredicate M full) x :=
  Classical.choose_spec (full_has_empty M full 0) (fun _ => x)

noncomputable def zero (M : Interpretation D R) (full : HasFullComprehension M) : D :=
  M.number (emptyPredicate M full)

theorem full_has_singleton (M : Interpretation D R) (full : HasFullComprehension M) (a : D) :
    ∃ S : R 0, ∀ x, member M S x ↔ x = a := by
  obtain ⟨S, law⟩ := full_represents_unary M full (.equal (.var 0) (.var 1))
    (fun _ => a) (basePredicates M full)
  exact ⟨S, law⟩

theorem full_has_deletion (M : Interpretation D R) (full : HasFullComprehension M)
    (P : R 0) (a : D) : ∃ Q : R 0, ∀ x, member M Q x ↔ member M P x ∧ x ≠ a := by
  let predicates := pushPredicate (basePredicates M full) 0 P
  obtain ⟨Q, law⟩ := full_represents_unary M full
    (.conjunction (unary 0 (.var 0)) (notFormula (.equal (.var 0) (.var 1))))
    (fun _ => a) predicates
  exact ⟨Q, law⟩

theorem full_has_identity_graph (M : Interpretation D R) (full : HasFullComprehension M)
    (P : R 0) : ∃ G : R 1, ∀ x y, member2 M G x y ↔ member M P x ∧ x = y := by
  let predicates := pushPredicate (basePredicates M full) 0 P
  obtain ⟨G, law⟩ := full_represents_binary M full
    (.conjunction (unary 0 (.var 0)) (.equal (.var 0) (.var 1)))
    (baseObjects M full) predicates
  refine ⟨G, ?_⟩
  intro x y
  simpa [Formula.truth, unary, Term.value, member, predicates,
    pushPredicate, assignTuple, pushObject] using law x y

/-- Coextensive concepts have the same number; its bijection witness is the
available identity graph restricted to the concept. -/
theorem number_eq_of_coextension (M : Interpretation D R) (full : FullConditions M)
    {P Q : R 0} (same : ∀ x, member M P x ↔ member M Q x) : M.number P = M.number Q := by
  obtain ⟨G, law⟩ := full_has_identity_graph M full.comprehension P
  apply (full.hume P Q).mpr
  refine ⟨G, ?_⟩
  constructor
  · intro x y gxy
    obtain ⟨px, rfl⟩ := (law x y).mp gxy
    exact ⟨px, (same x).mp px⟩
  · intro x px
    exact ⟨x, (law x x).mpr ⟨px, rfl⟩⟩
  · intro y qy
    exact ⟨y, (law y y).mpr ⟨(same y).mpr qy, rfl⟩⟩
  · intro x y z gxy gxz
    exact ((law x y).mp gxy).2.symm.trans ((law x z).mp gxz).2
  · intro x y z gxz gyz
    exact ((law x z).mp gxz).2.trans ((law y z).mp gyz).2.symm

theorem number_zero_iff_empty (M : Interpretation D R) (full : FullConditions M) (P : R 0) :
    M.number P = zero M full.comprehension ↔ ∀ x, ¬ member M P x := by
  constructor
  · intro same x px
    obtain ⟨G, bij⟩ := (full.hume P (emptyPredicate M full.comprehension)).mp same
    obtain ⟨y, gxy⟩ := bij.total x px
    exact empty_predicate M full.comprehension y (bij.support x y gxy).2
  · intro empty
    apply number_eq_of_coextension M full
    intro x
    exact ⟨fun px => False.elim (empty x px),
      fun ex => False.elim (empty_predicate M full.comprehension x ex)⟩

/-- HP itself supplies nontriviality: the numbers of empty and singleton
concepts are distinct. No infinity or arithmetic premise is introduced. -/
theorem at_least_two_objects (M : Interpretation D R) (full : FullConditions M) :
    ∃ a b : D, a ≠ b := by
  obtain ⟨S, singleton⟩ := full_has_singleton M full.comprehension (zero M full.comprehension)
  refine ⟨M.number S, zero M full.comprehension, ?_⟩
  intro same
  exact (number_zero_iff_empty M full S).mp same _ ((singleton _).mpr rfl)

/-- Standard Fregean predecession, with the deleted concept explicit as an
available unary predicate. Read `Precedes m n` as n immediately follows m. -/
def Precedes (M : Interpretation D R) (m n : D) : Prop :=
  ∃ F G : R 0, ∃ z : D, member M F z ∧
    (∀ x, member M G x ↔ member M F x ∧ x ≠ z) ∧ M.number G = m ∧ M.number F = n

def predecessionFormula : Formula :=
  .existsPredicate 0 (.existsPredicate 0 (.existsObject
    (.conjunction (unary 1 (.var 0))
      (.conjunction
        (.forallObject (iffFormula (unary 0 (.var 0))
          (.conjunction (unary 1 (.var 0)) (notFormula (.equal (.var 0) (.var 1))))))
        (.conjunction (.equal (.number 0) (.var 1)) (.equal (.number 1) (.var 2)))))))

theorem predecession_formula_truth (M : Interpretation D R)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R) :
    predecessionFormula.truth M objects predicates ↔ Precedes M (objects 0) (objects 1) := by
  have iffTruth (o : ObjectAssignment D) (r : PredicateAssignment R) (p q : Formula) :
      (iffFormula p q).truth M o r ↔ (p.truth M o r ↔ q.truth M o r) :=
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩
  simp only [predecessionFormula, Formula.truth, unary, iffTruth, notFormula,
    Term.value, pushPredicate, pushObject, member, dite_true, Precedes]

theorem full_has_predecession (M : Interpretation D R) (full : HasFullComprehension M) :
    ∃ G : R 1, ∀ x y, member2 M G x y ↔ Precedes M x y := by
  obtain ⟨G, law⟩ := full_represents_binary M full predecessionFormula
    (baseObjects M full) (basePredicates M full)
  refine ⟨G, ?_⟩
  intro x y
  exact (law x y).trans (predecession_formula_truth M _ _)

theorem zero_has_no_predecessor (M : Interpretation D R) (full : FullConditions M) (m : D) :
    ¬ Precedes M m (zero M full.comprehension) := by
  rintro ⟨F, G, z, fz, _, _, same⟩
  exact (number_zero_iff_empty M full F).mp same z fz

theorem deletion_precedes (M : Interpretation D R) (full : HasFullComprehension M)
    (F : R 0) (z : D) (fz : member M F z) :
    ∃ G : R 0, (∀ x, member M G x ↔ member M F x ∧ x ≠ z) ∧
      Precedes M (M.number G) (M.number F) := by
  obtain ⟨G, deletion⟩ := full_has_deletion M full F z
  exact ⟨G, deletion, F, G, z, fz, deletion, rfl, rfl⟩

theorem zero_has_a_successor (M : Interpretation D R) (full : FullConditions M) :
    ∃ n, Precedes M (zero M full.comprehension) n := by
  let z := zero M full.comprehension
  obtain ⟨S, singleton⟩ := full_has_singleton M full.comprehension z
  obtain ⟨G, deletion, precedes⟩ := deletion_precedes M full.comprehension S z ((singleton z).mpr rfl)
  have empty : ∀ x, ¬ member M G x := by
    intro x gx
    obtain ⟨sx, different⟩ := (deletion x).mp gx
    exact different ((singleton x).mp sx)
  have same := (number_zero_iff_empty M full G).mpr empty
  exact ⟨M.number S, same ▸ precedes⟩

end FregeanECA.Part2.FregeArithmetic
