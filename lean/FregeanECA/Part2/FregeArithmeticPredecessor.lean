import FregeanECA.Part2.FregeArithmeticBasic

/-! The two uniqueness laws for generic Fregean predecession. Each graph
modification is supplied by an explicit source-language comprehension
instance, rather than assuming arbitrary functions or their graphs exist. -/
namespace FregeanECA.Part2.FregeArithmetic
open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

theorem GraphBijection.congr {M : Interpretation D R} {G : R 1}
    {A B A' B' : D → Prop} (bij : GraphBijection M A B G)
    (left : ∀ x, A x ↔ A' x) (right : ∀ x, B x ↔ B' x) : GraphBijection M A' B' G where
  support := fun x y h => ⟨(left x).mp (bij.support x y h).1,
    (right y).mp (bij.support x y h).2⟩
  total := fun x h => bij.total x ((left x).mpr h)
  onto := fun y h => bij.onto y ((right y).mpr h)
  functional := bij.functional
  injective := bij.injective

theorem full_has_adjoined_graph (M : Interpretation D R) (full : HasFullComprehension M)
    (G : R 1) (a b : D) : ∃ H : R 1, ∀ x y,
      member2 M H x y ↔ member2 M G x y ∨ (x = a ∧ y = b) := by
  let predicates := pushPredicate (basePredicates M full) 1 G
  let objects : ObjectAssignment D := pushObject (fun _ => b) a
  obtain ⟨H, law⟩ := full_represents_binary M full
    (.disjunction (binary 0 (.var 0) (.var 1))
      (.conjunction (.equal (.var 0) (.var 2)) (.equal (.var 1) (.var 3)))) objects predicates
  refine ⟨H, ?_⟩
  intro x y
  simpa [Formula.truth, binary_truth, Term.value, predicates, objects,
    pushPredicate, assignTuple, pushObject] using law x y

theorem bijection_adjoin (M : Interpretation D R) (full : HasFullComprehension M)
    {A B : D → Prop} {G : R 1} (bij : GraphBijection M A B G)
    (a b : D) (na : ¬ A a) (nb : ¬ B b) :
    ∃ H : R 1, GraphBijection M (fun x => A x ∨ x = a) (fun y => B y ∨ y = b) H := by
  obtain ⟨H, law⟩ := full_has_adjoined_graph M full G a b
  refine ⟨H, ?_⟩
  constructor
  · intro x y h
    rcases (law x y).mp h with old | ⟨rfl, rfl⟩
    · exact ⟨Or.inl (bij.support x y old).1, Or.inl (bij.support x y old).2⟩
    · exact ⟨Or.inr rfl, Or.inr rfl⟩
  · intro x hx
    rcases hx with old | rfl
    · obtain ⟨y, gxy⟩ := bij.total x old
      exact ⟨y, (law x y).mpr (Or.inl gxy)⟩
    · exact ⟨b, (law x b).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro y hy
    rcases hy with old | rfl
    · obtain ⟨x, gxy⟩ := bij.onto y old
      exact ⟨x, (law x y).mpr (Or.inl gxy)⟩
    · exact ⟨a, (law a y).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro x y z hxy hxz
    rcases (law x y).mp hxy with gxy | ⟨rfl, rfl⟩
    · rcases (law x z).mp hxz with gxz | ⟨rfl, _⟩
      · exact bij.functional x y z gxy gxz
      · exact False.elim (na (bij.support x y gxy).1)
    · rcases (law x z).mp hxz with gaz | ⟨_, rfl⟩
      · exact False.elim (na (bij.support x z gaz).1)
      · rfl
  · intro x y z hxz hyz
    rcases (law x z).mp hxz with gxz | ⟨rfl, rfl⟩
    · rcases (law y z).mp hyz with gyz | ⟨_, rfl⟩
      · exact bij.injective x y z gxz gyz
      · exact False.elim (nb (bij.support x z gxz).2)
    · rcases (law y z).mp hyz with gyb | ⟨rfl, _⟩
      · exact False.elim (nb (bij.support y z gyb).2)
      · rfl

theorem deletion_rejoin {M : Interpretation D R} {F G : R 0} {a : D}
    (fa : member M F a) (deletion : ∀ x, member M G x ↔ member M F x ∧ x ≠ a) :
    ∀ x, (member M G x ∨ x = a) ↔ member M F x := by
  classical
  intro x
  constructor
  · rintro (gx | rfl)
    · exact ((deletion x).mp gx).1
    · exact fa
  · intro fx
    by_cases same : x = a
    · exact Or.inr same
    · exact Or.inl ((deletion x).mpr ⟨fx, same⟩)

/-- A number has at most one immediate successor. -/
theorem predecession_functional (M : Interpretation D R) (full : FullConditions M)
    {m n p : D} (mn : Precedes M m n) (mp : Precedes M m p) : n = p := by
  obtain ⟨F, G, a, fa, deletion, gm, fn⟩ := mn
  obtain ⟨F', G', b, fb, deletion', g'm, f'p⟩ := mp
  obtain ⟨B, bij⟩ := (full.hume G G').mp (gm.trans g'm.symm)
  have na : ¬ member M G a := fun ga => ((deletion a).mp ga).2 rfl
  have nb : ¬ member M G' b := fun gb => ((deletion' b).mp gb).2 rfl
  obtain ⟨H, extended⟩ := bijection_adjoin M full.comprehension bij a b na nb
  have same := (full.hume F F').mpr ⟨H,
    extended.congr (deletion_rejoin fa deletion) (deletion_rejoin fb deletion')⟩
  exact fn.symm.trans (same.trans f'p)

/-- Remove a specified point from each side, redirecting the preimage of b
to the old image w of a. All parameters are ordinary object parameters. -/
theorem full_has_deleted_graph (M : Interpretation D R) (full : HasFullComprehension M)
    (G : R 1) (a b w : D) : ∃ H : R 1, ∀ x y,
      member2 M H x y ↔ x ≠ a ∧ y ≠ b ∧
        ((member2 M G x y ∧ y ≠ w) ∨ (member2 M G x b ∧ y = w)) := by
  let predicates := pushPredicate (basePredicates M full) 1 G
  let objects : ObjectAssignment D := pushObject (pushObject (fun _ => w) b) a
  let formula : Formula :=
    .conjunction (notFormula (.equal (.var 0) (.var 2)))
      (.conjunction (notFormula (.equal (.var 1) (.var 3)))
        (.disjunction
          (.conjunction (binary 0 (.var 0) (.var 1)) (notFormula (.equal (.var 1) (.var 4))))
          (.conjunction (binary 0 (.var 0) (.var 3)) (.equal (.var 1) (.var 4)))))
  obtain ⟨H, law⟩ := full_represents_binary M full formula objects predicates
  refine ⟨H, ?_⟩
  intro x y
  simpa [formula, Formula.truth, notFormula, binary_truth, Term.value, predicates, objects,
    pushPredicate, assignTuple, pushObject] using law x y

theorem bijection_delete (M : Interpretation D R) (full : HasFullComprehension M)
    {A B : D → Prop} {G : R 1} (bij : GraphBijection M A B G)
    (a b : D) (aa : A a) (bb : B b) :
    ∃ H : R 1, GraphBijection M (fun x => A x ∧ x ≠ a) (fun y => B y ∧ y ≠ b) H := by
  classical
  obtain ⟨w, gaw⟩ := bij.total a aa
  obtain ⟨H, law⟩ := full_has_deleted_graph M full G a b w
  refine ⟨H, ?_⟩
  constructor
  · intro x y h
    obtain ⟨xa, yb, old⟩ := (law x y).mp h
    rcases old with ⟨gxy, _⟩ | ⟨gxb, rfl⟩
    · exact ⟨⟨(bij.support x y gxy).1, xa⟩, (bij.support x y gxy).2, yb⟩
    · exact ⟨⟨(bij.support x b gxb).1, xa⟩, (bij.support a y gaw).2, yb⟩
  · rintro x ⟨ax, xa⟩
    obtain ⟨y, gxy⟩ := bij.total x ax
    have yw : y ≠ w := fun same => xa (bij.injective x a w (same ▸ gxy) gaw)
    by_cases yb : y = b
    · subst y
      exact ⟨w, (law x w).mpr ⟨xa, Ne.symm yw, Or.inr ⟨gxy, rfl⟩⟩⟩
    · exact ⟨y, (law x y).mpr ⟨xa, yb, Or.inl ⟨gxy, yw⟩⟩⟩
  · rintro y ⟨by', yb⟩
    by_cases yw : y = w
    · subst y
      obtain ⟨x, gxb⟩ := bij.onto b bb
      have xa : x ≠ a := by
        intro same
        have bw := bij.functional a b w (same ▸ gxb) gaw
        exact yb bw.symm
      exact ⟨x, (law x w).mpr ⟨xa, yb, Or.inr ⟨gxb, rfl⟩⟩⟩
    · obtain ⟨x, gxy⟩ := bij.onto y by'
      have xa : x ≠ a := fun same => yw (bij.functional a y w (same ▸ gxy) gaw)
      exact ⟨x, (law x y).mpr ⟨xa, yb, Or.inl ⟨gxy, yw⟩⟩⟩
  · intro x y z hxy hxz
    obtain ⟨_, yb, oldy⟩ := (law x y).mp hxy
    obtain ⟨_, zb, oldz⟩ := (law x z).mp hxz
    rcases oldy with ⟨gxy, _⟩ | ⟨gxb, rfl⟩
    · rcases oldz with ⟨gxz, _⟩ | ⟨gxb, _⟩
      · exact bij.functional x y z gxy gxz
      · exact False.elim (yb (bij.functional x y b gxy gxb))
    · rcases oldz with ⟨gxz, _⟩ | ⟨_, rfl⟩
      · exact False.elim (zb (bij.functional x z b gxz gxb))
      · rfl
  · intro x y z hxz hyz
    obtain ⟨_, _, oldx⟩ := (law x z).mp hxz
    obtain ⟨_, _, oldy⟩ := (law y z).mp hyz
    rcases oldx with ⟨gxz, zw⟩ | ⟨gxb, rfl⟩
    · rcases oldy with ⟨gyz, _⟩ | ⟨_, same⟩
      · exact bij.injective x y z gxz gyz
      · exact False.elim (zw same)
    · rcases oldy with ⟨_, impossible⟩ | ⟨gyb, _⟩
      · exact False.elim (impossible rfl)
      · exact bij.injective x y b gxb gyb

/-- A number has at most one immediate predecessor. -/
theorem predecession_injective (M : Interpretation D R) (full : FullConditions M)
    {m n p : D} (mn : Precedes M m n) (pn : Precedes M p n) : m = p := by
  obtain ⟨F, G, a, fa, deletion, gm, fn⟩ := mn
  obtain ⟨F', G', b, fb, deletion', g'p, f'n⟩ := pn
  obtain ⟨B, bij⟩ := (full.hume F F').mp (fn.trans f'n.symm)
  obtain ⟨H, deleted⟩ := bijection_delete M full.comprehension bij a b fa fb
  have same := (full.hume G G').mpr ⟨H,
    deleted.congr (fun x => (deletion x).symm) (fun x => (deletion' x).symm)⟩
  exact gm.symm.trans (same.trans g'p)

end FregeanECA.Part2.FregeArithmetic
