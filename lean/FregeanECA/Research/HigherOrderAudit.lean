import Std

/-!
# Separate research audit: higher-order rows and unrestricted functional reflection

This file is deliberately outside the Version 2 paper certificate. It proves
conditional lemmas about explicit higher-order proposals, not a consistency
result or a formal translation of an unspecified raised A2.
-/

namespace FregeanECA.Research.HigherOrderAudit

universe u v w
variable {D : Type u} {C : Type v} {H : Type w}

/-- The proposed row takes a concept as input and returns one of two objects. -/
def IsRow (evaluate : H → C → D) (top bottom : D) (E : C → C → Prop)
    (concept : C) (row : H) : Prop :=
  ∀ argument, (E concept argument → evaluate row argument = top) ∧
    (¬ E concept argument → evaluate row argument = bottom)

/-- Equivalence rows plus a same-sort functional value-range law give the
corresponding abstraction biconditional. No function-identity axiom is needed. -/
theorem rows_give_abstraction (evaluate : H → C → D) (code : H → D)
    (top bottom : D) (distinct : top ≠ bottom) (E : C → C → Prop)
    (reflexive : ∀ P, E P P) (symmetric : ∀ P Q, E P Q → E Q P)
    (transitive : ∀ P Q U, E P Q → E Q U → E P U)
    (valueRange : ∀ r s, code r = code s ↔ ∀ P, evaluate r P = evaluate s P)
    (P Q : C) (r s : H) (rRow : IsRow evaluate top bottom E P r)
    (sRow : IsRow evaluate top bottom E Q s) :
    code r = code s ↔ E P Q := by
  classical
  constructor
  · intro codesEqual
    have atQ := (valueRange r s).mp codesEqual Q
    have sTop := (sRow Q).1 (reflexive Q)
    apply Classical.byContradiction
    intro notRelated
    have rBottom := (rRow Q).2 notRelated
    exact distinct (sTop.symm.trans (atQ.symm.trans rBottom))
  · intro related
    apply (valueRange r s).mpr
    intro U
    by_cases first : E P U
    · have second : E Q U := transitive Q P U (symmetric P Q related) first
      exact ((rRow U).1 first).trans ((sRow U).1 second).symm
    · have second : ¬ E Q U := fun h => first (transitive P Q U related h)
      exact ((rRow U).2 first).trans ((sRow U).2 second).symm

/-- Individual row existence suffices to prove existence of an abstraction map
in the metatheory. Object uniqueness alternatively permits a definitional
extension in a first-order presentation, without a function-choice axiom. -/
theorem row_existence_gives_abstraction (evaluate : H → C → D) (code : H → D)
    (top bottom : D) (distinct : top ≠ bottom) (E : C → C → Prop)
    (reflexive : ∀ P, E P P) (symmetric : ∀ P Q, E P Q → E Q P)
    (transitive : ∀ P Q U, E P Q → E Q U → E P U)
    (valueRange : ∀ r s, code r = code s ↔ ∀ P, evaluate r P = evaluate s P)
    (rows : ∀ P, ∃ r, IsRow evaluate top bottom E P r) :
    ∃ cardinal : C → D, ∀ P Q, cardinal P = cardinal Q ↔ E P Q := by
  classical
  let chosen : C → H := fun P => Classical.choose (rows P)
  refine ⟨fun P => code (chosen P), ?_⟩
  intro P Q
  exact rows_give_abstraction evaluate code top bottom distinct E reflexive symmetric
    transitive valueRange P Q (chosen P) (chosen Q)
    (Classical.choose_spec (rows P)) (Classical.choose_spec (rows Q))

/-- One precisely stated characteristic-function instance already contradicts
the value-range injection into the object domain and singleton comprehension.
This proof works with arbitrary Henkin concept/function sorts. It makes no
full-powerset or full-function-space assumption. -/
theorem diagonal_instance_is_inconsistent
    (holds : C → D → Prop) (evaluate : H → C → D) (code : H → D)
    (top bottom : D) (distinct : top ≠ bottom)
    (singletons : ∀ a : D, ∃ P : C, ∀ x : D, holds P x ↔ x = a)
    (codeSound : ∀ r s : H, code r = code s → ∀ P : C, evaluate r P = evaluate s P)
    (diagonal : ∃ h : H, ∀ P : C,
      (evaluate h P = top ↔ ∃ r : H, holds P (code r) ∧ evaluate r P = bottom) ∧
      (evaluate h P = top ∨ evaluate h P = bottom)) : False := by
  obtain ⟨h, hLaw⟩ := diagonal
  obtain ⟨P, singletonLaw⟩ := singletons (code h)
  have flip : evaluate h P = top ↔ evaluate h P = bottom := by
    constructor
    · intro isTop
      obtain ⟨r, member, isBottom⟩ := (hLaw P).1.mp isTop
      have sameCode := (singletonLaw (code r)).mp member
      exact (codeSound r h sameCode P).symm.trans isBottom
    · intro isBottom
      apply (hLaw P).1.mpr
      exact ⟨h, (singletonLaw (code h)).mpr rfl, isBottom⟩
  rcases (hLaw P).2 with isTop | isBottom
  · exact distinct (isTop.symm.trans (flip.mp isTop))
  · exact distinct ((flip.mpr isBottom).symm.trans isBottom)

#print axioms rows_give_abstraction
#print axioms row_existence_gives_abstraction
#print axioms diagonal_instance_is_inconsistent

end FregeanECA.Research.HigherOrderAudit
