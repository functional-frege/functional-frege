import FregeanECA.Part2.Models

/-! A worked program/specification example. Programs are objects and the
preconditions, postconditions, and graphs are available relation objects.
The results are consequences of the actual model conditions; they do not
postulate a relation representing an arbitrary metatheoretic predicate. -/

namespace FregeanECA.V3.Specifications
open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

def holds (M : Interpretation D R) (P : R 0) (x : D) : Prop :=
  M.satisfies 0 P (fun _ => x)

def meets (M : Interpretation D R) (p : D) (P Q : R 0) : Prop :=
  ∀ x, holds M P x → holds M Q (M.apply p x)

def compose (M : Interpretation D R) (p q : D) : D :=
  M.apply (M.apply M.constantS (M.apply M.constantK q)) p

theorem composition_correct (M : Interpretation D R)
    (laws : CombinatoryLaws M) (p q x : D) :
    M.apply (compose M p q) x = M.apply q (M.apply p x) := by
  unfold compose
  rw [laws.distribute, laws.constant]

theorem composition_specification (M : Interpretation D R)
    (laws : CombinatoryLaws M) (p q : D) (P Q T : R 0)
    (hp : meets M p P Q) (hq : meets M q Q T) :
    meets M (compose M p q) P T := by
  intro x hx
  rw [composition_correct M laws]
  exact hq _ (hp x hx)

/-- Binary graph existence is proved by one actual comprehension instance. -/
theorem composition_graph (M : Interpretation D R)
    (laws : CombinatoryLaws M) (full : Part2.HasFullComprehension M) (p q : D) :
    ∃ G : R 1, ∀ x y,
      M.satisfies 1 G (Fin.cases x (fun _ => y)) ↔
        y = M.apply q (M.apply p x) := by
  classical
  let predicates : PredicateAssignment R :=
    fun n _ => Classical.choice (full.relations_nonempty n)
  let formula : Applicative.Formula :=
    .equal (.var 1) (.app (.var 2) (.var 0))
  obtain ⟨G, hg⟩ := full.comprehend 1 formula
    (fun _ => compose M p q) predicates
  refine ⟨G, fun x y => ?_⟩
  have h := hg (Fin.cases x (fun _ => y))
  change M.satisfies 1 G (Fin.cases x (fun _ => y)) ↔
    y = M.apply (compose M p q) x at h
  simpa only [composition_correct M laws] using h

theorem graph_specification (M : Interpretation D R)
    (laws : CombinatoryLaws M) (full : Part2.HasFullComprehension M)
    (p q : D) (P Q T : R 0)
    (hp : meets M p P Q) (hq : meets M q Q T) :
    ∃ G : R 1,
      (∀ x y, M.satisfies 1 G (Fin.cases x (fun _ => y)) ↔
        y = M.apply (compose M p q) x) ∧
      (∀ x y, M.satisfies 1 G (Fin.cases x (fun _ => y)) →
        holds M P x → holds M T y) := by
  obtain ⟨G, hg⟩ := composition_graph M laws full p q
  refine ⟨G, ?_, ?_⟩
  · intro x y
    simpa only [composition_correct M laws] using hg x y
  · intro x y hxy hx
    rw [(hg x y).mp hxy]
    exact hq _ (hp x hx)

end FregeanECA.V3.Specifications

#print axioms FregeanECA.V3.Specifications.composition_correct
#print axioms FregeanECA.V3.Specifications.composition_specification
#print axioms FregeanECA.V3.Specifications.graph_specification
