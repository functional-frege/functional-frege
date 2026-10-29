import FregeanECA.V4.PrintedTheory

/-!
`prop:choice`: no object of FF is a choice function.

Functional choice, AC_f, is the schema ∀x ∃y R(x,y) → ∃f ∀x R(x, f(x)) for
available binary relations R. FF refutes its instance for the relation
R(x,y) :↔ y ≠ x(x): the relation is total because there are two distinct
objects (A6), and a function f with f(x) ≠ x(x) for every x would give, at
x = δf, f(δf) ≠ (δf)(δf) = f(δf). Hence FF + AC_f is inconsistent. The
argument uses A1 (to form R), A6 and the evaluation law only.
-/
namespace FregeanECA.V4.Choice

open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2
open scoped FFL.FirstOrder

universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- The relation y ≠ x(x) is total: ∀x ∃y (y ≠ x(x)). -/
def total : Formula :=
  .forallObject (.existsObject (notF (.equal (.var 0) (.app (.var 1) (.var 1)))))

/-- A function choosing inside that relation: ∃f ∀x (f(x) ≠ x(x)). -/
def chooser : Formula :=
  .existsFunction (.forallObject (notF (.equal (.eval 0 (.var 0)) (.app (.var 0) (.var 0)))))

/-- The instance of functional choice for the relation y ≠ x(x). -/
def choiceInstance : Formula := .implies total chooser

theorem total_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    total.truth M o f r ↔ ∀ x : D, ∃ y : D, y ≠ M.applicative.apply x x := Iff.rfl

theorem chooser_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    chooser.truth M o f r ↔ ∃ g : F, ∀ x : D, M.eval g x ≠ M.applicative.apply x x := Iff.rfl

/-- In every model of the printed axioms the choice instance fails: a chooser
applied to its own abstract would differ from itself. -/
theorem choice_fails (M : Interpretation D F R) [Nonempty F] [∀ n, Nonempty (R n)]
    (h : ∀ p, Printed.Axiom p → Valid M p) : Valid M (notF choiceInstance) := by
  intro o f r hc
  obtain ⟨a, b, hab⟩ := (nontriviality_truth M o f r).mp
    (Printed.nontriviality_of_A6 M (h _ (Or.inl .a6)) o f r)
  have ev := (evaluation_truth M o f r).mp (h _ (Or.inr .evaluation) o f r)
  have htotal : ∀ x : D, ∃ y : D, y ≠ M.applicative.apply x x := by
    intro x
    by_cases hx : a = M.applicative.apply x x
    · exact ⟨b, fun hb => hab (hx.trans hb.symm)⟩
    · exact ⟨a, hx⟩
  obtain ⟨g, hg⟩ := (chooser_truth M o f r).mp (hc ((total_truth M o f r).mpr htotal))
  exact hg (M.delta g) (ev g (M.delta g))

/-- `prop:choice`: FF proves the negation of the choice instance. -/
theorem no_choice_provable : Printed.theory ⊢ sentence (notF choiceInstance) :=
  (Printed.provability_iff _).mpr
    (V3.PaperResults.provable_of_valid _ (fun M h =>
      choice_fails M ((Printed.axioms_iff_cleaner M).mpr h)))

end FregeanECA.V4.Choice

#print axioms FregeanECA.V4.Choice.no_choice_provable
