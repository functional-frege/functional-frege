import Frege.CombinatoryAlgebra

/-!
The representation part of A3--A4, without assuming identity of functions is
extensional. The two explicit comprehension instances used below are exactly
the instances of A2 producing K and S; this file does not assume all of A2.
-/
namespace FregeanECA

universe u v

structure Representation (D : Type u) (F : Type v) where
  eval : F → D → D
  delta : F → D
  lawV : ∀ f g, delta f = delta g ↔ ∀ x, eval f x = eval g x
  coverage : ∀ a, ∃ f, delta f = a

namespace Representation

variable {D : Type u} {F : Type v} (R : Representation D F)

noncomputable def representative (a : D) : F := Classical.choose (R.coverage a)

theorem representative_spec (a : D) : R.delta (R.representative a) = a :=
  Classical.choose_spec (R.coverage a)

noncomputable def app (a b : D) : D := R.eval (R.representative a) b

theorem application_of_representative (f : F) (x : D) :
    R.app (R.delta f) x = R.eval f x :=
  (R.lawV _ _).mp (R.representative_spec (R.delta f)) x

theorem application_graph (a b c : D) :
    R.app a b = c ↔ ∃ f, R.delta f = a ∧ R.eval f b = c := by
  constructor
  · intro h
    exact ⟨R.representative a, R.representative_spec a, h⟩
  · rintro ⟨f, hf, h⟩
    rw [← hf, R.application_of_representative]
    exact h

theorem application_graph_unique (a b c d : D)
    (hc : ∃ f, R.delta f = a ∧ R.eval f b = c)
    (hd : ∃ f, R.delta f = a ∧ R.eval f b = d) : c = d := by
  exact ((R.application_graph a b c).mpr hc).symm.trans
    ((R.application_graph a b d).mpr hd)

theorem application_extensional (a b : D)
    (h : ∀ x, R.app a x = R.app b x) : a = b := by
  have hdelta := (R.lawV (R.representative a) (R.representative b)).mpr h
  simpa only [R.representative_spec] using hdelta

def FunctionExtensionality : Prop :=
  ∀ f g, (∀ x, R.eval f x = R.eval g x) → f = g

theorem function_extensionality_iff_injective :
    R.FunctionExtensionality ↔ (∀ f g, R.delta f = R.delta g → f = g) := by
  constructor
  · intro h f g same
    exact h f g ((R.lawV f g).mp same)
  · intro h f g same
    exact h f g ((R.lawV f g).mpr same)

/-- The n=2 and n=3 instances of finite applicative comprehension. -/
structure CombinatorInstances : Prop where
  constant : ∃ f, ∀ x y, R.app (R.eval f x) y = x
  distribute : ∃ f, ∀ x y z,
    R.app (R.app (R.eval f x) y) z = R.app (R.app x z) (R.app y z)

noncomputable def toCombinatoryAlgebra (h : R.CombinatorInstances) :
    Frege.CombinatoryAlgebra D where
  apply := R.app
  constant := R.delta (Classical.choose h.constant)
  distribute := R.delta (Classical.choose h.distribute)
  constant_returns_first_argument := by
    intro x y
    rw [R.application_of_representative]
    exact Classical.choose_spec h.constant x y
  distribute_applies_the_same_argument := by
    intro x y z
    rw [R.application_of_representative]
    exact Classical.choose_spec h.distribute x y z

theorem extracted_algebra_extensional (h : R.CombinatorInstances) :
    (R.toCombinatoryAlgebra h).IsExtensional := R.application_extensional

end Representation

/-- Duplicating a function code preserves A3 and A4. -/
def duplicateRepresentation {D : Type u} (A : Frege.CombinatoryAlgebra D)
    (ext : A.IsExtensional) : Representation D (D × Bool) where
  eval := fun f x => A.apply f.1 x
  delta := Prod.fst
  lawV := by
    intro f g
    constructor
    · intro h x
      exact congrArg (fun a => A.apply a x) h
    · exact ext f.1 g.1
  coverage := fun a => ⟨(a, false), rfl⟩

theorem duplicateRepresentation_not_extensional {D : Type u}
    (A : Frege.CombinatoryAlgebra D) (ext : A.IsExtensional) :
    ¬ (duplicateRepresentation A ext).FunctionExtensionality := by
  intro h
  have impossible := h (A.constant, false) (A.constant, true) (fun _ => rfl)
  have : false = true := congrArg Prod.snd impossible
  cases this

end FregeanECA
