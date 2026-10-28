/-
Conditional semantic reconstruction of the paper's application theorem.
`Expr` is a restricted collection of concept expressions, NOT all predicates.
No model existence, comprehension, or consistency is assumed or proved here.
The hypotheses are explicit parameters, not Lean axiom declarations.
-/
namespace Frege

universe u v w

structure Operations (Obj : Type u) (Fun : Type v) (Expr : Type w) where
  eval : Fun → Obj → Obj
  range : Fun → Obj
  holds : Expr → Obj → Prop
  ext : Expr → Obj
  singletonExpr : Obj → Expr
  outputExpr : Obj → Obj → Expr
  extract : Obj → Obj
  singleton_spec : ∀ a z, holds (singletonExpr a) z ↔ z = a
  output_spec : ∀ u a z,
    holds (outputExpr u a) z ↔ ∃ f, u = range f ∧ eval f a = z

namespace Operations

variable {Obj : Type u} {Fun : Type v} {Expr : Type w}
variable (O : Operations Obj Fun Expr)

def singleton (a : Obj) : Obj := O.ext (O.singletonExpr a)
def app (p a : Obj) : Obj := O.extract (O.ext (O.outputExpr p a))

def BasicLawVConcept : Prop :=
  ∀ A B, O.ext A = O.ext B ↔ ∀ z, O.holds A z ↔ O.holds B z

def BasicLawVFunction : Prop :=
  ∀ f g, O.range f = O.range g ↔ ∀ a, O.eval f a = O.eval g a

def BasicLawVI : Prop := ∀ a, O.extract (O.singleton a) = a

theorem output_iff (vf : O.BasicLawVFunction) (g : Fun) (a z : Obj) :
    O.holds (O.outputExpr (O.range g) a) z ↔ z = O.eval g a := by
  constructor
  · intro h
    obtain ⟨f, hr, hv⟩ := (O.output_spec _ _ _).mp h
    exact hv.symm.trans (((vf g f).mp hr a).symm)
  · intro h
    apply (O.output_spec _ _ _).mpr
    exact ⟨g, rfl, h.symm⟩

theorem output_singleton (vc : O.BasicLawVConcept) (vf : O.BasicLawVFunction)
    (g : Fun) (a : Obj) :
    O.ext (O.outputExpr (O.range g) a) = O.singleton (O.eval g a) := by
  apply (vc _ _).mpr
  intro z
  exact (O.output_iff vf g a z).trans (O.singleton_spec _ _).symm

/-- Frege's application theorem, derived without Conversion or Coverage. -/
theorem range_application (vc : O.BasicLawVConcept) (vf : O.BasicLawVFunction)
    (vi : O.BasicLawVI) (g : Fun) (a : Obj) :
    O.app (O.range g) a = O.eval g a := by
  unfold app
  rw [O.output_singleton vc vf g a]
  exact vi _

/-- Function-level substitution is supplied separately; object beta is derived. -/
theorem object_beta (vc : O.BasicLawVConcept) (vf : O.BasicLawVFunction)
    (vi : O.BasicLawVI) (body : Obj → Obj) (f : Fun)
    (conversion : ∀ a, O.eval f a = body a) (a : Obj) :
    O.app (O.range f) a = body a :=
  (O.range_application vc vf vi f a).trans (conversion a)

def Coverage : Prop := ∀ p, ∃ f, O.range f = p
def ApplicationExtensionality : Prop :=
  ∀ p q, (∀ a, O.app p a = O.app q a) → p = q

theorem coverage_extensionality (vc : O.BasicLawVConcept)
    (vf : O.BasicLawVFunction) (vi : O.BasicLawVI) (cov : O.Coverage) :
    O.ApplicationExtensionality := by
  intro p q h
  obtain ⟨f, rfl⟩ := cov p
  obtain ⟨g, rfl⟩ := cov q
  apply (vf f g).mpr
  intro a
  rw [← O.range_application vc vf vi f a,
      ← O.range_application vc vf vi g a]
  exact h a

/-- This represents only the admitted body `[x ↦ p ⋆ x]`. -/
structure Reification where
  reify : Obj → Fun
  conversion : ∀ p a, O.eval (reify p) a = O.app p a

def Eta (R : O.Reification) : Prop := ∀ p, O.range (R.reify p) = p

theorem extensionality_eta (vc : O.BasicLawVConcept)
    (vf : O.BasicLawVFunction) (vi : O.BasicLawVI) (R : O.Reification)
    (ae : O.ApplicationExtensionality) : O.Eta R := by
  intro p
  apply ae
  intro a
  exact (O.range_application vc vf vi (R.reify p) a).trans (R.conversion p a)

theorem eta_coverage (R : O.Reification) (eta : O.Eta R) : O.Coverage := by
  intro p
  exact ⟨R.reify p, eta p⟩

theorem coverage_iff_extensionality (vc : O.BasicLawVConcept)
    (vf : O.BasicLawVFunction) (vi : O.BasicLawVI) (R : O.Reification) :
    O.Coverage ↔ O.ApplicationExtensionality :=
  ⟨O.coverage_extensionality vc vf vi,
    fun ae => O.eta_coverage R (O.extensionality_eta vc vf vi R ae)⟩

theorem coverage_iff_eta (vc : O.BasicLawVConcept)
    (vf : O.BasicLawVFunction) (vi : O.BasicLawVI) (R : O.Reification) :
    O.Coverage ↔ O.Eta R :=
  ⟨fun cov => O.extensionality_eta vc vf vi R
      (O.coverage_extensionality vc vf vi cov), O.eta_coverage R⟩

/-- Semantic specification transfer; no claim of a full syntactic PE proof. -/
theorem specification_transfer (ae : O.ApplicationExtensionality)
    (p q : Obj) (same : ∀ a, O.app p a = O.app q a) (spec : Obj → Prop) :
    spec p ↔ spec q := by
  rw [ae p q same]

theorem higher_order_transfer (ae : O.ApplicationExtensionality)
    (p q r : Obj) (same : ∀ a, O.app p a = O.app q a) (spec : Obj → Prop) :
    spec (O.app r p) ↔ spec (O.app r q) :=
  O.specification_transfer ae p q same (fun z => spec (O.app r z))

end Operations
end Frege
