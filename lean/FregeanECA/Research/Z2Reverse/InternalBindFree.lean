import FregeanECA.Research.Z2Reverse.InternalBinderRecursion

/-!
Internal abstraction of a free name. A selected free-name occurrence is
replaced by the current binder depth, which increases beneath each lambda.
All depths, names and syntax codes are model elements, including nonstandard
ones. This is distinct from substituting the fixed term `bvar 0` under binders.
-/

namespace FregeanECA.Research.Z2Reverse.InternalBindFree

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Recursion

def blueprint : InternalBinderRecursion.Blueprint where
  bvar := .mkSigma “y p i. !qqBvarDef y i”
  fvar := .mkSigma “y p i. ∃ a d, !pi₁Def a p ∧ !pi₂Def d p ∧
    ((i = a ∧ !qqBvarDef y d) ∨ (i ≠ a ∧ !qqFvarDef y i))”
  app := .mkSigma “y p s t. !appFormula y s t”
  lam := .mkSigma “y p s. !lamFormula y s”
  change := .mkSigma “q p. ∃ a d, !pi₁Def a p ∧ !pi₂Def d p ∧ !pairDef q a (d + 1)”

open Classical in
noncomputable def construction : InternalBinderRecursion.Construction V blueprint where
  bvar _ i := bvar i
  fvar p i := if i = π₁ p then bvar (π₂ p) else fvar i
  app _ s t := app s t
  lam _ s := lam s
  change p := ⟪π₁ p, π₂ p + 1⟫
  bvar_defined := .mk fun v => by simp [blueprint, bvar]
  fvar_defined := .mk fun v => by
    by_cases h : v 2 = π₁ (v 1) <;> simp [blueprint, bvar, fvar, h]
  app_defined := .mk fun v => by simp [blueprint]
  lam_defined := .mk fun v => by simp [blueprint]
  change_defined := .mk fun v => by simp [blueprint]

end Recursion

noncomputable def bindFree (term name depth : V) : V :=
  Recursion.construction.result ⟪name, depth⟫ term

noncomputable def bindFreeFormula : 𝚺₁.Semisentence 4 := .mkSigma
  “y t a d. ∃ p, !pairDef p a d ∧ !Recursion.blueprint.resultFormula y p t”

instance bindFree_defined :
    𝚺₁-Function₃ (bindFree : V → V → V → V) via bindFreeFormula := .mk fun v => by
  have := Recursion.construction.result_defined (V := V)
  simp [bindFreeFormula, bindFree]

instance bindFreeDelta_defined :
    𝚫₁-Function₃ (bindFree : V → V → V → V) via bindFreeFormula.graphDelta :=
  bindFree_defined.graph_delta

instance bindFree_definable : 𝚺₁-Function₃ (bindFree : V → V → V → V) :=
  bindFree_defined.to_definable

instance bindFree_definable' (Γ m) : Γ-[m + 1]-Function₃ (bindFree : V → V → V → V) :=
  bindFree_definable.of_sigmaOne

@[simp] theorem bindFree_bvar (i name depth : V) :
    bindFree (bvar i) name depth = bvar i := by
  simp [bindFree, Recursion.construction]

@[simp] theorem bindFree_fvar_same (name depth : V) :
    bindFree (fvar name) name depth = bvar depth := by
  simp [bindFree, Recursion.construction]

theorem bindFree_fvar_ne (i name depth : V) (h : i ≠ name) :
    bindFree (fvar i) name depth = fvar i := by
  simp [bindFree, Recursion.construction, h]

theorem bindFree_app (s t name depth : V) (hs : IsTerm s) (ht : IsTerm t) :
    bindFree (app s t) name depth =
      app (bindFree s name depth) (bindFree t name depth) := by
  exact Recursion.construction.result_app _ s t hs ht

theorem bindFree_lam (s name depth : V) (hs : IsTerm s) :
    bindFree (lam s) name depth = lam (bindFree s name (depth + 1)) := by
  simpa [bindFree, Recursion.construction] using
    Recursion.construction.result_lam ⟪name, depth⟫ s hs

theorem preserves_terms : ∀ t : V, IsTerm t → ∀ name depth,
    IsTerm (bindFree t name depth) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ name depth, IsTerm (bindFree t name depth)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i name depth; simp
  · intro i name depth
    by_cases h : i = name
    · subst i; simp
    · simp [bindFree_fvar_ne i name depth h]
  · intro s hs ih name depth
    simpa [bindFree_lam s name depth hs] using ih name (depth + 1)
  · intro s t hs ht ihs iht name depth
    simpa [bindFree_app s t name depth hs ht] using
      And.intro (ihs name depth) (iht name depth)

/-- Binding a free name creates exactly one permitted outer binder level. -/
theorem preserves_scope : ∀ t : V, IsTerm t → ∀ name depth,
    IsScoped depth t → IsScoped (depth + 1) (bindFree t name depth) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ name depth,
      IsScoped depth t → IsScoped (depth + 1) (bindFree t name depth))
    ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i name depth h
    simpa using h.mono (show depth ≤ depth + 1 by simp)
  · intro i name depth _
    by_cases h : i = name
    · subst i; simp
    · simp [bindFree_fvar_ne i name depth h]
  · intro s hs ih name depth h
    rw [bindFree_lam s name depth hs, isScoped_lam_iff]
    exact ih name (depth + 1) ((isScoped_lam_iff depth s).mp h)
  · intro s t hs ht ihs iht name depth h
    rw [bindFree_app s t name depth hs ht, isScoped_app_iff]
    obtain ⟨hs', ht'⟩ := (isScoped_app_iff depth s t).mp h
    exact ⟨ihs name depth hs', iht name depth ht'⟩

theorem fresh_bindFree : ∀ t : V, IsTerm t → ∀ name depth,
    freeBound t ≤ name → bindFree t name depth = t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ name depth, freeBound t ≤ name → bindFree t name depth = t)
    ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i name depth _; simp
  · intro i name depth h
    have hi : i < name := succ_le_iff_lt.mp (by simpa using h)
    exact bindFree_fvar_ne i name depth (ne_of_lt hi)
  · intro s hs ih name depth h
    rw [bindFree_lam s name depth hs,
      ih name (depth + 1) (by simpa [freeBound_lam s hs] using h)]
  · intro s t hs ht ihs iht name depth h
    have bounds : freeBound s ≤ name ∧ freeBound t ≤ name := by
      simpa [freeBound_app s t hs ht] using h
    rw [bindFree_app s t name depth hs ht,
      ihs name depth bounds.1, iht name depth bounds.2]

theorem freeBound_bindFree_le : ∀ t : V, IsTerm t → ∀ name depth,
    freeBound (bindFree t name depth) ≤ freeBound t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ name depth, freeBound (bindFree t name depth) ≤ freeBound t)
    ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i name depth; simp
  · intro i name depth
    by_cases h : i = name
    · subst i; simp
    · simp [bindFree_fvar_ne i name depth h]
  · intro s hs ih name depth
    rw [bindFree_lam s name depth hs,
      freeBound_lam _ (preserves_terms s hs name (depth + 1)), freeBound_lam s hs]
    exact ih name (depth + 1)
  · intro s t hs ht ihs iht name depth
    rw [bindFree_app s t name depth hs ht,
      freeBound_app _ _ (preserves_terms s hs name depth) (preserves_terms t ht name depth),
      freeBound_app s t hs ht]
    exact max_le_max (ihs name depth) (iht name depth)

noncomputable def abstractFree (term name : V) : V := lam (bindFree term name 0)

theorem abstractFree_scoped (t name : V) (ht : IsScoped 0 t) :
    IsScoped 0 (abstractFree t name) := by
  rw [abstractFree, isScoped_lam_iff]
  exact preserves_scope t ht.term name 0 ht

end FregeanECA.Research.Z2Reverse.InternalBindFree

#print axioms FregeanECA.Research.Z2Reverse.InternalBindFree.preserves_scope
#print axioms FregeanECA.Research.Z2Reverse.InternalBindFree.fresh_bindFree
#print axioms FregeanECA.Research.Z2Reverse.InternalBindFree.abstractFree_scoped
