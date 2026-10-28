import FregeanECA.Research.Z2Reverse.InternalBoundShift

/-!
Internal capture-avoiding substitution for one de Bruijn binder. Removing the
binder decrements larger indices. Entering a lambda increases the cutoff and
shifts the replacement, so its escaping indices cannot be captured.
-/

namespace FregeanECA.Research.Z2Reverse.InternalBoundSubstitution

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Recursion

noncomputable def blueprint : InternalBinderRecursion.Blueprint where
  bvar := .mkSigma “y p i. ∃ c r, !pi₁Def c p ∧ !pi₂Def r p ∧
    ((i = c ∧ y = r) ∨ (i ≠ c ∧ i < c ∧ !qqBvarDef y i) ∨
      (i ≠ c ∧ ¬i < c ∧ ∃ j, !subDef j i 1 ∧ !qqBvarDef y j))”
  fvar := .mkSigma “y p i. !qqFvarDef y i”
  app := .mkSigma “y p s t. !appFormula y s t”
  lam := .mkSigma “y p s. !lamFormula y s”
  change := .mkSigma “q p. ∃ c r s,
    !pi₁Def c p ∧ !pi₂Def r p ∧ !shiftFormula s r 0 1 ∧ !pairDef q (c + 1) s”

open Classical in
noncomputable def construction : InternalBinderRecursion.Construction V blueprint where
  bvar p i := if i = π₁ p then π₂ p else if i < π₁ p then bvar i else bvar (i - 1)
  fvar _ i := fvar i
  app _ s t := app s t
  lam _ s := lam s
  change p := ⟪π₁ p + 1, shift (π₂ p) 0 1⟫
  bvar_defined := .mk fun v => by
    by_cases he : v 2 = π₁ (v 1)
    · simp [blueprint, he]
    · by_cases hl : v 2 < π₁ (v 1)
      · simp [blueprint, bvar, he, hl]
      · simp [blueprint, bvar, he, hl, not_lt.mp hl]
  fvar_defined := .mk fun v => by simp [blueprint, fvar]
  app_defined := .mk fun v => by simp [blueprint]
  lam_defined := .mk fun v => by simp [blueprint]
  change_defined := .mk fun v => by simp [blueprint]

end Recursion

noncomputable def substitute (term cutoff replacement : V) : V :=
  Recursion.construction.result ⟪cutoff, replacement⟫ term

noncomputable def substitutionFormula : 𝚺₁.Semisentence 4 := .mkSigma
  “y t c r. ∃ p, !pairDef p c r ∧ !Recursion.blueprint.resultFormula y p t”

instance substitution_defined :
    𝚺₁-Function₃ (substitute : V → V → V → V) via substitutionFormula := .mk fun v => by
  have := Recursion.construction.result_defined (V := V)
  simp [substitutionFormula, substitute]

instance substitutionDelta_defined :
    𝚫₁-Function₃ (substitute : V → V → V → V) via substitutionFormula.graphDelta :=
  substitution_defined.graph_delta

instance substitution_definable : 𝚺₁-Function₃ (substitute : V → V → V → V) :=
  substitution_defined.to_definable

instance substitution_definable' (Γ m) :
    Γ-[m + 1]-Function₃ (substitute : V → V → V → V) :=
  substitution_definable.of_sigmaOne

@[simp] theorem substitute_bvar_eq (cutoff replacement : V) :
    substitute (bvar cutoff) cutoff replacement = replacement := by
  simp [substitute, Recursion.construction]

theorem substitute_bvar_lt (i cutoff replacement : V) (h : i < cutoff) :
    substitute (bvar i) cutoff replacement = bvar i := by
  simp [substitute, Recursion.construction, h, ne_of_lt h]

theorem substitute_bvar_gt (i cutoff replacement : V) (h : cutoff < i) :
    substitute (bvar i) cutoff replacement = bvar (i - 1) := by
  simp [substitute, Recursion.construction, not_lt.mpr (le_of_lt h), ne_of_gt h]

@[simp] theorem substitute_fvar (i cutoff replacement : V) :
    substitute (fvar i) cutoff replacement = fvar i := by
  simp [substitute, Recursion.construction]

theorem substitute_app (s t cutoff replacement : V) (hs : IsTerm s) (ht : IsTerm t) :
    substitute (app s t) cutoff replacement =
      app (substitute s cutoff replacement) (substitute t cutoff replacement) := by
  exact Recursion.construction.result_app _ s t hs ht

theorem substitute_lam (s cutoff replacement : V) (hs : IsTerm s) :
    substitute (lam s) cutoff replacement =
      lam (substitute s (cutoff + 1) (shift replacement 0 1)) := by
  simpa [substitute, Recursion.construction] using
    Recursion.construction.result_lam ⟪cutoff, replacement⟫ s hs

theorem preserves_terms : ∀ t : V, IsTerm t → ∀ cutoff replacement,
    IsTerm replacement → IsTerm (substitute t cutoff replacement) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff replacement,
      IsTerm replacement → IsTerm (substitute t cutoff replacement)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff replacement hr
    rcases lt_trichotomy i cutoff with h | rfl | h
    · simp [substitute_bvar_lt i cutoff replacement h]
    · simpa using hr
    · simp [substitute_bvar_gt i cutoff replacement h]
  · intro i cutoff replacement _; simp
  · intro s hs ih cutoff replacement hr
    rw [substitute_lam s cutoff replacement hs, isTerm_lam_iff]
    exact ih (cutoff + 1) _ (InternalBoundShift.preserves_terms replacement hr 0 1)
  · intro s t hs ht ihs iht cutoff replacement hr
    rw [substitute_app s t cutoff replacement hs ht, isTerm_app_iff]
    exact ⟨ihs cutoff replacement hr, iht cutoff replacement hr⟩

theorem preserves_scope : ∀ t : V, IsTerm t → ∀ depth cutoff replacement,
    cutoff ≤ depth → IsScoped depth replacement → IsScoped (depth + 1) t →
      IsScoped depth (substitute t cutoff replacement) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ depth cutoff replacement,
      cutoff ≤ depth → IsScoped depth replacement → IsScoped (depth + 1) t →
        IsScoped depth (substitute t cutoff replacement)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i depth cutoff replacement hc hr hi
    have hi' : i < depth + 1 := (isScoped_bvar_iff (depth + 1) i).mp hi
    rcases lt_trichotomy i cutoff with h | rfl | h
    · rw [substitute_bvar_lt i cutoff replacement h, isScoped_bvar_iff]
      exact lt_of_lt_of_le h hc
    · simpa using hr
    · rw [substitute_bvar_gt i cutoff replacement h, isScoped_bvar_iff]
      have hpos : 0 < i := lt_of_le_of_lt (by simp) h
      exact (tsub_lt_iff_left (one_le_of_zero_lt i hpos)).mpr
        (by simpa [add_comm] using hi')
  · intro i depth cutoff replacement _ _ _; simp
  · intro s hs ih depth cutoff replacement hc hr h
    rw [substitute_lam s cutoff replacement hs, isScoped_lam_iff]
    exact ih (depth + 1) (cutoff + 1) (shift replacement 0 1)
      (by simpa [add_comm] using add_le_add_right hc (1 : V))
      (InternalBoundShift.preserves_scope replacement hr.term depth 0 1 hr)
      ((isScoped_lam_iff (depth + 1) s).mp h)
  · intro s t hs ht ihs iht depth cutoff replacement hc hr h
    rw [substitute_app s t cutoff replacement hs ht, isScoped_app_iff]
    obtain ⟨hs', ht'⟩ := (isScoped_app_iff (depth + 1) s t).mp h
    exact ⟨ihs depth cutoff replacement hc hr hs', iht depth cutoff replacement hc hr ht'⟩

/-- Terms below the removed binder are unchanged. -/
theorem substitute_of_scoped : ∀ t : V, IsTerm t → ∀ cutoff replacement,
    IsScoped cutoff t → substitute t cutoff replacement = t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff replacement,
      IsScoped cutoff t → substitute t cutoff replacement = t) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff replacement h
    exact substitute_bvar_lt i cutoff replacement ((isScoped_bvar_iff cutoff i).mp h)
  · intro i cutoff replacement _; simp
  · intro s hs ih cutoff replacement h
    rw [substitute_lam s cutoff replacement hs,
      ih (cutoff + 1) _ ((isScoped_lam_iff cutoff s).mp h)]
  · intro s t hs ht ihs iht cutoff replacement h
    obtain ⟨hs', ht'⟩ := (isScoped_app_iff cutoff s t).mp h
    rw [substitute_app s t cutoff replacement hs ht,
      ihs cutoff replacement hs', iht cutoff replacement ht']

/-- Removing a freshly inserted index leaves the original expression. -/
theorem substitute_shift : ∀ t : V, IsTerm t → ∀ cutoff replacement,
    substitute (shift t cutoff 1) cutoff replacement = t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff replacement,
      substitute (shift t cutoff 1) cutoff replacement = t) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff replacement
    by_cases hi : i < cutoff
    · rw [shift_bvar_lt i cutoff 1 hi, substitute_bvar_lt i cutoff replacement hi]
    · have hge : cutoff ≤ i := not_lt.mp hi
      have hgt : cutoff < i + 1 := lt_succ_iff_le.mpr hge
      rw [shift_bvar_ge i cutoff 1 hge, substitute_bvar_gt (i + 1) cutoff replacement hgt]
      simp
  · intro i cutoff replacement; simp
  · intro s hs ih cutoff replacement
    rw [shift_lam s cutoff 1 hs,
      substitute_lam _ cutoff replacement (InternalBoundShift.preserves_terms s hs (cutoff + 1) 1),
      ih (cutoff + 1) _]
  · intro s t hs ht ihs iht cutoff replacement
    rw [shift_app s t cutoff 1 hs ht,
      substitute_app _ _ cutoff replacement (InternalBoundShift.preserves_terms s hs cutoff 1)
        (InternalBoundShift.preserves_terms t ht cutoff 1),
      ihs cutoff replacement, iht cutoff replacement]

/-- Contract the outermost lambda binder. -/
noncomputable def beta (body argument : V) : V := substitute body 0 argument

instance beta_definable : 𝚺₁-Function₂ (beta : V → V → V) := by
  unfold beta
  definability

instance beta_definable' (Γ m) : Γ-[m + 1]-Function₂ (beta : V → V → V) :=
  beta_definable.of_sigmaOne

theorem beta_scoped {depth body argument : V}
    (hb : IsScoped (depth + 1) body) (ha : IsScoped depth argument) :
    IsScoped depth (beta body argument) :=
  preserves_scope body hb.term depth 0 argument (by simp) ha hb

end FregeanECA.Research.Z2Reverse.InternalBoundSubstitution
