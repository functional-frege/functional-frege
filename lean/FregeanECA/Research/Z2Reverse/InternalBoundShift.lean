import FregeanECA.Research.Z2Reverse.InternalBinderRecursion

/-!
Capture-avoiding upward shift of bound-variable indices, internally defined in
every IΣ1 model. The cutoff increases on entering a lambda; the increment stays
fixed. No external recursion on the model's numbers is used.
-/

namespace FregeanECA.Research.Z2Reverse.InternalBoundShift

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Recursion

def blueprint : InternalBinderRecursion.Blueprint where
  bvar := .mkSigma “y p i. ∃ c d, !pi₁Def c p ∧ !pi₂Def d p ∧
    ((i < c ∧ !qqBvarDef y i) ∨ (¬i < c ∧ !qqBvarDef y (i + d)))”
  fvar := .mkSigma “y p i. !qqFvarDef y i”
  app := .mkSigma “y p s t. !appFormula y s t”
  lam := .mkSigma “y p s. !lamFormula y s”
  change := .mkSigma “q p. ∃ c d, !pi₁Def c p ∧ !pi₂Def d p ∧ !pairDef q (c + 1) d”

open Classical in
noncomputable def construction : InternalBinderRecursion.Construction V blueprint where
  bvar p i := if i < π₁ p then bvar i else bvar (i + π₂ p)
  fvar _ i := fvar i
  app _ s t := app s t
  lam _ s := lam s
  change p := ⟪π₁ p + 1, π₂ p⟫
  bvar_defined := .mk fun v => by
    by_cases h : v 2 < π₁ (v 1)
    · simp [blueprint, bvar, h]
    · simp [blueprint, bvar, h, not_lt.mp h]
  fvar_defined := .mk fun v => by simp [blueprint, fvar]
  app_defined := .mk fun v => by simp [blueprint]
  lam_defined := .mk fun v => by simp [blueprint]
  change_defined := .mk fun v => by simp [blueprint]

end Recursion

noncomputable def shift (term cutoff increment : V) : V :=
  Recursion.construction.result ⟪cutoff, increment⟫ term

noncomputable def shiftFormula : 𝚺₁.Semisentence 4 := .mkSigma
  “y t c d. ∃ p, !pairDef p c d ∧ !Recursion.blueprint.resultFormula y p t”

instance shift_defined : 𝚺₁-Function₃ (shift : V → V → V → V) via shiftFormula :=
  .mk fun v => by
    have := Recursion.construction.result_defined (V := V)
    simp [shiftFormula, shift]

instance shiftDelta_defined :
    𝚫₁-Function₃ (shift : V → V → V → V) via shiftFormula.graphDelta :=
  shift_defined.graph_delta

instance shift_definable : 𝚺₁-Function₃ (shift : V → V → V → V) :=
  shift_defined.to_definable

instance shift_definable' (Γ m) : Γ-[m + 1]-Function₃ (shift : V → V → V → V) :=
  shift_definable.of_sigmaOne

theorem shift_bvar_lt (i cutoff increment : V) (h : i < cutoff) :
    shift (bvar i) cutoff increment = bvar i := by
  simp [shift, Recursion.construction, h]

theorem shift_bvar_ge (i cutoff increment : V) (h : cutoff ≤ i) :
    shift (bvar i) cutoff increment = bvar (i + increment) := by
  simp [shift, Recursion.construction, not_lt.mpr h]

@[simp] theorem shift_fvar (i cutoff increment : V) :
    shift (fvar i) cutoff increment = fvar i := by
  simp [shift, Recursion.construction]

theorem shift_app (s t cutoff increment : V) (hs : IsTerm s) (ht : IsTerm t) :
    shift (app s t) cutoff increment =
      app (shift s cutoff increment) (shift t cutoff increment) := by
  exact Recursion.construction.result_app _ s t hs ht

theorem shift_lam (s cutoff increment : V) (hs : IsTerm s) :
    shift (lam s) cutoff increment = lam (shift s (cutoff + 1) increment) := by
  simpa [shift, Recursion.construction] using
    Recursion.construction.result_lam ⟪cutoff, increment⟫ s hs

theorem preserves_terms : ∀ t : V, IsTerm t → ∀ cutoff increment,
    IsTerm (shift t cutoff increment) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff increment, IsTerm (shift t cutoff increment)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff increment
    by_cases h : i < cutoff
    · simp [shift_bvar_lt i cutoff increment h]
    · simp [shift_bvar_ge i cutoff increment (not_lt.mp h)]
  · intro i cutoff increment; simp
  · intro s hs ih cutoff increment
    simpa [shift_lam s cutoff increment hs] using ih (cutoff + 1) increment
  · intro s t hs ht ihs iht cutoff increment
    simpa [shift_app s t cutoff increment hs ht] using
      And.intro (ihs cutoff increment) (iht cutoff increment)

theorem preserves_scope : ∀ t : V, IsTerm t → ∀ depth cutoff increment,
    IsScoped depth t → IsScoped (depth + increment) (shift t cutoff increment) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ depth cutoff increment,
      IsScoped depth t → IsScoped (depth + increment) (shift t cutoff increment))
    ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i depth cutoff increment hi
    have hi' : i < depth := (isScoped_bvar_iff depth i).mp hi
    by_cases h : i < cutoff
    · rw [shift_bvar_lt i cutoff increment h, isScoped_bvar_iff]
      exact lt_of_lt_of_le hi' (by simp)
    · rw [shift_bvar_ge i cutoff increment (not_lt.mp h), isScoped_bvar_iff]
      simpa [add_comm] using add_lt_add_right hi' increment
  · intro i depth cutoff increment _; simp
  · intro s hs ih depth cutoff increment h
    rw [shift_lam s cutoff increment hs, isScoped_lam_iff]
    simpa [add_assoc, add_comm, add_left_comm] using
      ih (depth + 1) (cutoff + 1) increment ((isScoped_lam_iff depth s).mp h)
  · intro s t hs ht ihs iht depth cutoff increment h
    rw [shift_app s t cutoff increment hs ht, isScoped_app_iff]
    obtain ⟨hs', ht'⟩ := (isScoped_app_iff depth s t).mp h
    exact ⟨ihs depth cutoff increment hs', iht depth cutoff increment ht'⟩

/-- An expression wholly below the cutoff is unchanged, including beneath lambdas. -/
theorem shift_of_scoped : ∀ t : V, IsTerm t → ∀ cutoff increment,
    IsScoped cutoff t → shift t cutoff increment = t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff increment, IsScoped cutoff t → shift t cutoff increment = t)
    ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff increment hi
    exact shift_bvar_lt i cutoff increment ((isScoped_bvar_iff cutoff i).mp hi)
  · intro i cutoff increment _; simp
  · intro s hs ih cutoff increment h
    rw [shift_lam s cutoff increment hs,
      ih (cutoff + 1) increment ((isScoped_lam_iff cutoff s).mp h)]
  · intro s t hs ht ihs iht cutoff increment h
    obtain ⟨hs', ht'⟩ := (isScoped_app_iff cutoff s t).mp h
    rw [shift_app s t cutoff increment hs ht,
      ihs cutoff increment hs', iht cutoff increment ht']

theorem shift_zero : ∀ t : V, IsTerm t → ∀ cutoff, shift t cutoff 0 = t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff, shift t cutoff 0 = t) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff
    by_cases h : i < cutoff
    · exact shift_bvar_lt i cutoff 0 h
    · simpa using shift_bvar_ge i cutoff 0 (not_lt.mp h)
  · intro i cutoff; simp
  · intro s hs ih cutoff; rw [shift_lam s cutoff 0 hs, ih (cutoff + 1)]
  · intro s t hs ht ihs iht cutoff
    rw [shift_app s t cutoff 0 hs ht, ihs cutoff, iht cutoff]

theorem shift_add : ∀ t : V, IsTerm t → ∀ cutoff first second,
    shift (shift t cutoff first) cutoff second = shift t cutoff (first + second) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff first second,
      shift (shift t cutoff first) cutoff second = shift t cutoff (first + second))
    ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff first second
    by_cases h : i < cutoff
    · rw [shift_bvar_lt i cutoff first h, shift_bvar_lt i cutoff second h,
        shift_bvar_lt i cutoff (first + second) h]
    · have hi : cutoff ≤ i := not_lt.mp h
      have hi' : cutoff ≤ i + first := le_trans hi (by simp)
      rw [shift_bvar_ge i cutoff first hi, shift_bvar_ge (i + first) cutoff second hi',
        shift_bvar_ge i cutoff (first + second) hi, add_assoc]
  · intro i cutoff first second; simp
  · intro s hs ih cutoff first second
    rw [shift_lam s cutoff first hs,
      shift_lam _ cutoff second (preserves_terms s hs (cutoff + 1) first),
      ih (cutoff + 1) first second, shift_lam s cutoff (first + second) hs]
  · intro s t hs ht ihs iht cutoff first second
    rw [shift_app s t cutoff first hs ht,
      shift_app _ _ cutoff second (preserves_terms s hs cutoff first)
        (preserves_terms t ht cutoff first),
      ihs cutoff first second, iht cutoff first second,
      shift_app s t cutoff (first + second) hs ht]

theorem freeBound_shift : ∀ t : V, IsTerm t → ∀ cutoff increment,
    freeBound (shift t cutoff increment) = freeBound t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff increment,
      freeBound (shift t cutoff increment) = freeBound t) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff increment
    by_cases h : i < cutoff
    · simp [shift_bvar_lt i cutoff increment h]
    · simp [shift_bvar_ge i cutoff increment (not_lt.mp h)]
  · intro i cutoff increment; simp
  · intro s hs ih cutoff increment
    rw [shift_lam s cutoff increment hs,
      freeBound_lam _ (preserves_terms s hs (cutoff + 1) increment),
      ih (cutoff + 1) increment, freeBound_lam s hs]
  · intro s t hs ht ihs iht cutoff increment
    rw [shift_app s t cutoff increment hs ht,
      freeBound_app _ _ (preserves_terms s hs cutoff increment)
        (preserves_terms t ht cutoff increment),
      ihs cutoff increment, iht cutoff increment, freeBound_app s t hs ht]

end FregeanECA.Research.Z2Reverse.InternalBoundShift
