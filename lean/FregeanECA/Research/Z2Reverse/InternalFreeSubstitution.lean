import FregeanECA.Research.Z2Reverse.InternalLambdaScope

/-!
Internal substitution of free names.

This operation replaces a free-name leaf and leaves bound-variable indices
unchanged. Preservation of binder scope is proved for replacements with no
unbound de Bruijn indices. It is not beta substitution for a bound variable.
-/

namespace FregeanECA.Research.Z2Reverse.InternalFreeSubstitution

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Recursion

def blueprint : Bootstrapping.Language.TermRec.Blueprint 2 where
  bvar := .mkSigma “y z a r. !qqBvarDef y z”
  fvar := .mkSigma “y x a r. (x = a ∧ y = r) ∨ (x ≠ a ∧ !qqFvarDef y x)”
  func := .mkSigma “y k f v w a r. !qqFuncDef y k f w”

open Classical in
noncomputable def construction : Bootstrapping.Language.TermRec.Construction V blueprint where
  bvar _ i := bvar i
  fvar p i := if i = p 0 then p 1 else fvar i
  func _ k f _ w := qqFunc k f w
  bvar_defined := .mk fun v => by simp [blueprint, bvar]
  fvar_defined := .mk fun v => by
    by_cases h : v 1 = v 2 <;> simp [blueprint, fvar, h]
  func_defined := .mk fun v => by simp [blueprint]

end Recursion

noncomputable def substitute (term name replacement : V) : V :=
  Recursion.construction.result language ![name, replacement] term

noncomputable def substitutionFormula : 𝚺₁.Semisentence 4 :=
  Recursion.blueprint.result language

noncomputable def substitutionDeltaFormula : 𝚫₁.Semisentence 4 :=
  substitutionFormula.graphDelta

instance substitution_defined :
    𝚺₁-Function₃ (substitute : V → V → V → V) via substitutionFormula := .mk fun v => by
  simpa [substitutionFormula, substitute, Matrix.fun_eq_vec_two] using!
    Recursion.construction.result_defined.defined v

instance substitutionDelta_defined :
    𝚫₁-Function₃ (substitute : V → V → V → V) via substitutionDeltaFormula :=
  substitution_defined.graph_delta

instance substitution_definable : 𝚺₁-Function₃ (substitute : V → V → V → V) :=
  substitution_defined.to_definable

instance substitution_definable' (Γ m) :
    Γ-[m + 1]-Function₃ (substitute : V → V → V → V) :=
  substitution_definable.of_sigmaOne

instance scoped_definable' (Γ m) : Γ-[m + 1]-Relation (IsScoped (V := V)) :=
  scoped_definable.of_deltaOne

instance term_definable' (Γ m) : Γ-[m + 1]-Predicate (IsTerm (V := V)) :=
  term_definable.of_deltaOne

instance freeBound_definable' (Γ m) : Γ-[m + 1]-Function₁ (freeBound : V → V) :=
  freeBound_definable.of_sigmaOne

@[simp] theorem substitute_bvar (i name replacement : V) :
    substitute (bvar i) name replacement = bvar i := by
  simp [substitute, bvar, Recursion.construction]

@[simp] theorem substitute_fvar_same (name replacement : V) :
    substitute (fvar name) name replacement = replacement := by
  simp [substitute, fvar, Recursion.construction]

theorem substitute_fvar_ne (i name replacement : V) (h : i ≠ name) :
    substitute (fvar i) name replacement = fvar i := by
  simp [substitute, fvar, Recursion.construction, h]

theorem substitute_lam (s name replacement : V) (hs : IsTerm s) :
    substitute (lam s) name replacement = lam (substitute s name replacement) := by
  have hvec : IsUTermVec language (1 : V) ?[s] := IsUTermVec.adjoin₁_iff.mpr hs
  have computation := Recursion.construction.result_func (L := language)
    (param := ![name, replacement]) (k := (1 : V)) (f := (0 : V))
    (v := ?[s]) (w := ?[substitute s name replacement])
    (by simp) hvec (by simp) (by
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      simp [substitute])
  simpa [substitute, lam, Recursion.construction] using computation

theorem substitute_app (s t name replacement : V) (hs : IsTerm s) (ht : IsTerm t) :
    substitute (app s t) name replacement =
      app (substitute s name replacement) (substitute t name replacement) := by
  have hvec : IsUTermVec language (2 : V) ?[s, t] := IsUTermVec.mkSeq₂_iff.mpr ⟨hs, ht⟩
  have computation := Recursion.construction.result_func (L := language)
    (param := ![name, replacement]) (k := (2 : V)) (f := (0 : V)) (v := ?[s, t])
    (w := ?[substitute s name replacement, substitute t name replacement])
    (by simp) hvec (by simp [one_add_one_eq_two]) (by
      intro i hi
      rcases (lt_two_iff_le_one.trans le_one_iff_eq_zero_or_one).mp hi with rfl | rfl <;>
        simp [substitute])
  simpa [substitute, app, Recursion.construction] using computation

theorem preserves_terms (name replacement : V) (hr : IsTerm replacement) :
    ∀ t, IsTerm t → IsTerm (substitute t name replacement) := by
  refine InternalLambdaCode.induction 𝚺
    (P := fun t => IsTerm (substitute t name replacement)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i; simp
  · intro i
    by_cases hi : i = name
    · subst i; simpa using hr
    · simp [substitute_fvar_ne i name replacement hi]
  · intro s hs ih
    simpa [substitute_lam s name replacement hs] using (isTerm_lam_iff _).mpr ih
  · intro s t hs ht ihs iht
    simpa [substitute_app s t name replacement hs ht] using
      (isTerm_app_iff _ _).mpr ⟨ihs, iht⟩

/-- A replacement with no escaping bound indices remains safe under every binder. -/
theorem preserves_scope (name replacement : V) (hr : IsScoped 0 replacement) :
    ∀ t, IsTerm t → ∀ depth, IsScoped depth t →
      IsScoped depth (substitute t name replacement) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ depth, IsScoped depth t →
      IsScoped depth (substitute t name replacement)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i depth ht; simpa using ht
  · intro i depth _
    by_cases hi : i = name
    · subst i
      simpa using hr.mono (show (0 : V) ≤ depth by simp)
    · simp [substitute_fvar_ne i name replacement hi]
  · intro s hs ih depth h
    rw [substitute_lam s name replacement hs, isScoped_lam_iff]
    exact ih (depth + 1) ((isScoped_lam_iff depth s).mp h)
  · intro s t hs ht ihs iht depth h
    rw [substitute_app s t name replacement hs ht, isScoped_app_iff]
    obtain ⟨hs', ht'⟩ := (isScoped_app_iff depth s t).mp h
    exact ⟨ihs depth hs', iht depth ht'⟩

/-- An index at or above the internal free-variable bound does not occur. -/
theorem fresh_substitution (name replacement : V) :
    ∀ t, IsTerm t → freeBound t ≤ name → substitute t name replacement = t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => freeBound t ≤ name → substitute t name replacement = t) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i _; simp
  · intro i h
    have hi : i < name := (succ_le_iff_lt).mp (by simpa using h)
    exact substitute_fvar_ne i name replacement (ne_of_lt hi)
  · intro s hs ih h
    rw [substitute_lam s name replacement hs]
    exact congrArg lam (ih (by simpa [freeBound_lam s hs] using h))
  · intro s t hs ht ihs iht h
    have bounds : freeBound s ≤ name ∧ freeBound t ≤ name := by
      simpa [freeBound_app s t hs ht] using h
    rw [substitute_app s t name replacement hs ht, ihs bounds.1, iht bounds.2]

end FregeanECA.Research.Z2Reverse.InternalFreeSubstitution
