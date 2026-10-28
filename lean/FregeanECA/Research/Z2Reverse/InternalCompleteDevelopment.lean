import FregeanECA.Research.Z2Reverse.InternalBoundSubstitution

/-!
Complete development of the beta redexes present in an internal source term.
The application case tests the original function child, not its development.
The definition is an internally total, arithmetically definable recursion.
-/

namespace FregeanECA.Research.Z2Reverse.InternalCompleteDevelopment

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A total arithmetic decoder, used as a lambda body only after a shape check. -/
noncomputable def lambdaBody (t : V) : V := (π₂ (π₂ (sndIdx t))).[0]

def lambdaBodyFormula : 𝚺₁.Semisentence 2 := .mkSigma
  “y t. ∃ a b c, !sndIdxDef a t ∧ !pi₂Def b a ∧ !pi₂Def c b ∧ !nthDef y c 0”

instance lambdaBody_defined : 𝚺₁-Function₁ (lambdaBody : V → V) via lambdaBodyFormula :=
  .mk fun v => by simp [lambdaBodyFormula, lambdaBody]

instance lambdaBody_definable : 𝚺₁-Function₁ (lambdaBody : V → V) :=
  lambdaBody_defined.to_definable

@[simp] theorem lambdaBody_lam (s : V) : lambdaBody (lam s) = s := by
  simp [lambdaBody, lam, qqFunc, sndIdx]

def IsLam (t : V) : Prop := t = lam (lambdaBody t)

def isLamFormula : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “t. ∃ s, !lambdaBodyFormula s t ∧ !lamFormula t s”)
  (.mkPi “t. ∀ s, !lambdaBodyFormula s t → !lamFormula.graphDelta.pi t s”)

instance isLam_defined : 𝚫₁-Predicate (IsLam (V := V)) via isLamFormula :=
  ⟨by
      have := lam_defined.graph_delta (V := V)
      intro v
      simp [isLamFormula],
   by
      have := lam_defined.graph_delta (V := V)
      intro v
      simp [isLamFormula, IsLam]⟩

instance isLam_definable : 𝚫₁-Predicate (IsLam (V := V)) := isLam_defined.to_definable

theorem isLam_iff (t : V) : IsLam t ↔ ∃ s, t = lam s := by
  constructor
  · intro h; exact ⟨lambdaBody t, h⟩
  · rintro ⟨s, rfl⟩; simp [IsLam]

@[simp] theorem isLam_lam (s : V) : IsLam (lam s) := by simp [IsLam]

@[simp] theorem not_isLam_bvar (i : V) : ¬IsLam (bvar i) := by
  simp [isLam_iff]

@[simp] theorem not_isLam_fvar (i : V) : ¬IsLam (fvar i) := by
  simp [isLam_iff]

@[simp] theorem not_isLam_app (s t : V) : ¬IsLam (app s t) := by
  intro h
  obtain ⟨u, hu⟩ := (isLam_iff (app s t)).mp h
  exact lam_ne_app u s t hu.symm

namespace Recursion

noncomputable def blueprint : Bootstrapping.Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y i. !qqBvarDef y i”
  fvar := .mkSigma “y i. !qqFvarDef y i”
  func := .mkSigma “y k f v w.
    (k = 1 ∧ ∃ s, !nthDef s w 0 ∧ !lamFormula y s) ∨
    (k ≠ 1 ∧ ∃ a s t, !nthDef a v 0 ∧ !nthDef s w 0 ∧ !nthDef t w 1 ∧
      ((!isLamFormula.sigma a ∧ ∃ b, !lambdaBodyFormula b s ∧
          !InternalBoundSubstitution.substitutionFormula y b 0 t) ∨
        (¬!isLamFormula.pi a ∧ !appFormula y s t)))”

open Classical in
noncomputable def construction : Bootstrapping.Language.TermRec.Construction V blueprint where
  bvar _ i := bvar i
  fvar _ i := fvar i
  func _ k _ v w := if k = 1 then lam w.[0] else
    if IsLam v.[0] then InternalBoundSubstitution.beta (lambdaBody w.[0]) w.[1]
    else app w.[0] w.[1]
  bvar_defined := .mk fun v => by simp [blueprint, bvar]
  fvar_defined := .mk fun v => by simp [blueprint, fvar]
  func_defined := .mk fun v => by
    by_cases hk : v 1 = 1
    · simp [blueprint, hk]
    · by_cases hl : IsLam (v 3).[0] <;>
        simp [blueprint, hk, hl, InternalBoundSubstitution.beta]

end Recursion

noncomputable def complete (t : V) : V :=
  Recursion.construction.result language ![] t

noncomputable def completeFormula : 𝚺₁.Semisentence 2 :=
  Recursion.blueprint.result language

instance complete_defined : 𝚺₁-Function₁ (complete : V → V) via completeFormula :=
  Recursion.construction.result_defined

instance completeDelta_defined :
    𝚫₁-Function₁ (complete : V → V) via completeFormula.graphDelta :=
  complete_defined.graph_delta

instance complete_definable : 𝚺₁-Function₁ (complete : V → V) :=
  complete_defined.to_definable

instance complete_definable' (Γ m) : Γ-[m + 1]-Function₁ (complete : V → V) :=
  complete_definable.of_sigmaOne

@[simp] theorem complete_bvar (i : V) : complete (bvar i) = bvar i := by
  simp [complete, bvar, Recursion.construction]

@[simp] theorem complete_fvar (i : V) : complete (fvar i) = fvar i := by
  simp [complete, fvar, Recursion.construction]

theorem complete_lam (s : V) (hs : IsTerm s) : complete (lam s) = lam (complete s) := by
  have hvec : IsUTermVec language (1 : V) ?[s] := IsUTermVec.adjoin₁_iff.mpr hs
  have computation := Recursion.construction.result_func (L := language) (param := ![])
    (k := (1 : V)) (f := (0 : V)) (v := ?[s]) (w := ?[complete s])
    (by simp) hvec (by simp) (by
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      simp [complete])
  simpa [complete, lam, Recursion.construction] using computation

open Classical in
theorem complete_app (s t : V) (hs : IsTerm s) (ht : IsTerm t) :
    complete (app s t) = if IsLam s then
      InternalBoundSubstitution.beta (lambdaBody (complete s)) (complete t)
    else app (complete s) (complete t) := by
  have hvec : IsUTermVec language (2 : V) ?[s, t] := IsUTermVec.mkSeq₂_iff.mpr ⟨hs, ht⟩
  have computation := Recursion.construction.result_func (L := language) (param := ![])
    (k := (2 : V)) (f := (0 : V)) (v := ?[s, t]) (w := ?[complete s, complete t])
    (by simp) hvec (by simp [one_add_one_eq_two]) (by
      intro i hi
      rcases (lt_two_iff_le_one.trans le_one_iff_eq_zero_or_one).mp hi with rfl | rfl <;>
        simp [complete])
  simpa [complete, app, Recursion.construction] using computation

theorem complete_app_lam (s t : V) (hs : IsTerm s) (ht : IsTerm t) :
    complete (app (lam s) t) = InternalBoundSubstitution.beta (complete s) (complete t) := by
  rw [complete_app (lam s) t (by simpa using hs) ht]
  simp [complete_lam s hs]

theorem complete_app_of_not_lam (s t : V) (hs : IsTerm s) (ht : IsTerm t) (hl : ¬IsLam s) :
    complete (app s t) = app (complete s) (complete t) := by
  rw [complete_app s t hs ht]
  simp [hl]

theorem preserves_terms : ∀ t : V, IsTerm t → IsTerm (complete t) := by
  refine InternalLambdaCode.induction 𝚺
    (P := fun t => IsTerm (complete t)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i; simp
  · intro i; simp
  · intro s hs ih; simpa [complete_lam s hs] using ih
  · intro s t hs ht ihs iht
    by_cases hl : IsLam s
    · obtain ⟨b, rfl⟩ := (isLam_iff s).mp hl
      have hb : IsTerm b := (isTerm_lam_iff b).mp hs
      rw [complete_app_lam b t hb ht]
      have hcb : IsTerm (complete b) := by simpa [complete_lam b hb] using ihs
      exact InternalBoundSubstitution.preserves_terms (complete b) hcb 0 (complete t) iht
    · rw [complete_app_of_not_lam s t hs ht hl]
      simpa using And.intro ihs iht

theorem preserves_scope : ∀ t : V, IsTerm t → ∀ depth,
    IsScoped depth t → IsScoped depth (complete t) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ depth, IsScoped depth t → IsScoped depth (complete t)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i depth h; simpa using h
  · intro i depth _; simp
  · intro s hs ih depth h
    rw [complete_lam s hs, isScoped_lam_iff]
    exact ih (depth + 1) ((isScoped_lam_iff depth s).mp h)
  · intro s t hs ht ihs iht depth h
    obtain ⟨hs', ht'⟩ := (isScoped_app_iff depth s t).mp h
    by_cases hl : IsLam s
    · obtain ⟨b, rfl⟩ := (isLam_iff s).mp hl
      have hb : IsTerm b := (isTerm_lam_iff b).mp hs
      rw [complete_app_lam b t hb ht]
      have hcb : IsScoped (depth + 1) (complete b) := by
        simpa [complete_lam b hb] using ihs depth hs'
      exact InternalBoundSubstitution.beta_scoped hcb (iht depth ht')
    · rw [complete_app_of_not_lam s t hs ht hl, isScoped_app_iff]
      exact ⟨ihs depth hs', iht depth ht'⟩

end FregeanECA.Research.Z2Reverse.InternalCompleteDevelopment
