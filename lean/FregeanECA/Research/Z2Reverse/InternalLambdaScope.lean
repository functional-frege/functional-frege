import FregeanECA.Research.Z2Reverse.InternalLambdaCode

/-!
Binder scope for internal lambda terms over an arbitrary IΣ1 model.

The required number of enclosing binders is computed by an internally total
recursion. Abstraction decreases this requirement by truncated predecessor.
Both the binder depth and every syntax index range over the arithmetic model.
This module does not define substitution or beta-eta conversion.
-/

namespace FregeanECA.Research.Z2Reverse.InternalLambdaScope

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace RequiredDepth

def blueprint : Bootstrapping.Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = z + 1”
  fvar := .mkSigma “y x. y = 0”
  func := .mkSigma
    “y k f v w.
      (k = 1 ∧ ∃ d, !nthDef d w 0 ∧ !subDef y d 1) ∨
      (k ≠ 1 ∧ !listMaxDef y w)”

open Classical in
noncomputable def construction : Bootstrapping.Language.TermRec.Construction V blueprint where
  bvar _ i := i + 1
  fvar _ _ := 0
  func _ k _ _ w := if k = 1 then w.[0] - 1 else listMax w
  bvar_defined := .mk fun v => by simp [blueprint]
  fvar_defined := .mk fun v => by simp [blueprint]
  func_defined := .mk fun v => by
    simp only [blueprint]
    by_cases h : v 1 = 1 <;> simp [h]

end RequiredDepth

noncomputable def requiredDepth (t : V) : V :=
  RequiredDepth.construction.result language ![] t

noncomputable def requiredDepthFormula : 𝚺₁.Semisentence 2 :=
  RequiredDepth.blueprint.result language

noncomputable def requiredDepthDeltaFormula : 𝚫₁.Semisentence 2 :=
  requiredDepthFormula.graphDelta

instance requiredDepth_defined :
    𝚺₁-Function₁ (requiredDepth : V → V) via requiredDepthFormula :=
  RequiredDepth.construction.result_defined

instance requiredDepthDelta_defined :
    𝚫₁-Function₁ (requiredDepth : V → V) via requiredDepthDeltaFormula :=
  requiredDepth_defined.graph_delta

instance requiredDepth_definable : 𝚺₁-Function₁ (requiredDepth : V → V) :=
  requiredDepth_defined.to_definable

@[simp] theorem requiredDepth_bvar (i : V) : requiredDepth (bvar i) = i + 1 := by
  simp [requiredDepth, bvar, RequiredDepth.construction]

@[simp] theorem requiredDepth_fvar (i : V) : requiredDepth (fvar i) = 0 := by
  simp [requiredDepth, fvar, RequiredDepth.construction]

theorem requiredDepth_lam (s : V) (hs : IsTerm s) :
    requiredDepth (lam s) = requiredDepth s - 1 := by
  have hvec : IsUTermVec language (1 : V) ?[s] := IsUTermVec.adjoin₁_iff.mpr hs
  have computation := RequiredDepth.construction.result_func (L := language) (param := ![])
    (k := (1 : V)) (f := (0 : V)) (v := ?[s]) (w := ?[requiredDepth s])
    (by simp) hvec (by simp) (by
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      simp [requiredDepth])
  simpa [requiredDepth, lam, RequiredDepth.construction] using computation

theorem requiredDepth_app (s t : V) (hs : IsTerm s) (ht : IsTerm t) :
    requiredDepth (app s t) = max (requiredDepth s) (requiredDepth t) := by
  have hvec : IsUTermVec language (2 : V) ?[s, t] := IsUTermVec.mkSeq₂_iff.mpr ⟨hs, ht⟩
  have computation := RequiredDepth.construction.result_func (L := language) (param := ![])
    (k := (2 : V)) (f := (0 : V)) (v := ?[s, t])
    (w := ?[requiredDepth s, requiredDepth t])
    (by simp) hvec (by simp [one_add_one_eq_two]) (by
      intro i hi
      rcases (lt_two_iff_le_one.trans le_one_iff_eq_zero_or_one).mp hi with rfl | rfl <;>
        simp [requiredDepth])
  simpa [requiredDepth, app, RequiredDepth.construction] using computation

/-- Well-scoping at an arbitrary model-valued binder depth. -/
def IsScoped (depth term : V) : Prop := IsTerm term ∧ requiredDepth term ≤ depth

noncomputable def isScopedFormula : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “n t. !isTermFormula.sigma t ∧ ∃ d, !requiredDepthFormula d t ∧ d ≤ n”)
  (.mkPi “n t. !isTermFormula.pi t ∧ ∀ d, !requiredDepthFormula d t → d ≤ n”)

instance scoped_defined : 𝚫₁-Relation (IsScoped (V := V)) via isScopedFormula :=
  ⟨by
      intro v
      simp [isScopedFormula, requiredDepth_defined.iff],
   by
      intro v
      simp [isScopedFormula, IsScoped, requiredDepth_defined.iff]⟩

instance scoped_definable : 𝚫₁-Relation (IsScoped (V := V)) :=
  scoped_defined.to_definable

@[simp] theorem isScoped_bvar_iff (depth i : V) :
    IsScoped depth (bvar i) ↔ i < depth := by
  simp [IsScoped, succ_le_iff_lt]

@[simp] theorem isScoped_fvar (depth i : V) : IsScoped depth (fvar i) := by
  simp [IsScoped]

@[simp] theorem isScoped_lam_iff (depth s : V) :
    IsScoped depth (lam s) ↔ IsScoped (depth + 1) s := by
  by_cases hs : IsTerm s
  · simp [IsScoped, hs, requiredDepth_lam s hs, tsub_le_iff_right]
  · simp [IsScoped, hs]

@[simp] theorem isScoped_app_iff (depth s t : V) :
    IsScoped depth (app s t) ↔ IsScoped depth s ∧ IsScoped depth t := by
  by_cases hs : IsTerm s <;> by_cases ht : IsTerm t <;>
    simp [IsScoped, hs, ht, requiredDepth_app s t]

theorem IsScoped.mono {depth depth' t : V} (h : IsScoped depth t) (hle : depth ≤ depth') :
    IsScoped depth' t := ⟨h.1, le_trans h.2 hle⟩

theorem IsScoped.term {depth t : V} (h : IsScoped depth t) : IsTerm t := h.1

theorem isScoped_at_requiredDepth (t : V) (ht : IsTerm t) :
    IsScoped (requiredDepth t) t := ⟨ht, le_refl _⟩

theorem has_scope_iff (t : V) : (∃ depth, IsScoped depth t) ↔ IsTerm t :=
  ⟨fun ⟨_, h⟩ => h.1, fun ht => ⟨requiredDepth t, isScoped_at_requiredDepth t ht⟩⟩

theorem case_iff (depth t : V) : IsScoped depth t ↔
    (∃ i, i < depth ∧ t = bvar i) ∨ (∃ i, t = fvar i) ∨
    (∃ s, IsScoped (depth + 1) s ∧ t = lam s) ∨
    (∃ s u, IsScoped depth s ∧ IsScoped depth u ∧ t = app s u) := by
  constructor
  · intro ht
    rcases (InternalLambdaCode.case_iff t).mp ht.1 with
      ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨s, _, rfl⟩ | ⟨s, u, _, _, rfl⟩
    · exact Or.inl ⟨i, (isScoped_bvar_iff depth i).mp ht, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨s, (isScoped_lam_iff depth s).mp ht, rfl⟩))
    · obtain ⟨hs, hu⟩ := (isScoped_app_iff depth s u).mp ht
      exact Or.inr (Or.inr (Or.inr ⟨s, u, hs, hu, rfl⟩))
  · rintro (⟨i, hi, rfl⟩ | ⟨i, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, u, hs, hu, rfl⟩)
    · exact (isScoped_bvar_iff depth i).mpr hi
    · exact isScoped_fvar depth i
    · exact (isScoped_lam_iff depth s).mpr hs
    · exact (isScoped_app_iff depth s u).mpr ⟨hs, hu⟩

end FregeanECA.Research.Z2Reverse.InternalLambdaScope
