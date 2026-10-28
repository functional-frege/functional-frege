import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Basic

/-!
Internal raw lambda syntax in arbitrary IΣ1 models.

Every variable index and every syntax code in this file belongs to the
arithmetic model itself. No identification with the standard natural numbers
or external inductive lambda terms is made. Binding scopes and conversion are
separate obligations; this module supplies the internal raw syntax layer.
-/

namespace FregeanECA.Research.Z2Reverse.InternalLambdaCode

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.FormalizedTerm
open scoped FFL.FirstOrder

inductive Func : Nat → Type
  | lam : Func 1
  | app : Func 2

def Func.code : {n : Nat} → Func n → Nat
  | _, .lam => 0
  | _, .app => 0

def Func.decode : (n : Nat) → Nat → Option (Func n)
  | 1, 0 => some .lam
  | 2, 0 => some .app
  | _, _ => none

instance funcEncodable (n : Nat) : Encodable (Func n) where
  encode := Func.code
  decode := Func.decode n
  encodek := by intro f; cases f <;> rfl

def language : FFL.FirstOrder.Language where
  Func := Func
  Rel := fun _ => Empty

instance languageEncodable : language.Encodable where
  func := funcEncodable
  rel := fun _ => inferInstanceAs (Encodable Empty)

theorem code_range (k c : Nat) :
    c ∈ Set.range (Encodable.encode : language.Func k → Nat) ↔
      (k = 1 ∨ k = 2) ∧ c = 0 := by
  constructor
  · rintro ⟨f, rfl⟩
    cases f <;> exact ⟨by simp, rfl⟩
  · rintro ⟨rfl | rfl, rfl⟩
    · exact ⟨Func.lam, rfl⟩
    · exact ⟨Func.app, rfl⟩

instance : language.LORDefinable where
  func := .mkSigma “k f. (k = 1 ∨ k = 2) ∧ f = 0”
  rel := .mkSigma “k r. ⊥”
  func_iff {k c} := by simpa [models_iff] using! code_range k c
  rel_iff := by simp [language]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

@[simp] theorem isFunc_iff (k f : V) :
    language.IsFunc k f ↔ (k = 1 ∨ k = 2) ∧ f = 0 := by
  simp [Language.IsFunc, Language.isFunc, Language.LORDefinable.func]

noncomputable def bvar (index : V) : V := qqBvar index
noncomputable def fvar (index : V) : V := qqFvar index
noncomputable def lam (body : V) : V := qqFunc 1 0 ?[body]
noncomputable def app (left right : V) : V := qqFunc 2 0 ?[left, right]

def lamFormula : 𝚺₁.Semisentence 2 :=
  .mkSigma “t s. ∃ v, !mkVec₁Def v s ∧ !qqFuncDef t 1 0 v”

def appFormula : 𝚺₁.Semisentence 3 :=
  .mkSigma “t s u. ∃ v, !mkVec₂Def v s u ∧ !qqFuncDef t 2 0 v”

instance lam_defined : 𝚺₁-Function₁ (lam : V → V) via lamFormula :=
  .mk fun v => by simp [lamFormula, lam]

instance app_defined : 𝚺₁-Function₂ (app : V → V → V) via appFormula :=
  .mk fun v => by simp [appFormula, app]

instance lam_definable : 𝚺₁-Function₁ (lam : V → V) := lam_defined.to_definable

instance app_definable : 𝚺₁-Function₂ (app : V → V → V) := app_defined.to_definable

/-- Δ1-recognizable internally finite raw terms, including nonstandard codes. -/
def IsTerm (t : V) : Prop := IsUTerm language t

noncomputable def isTermFormula : 𝚫₁.Semisentence 1 := isUTerm language

instance term_defined : 𝚫₁-Predicate (IsTerm (V := V)) via isTermFormula :=
  IsUTerm.defined

instance term_definable : 𝚫₁-Predicate (IsTerm (V := V)) :=
  term_defined.to_definable

@[simp] theorem isTerm_bvar (index : V) : IsTerm (bvar index) :=
  IsUTerm.bvar

@[simp] theorem isTerm_fvar (index : V) : IsTerm (fvar index) :=
  IsUTerm.fvar index

@[simp] theorem isTerm_lam_iff (body : V) :
    IsTerm (lam body) ↔ IsTerm body := by
  simp [IsTerm, lam, IsUTerm.func_iff]

@[simp] theorem isTerm_app_iff (left right : V) :
    IsTerm (app left right) ↔ IsTerm left ∧ IsTerm right := by
  simp [IsTerm, app, IsUTerm.func_iff]

@[simp] theorem bvar_inj (i j : V) : bvar i = bvar j ↔ i = j := by
  simp [bvar]

@[simp] theorem fvar_inj (i j : V) : fvar i = fvar j ↔ i = j := by
  simp [fvar]

@[simp] theorem lam_inj (s t : V) : lam s = lam t ↔ s = t := by
  simp [lam]

@[simp] theorem app_inj (s t u v : V) :
    app s t = app u v ↔ s = u ∧ t = v := by
  simp [app]

@[simp] theorem lam_ne_app (s t u : V) : lam s ≠ app t u := by
  simp [lam, app]

@[simp] theorem bvar_ne_fvar (i j : V) : bvar i ≠ fvar j := by
  simp [bvar, fvar, qqBvar, qqFvar]

@[simp] theorem bvar_ne_lam (i s : V) : bvar i ≠ lam s := by
  simp [bvar, lam, qqBvar, qqFunc]

@[simp] theorem bvar_ne_app (i s t : V) : bvar i ≠ app s t := by
  simp [bvar, app, qqBvar, qqFunc]

@[simp] theorem fvar_ne_lam (i s : V) : fvar i ≠ lam s := by
  simp [fvar, lam, qqFvar, qqFunc]

@[simp] theorem fvar_ne_app (i s t : V) : fvar i ≠ app s t := by
  simp [fvar, app, qqFvar, qqFunc]

theorem index_lt_bvar (i : V) : i < bvar i := var_lt_qqBvar i

theorem index_lt_fvar (i : V) : i < fvar i := var_lt_qqFvar i

theorem body_lt_lam (s : V) : s < lam s :=
  lt_trans (lt_adjoin s 0) (terms_lt_qqFunc 1 0 ?[s])

theorem left_lt_app (s t : V) : s < app s t :=
  lt_trans (lt_adjoin s ?[t]) (terms_lt_qqFunc 2 0 ?[s, t])

theorem right_lt_app (s t : V) : t < app s t :=
  lt_trans (lt_adjoin t 0)
    (lt_trans (lt_adjoin' s ?[t]) (terms_lt_qqFunc 2 0 ?[s, t]))

theorem case_iff (t : V) : IsTerm t ↔
    (∃ i, t = bvar i) ∨ (∃ i, t = fvar i) ∨
    (∃ s, IsTerm s ∧ t = lam s) ∨
    (∃ s u, IsTerm s ∧ IsTerm u ∧ t = app s u) := by
  constructor
  · intro ht
    rcases (IsUTerm.case_iff.mp ht) with ⟨i, rfl⟩ | ⟨i, rfl⟩ |
      ⟨k, f, args, hk, hargs, rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · rcases (isFunc_iff k f).mp hk with ⟨rfl | rfl, rfl⟩
      · obtain ⟨s, hs⟩ := eq_singleton_iff_len_eq_one.mp hargs.lh.symm
        subst args
        exact Or.inr (Or.inr (Or.inl ⟨s, IsUTermVec.adjoin₁_iff.mp hargs, rfl⟩))
      · obtain ⟨s, u, hs, hu, rfl⟩ := IsUTermVec.two_iff.mp hargs
        exact Or.inr (Or.inr (Or.inr ⟨s, u, hs, hu, rfl⟩))
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, u, hs, hu, rfl⟩)
    · exact isTerm_bvar i
    · exact isTerm_fvar i
    · exact (isTerm_lam_iff s).mpr hs
    · exact (isTerm_app_iff s u).mpr ⟨hs, hu⟩

/-- Induction is restricted to internally definable predicates. -/
theorem induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (hb : ∀ i, P (bvar i)) (hf : ∀ i, P (fvar i))
    (hl : ∀ s, IsTerm s → P s → P (lam s))
    (ha : ∀ s t, IsTerm s → IsTerm t → P s → P t → P (app s t)) :
    ∀ t, IsTerm t → P t := by
  apply IsUTerm.induction (L := language) Γ hP hb hf
  intro k f args hk hargs ih
  rcases (isFunc_iff k f).mp hk with ⟨rfl | rfl, rfl⟩
  · obtain ⟨s, hs⟩ := eq_singleton_iff_len_eq_one.mp hargs.lh.symm
    subst args
    exact hl s (IsUTermVec.adjoin₁_iff.mp hargs) (by simpa using ih 0 (by simp))
  · obtain ⟨s, t, hs, ht, rfl⟩ := IsUTermVec.two_iff.mp hargs
    exact ha s t hs ht (by simpa using ih 0 (by simp))
      (by simpa using ih 1 (by simp))

namespace FreeBound

def blueprint : Bootstrapping.Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “y z. y = 0”
  fvar := .mkSigma “y x. y = x + 1”
  func := .mkSigma “y k f v w. !listMaxDef y w”

noncomputable def construction : Bootstrapping.Language.TermRec.Construction V blueprint where
  bvar _ _ := 0
  fvar _ x := x + 1
  func _ _ _ _ w := listMax w
  bvar_defined := .mk fun v => by simp [blueprint]
  fvar_defined := .mk fun v => by simp [blueprint]
  func_defined := .mk fun v => by simp [blueprint]

end FreeBound

/-- One more than the greatest free-variable index, or zero for no free variables.
The recursion is internally total, including on nonstandard syntax codes. -/
noncomputable def freeBound (t : V) : V := FreeBound.construction.result language ![] t

noncomputable def freeBoundFormula : 𝚺₁.Semisentence 2 :=
  FreeBound.blueprint.result language

instance freeBound_defined : 𝚺₁-Function₁ (freeBound : V → V) via freeBoundFormula :=
  FreeBound.construction.result_defined

instance freeBound_definable : 𝚺₁-Function₁ (freeBound : V → V) :=
  freeBound_defined.to_definable

@[simp] theorem freeBound_bvar (i : V) : freeBound (bvar i) = 0 := by
  simp [freeBound, bvar, FreeBound.construction]

@[simp] theorem freeBound_fvar (i : V) : freeBound (fvar i) = i + 1 := by
  simp [freeBound, fvar, FreeBound.construction]

theorem freeBound_lam (s : V) (hs : IsTerm s) : freeBound (lam s) = freeBound s := by
  have hvec : IsUTermVec language (1 : V) ?[s] := IsUTermVec.adjoin₁_iff.mpr hs
  have computation := FreeBound.construction.result_func (L := language) (param := ![])
    (k := (1 : V)) (f := (0 : V)) (v := ?[s]) (w := ?[freeBound s])
    (by simp) hvec (by simp)
    (by
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      simp [freeBound])
  simpa [freeBound, lam, FreeBound.construction] using computation

theorem freeBound_app (s t : V) (hs : IsTerm s) (ht : IsTerm t) :
    freeBound (app s t) = max (freeBound s) (freeBound t) := by
  have hvec : IsUTermVec language (2 : V) ?[s, t] := IsUTermVec.mkSeq₂_iff.mpr ⟨hs, ht⟩
  have computation := FreeBound.construction.result_func (L := language) (param := ![])
    (k := (2 : V)) (f := (0 : V)) (v := ?[s, t]) (w := ?[freeBound s, freeBound t])
    (by simp) hvec (by simp [one_add_one_eq_two]) (by
      intro i hi
      rcases (lt_two_iff_le_one.trans le_one_iff_eq_zero_or_one).mp hi with rfl | rfl <;>
        simp [freeBound])
  simpa [freeBound, app, FreeBound.construction] using computation

end FregeanECA.Research.Z2Reverse.InternalLambdaCode
