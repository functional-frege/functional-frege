import FregeanECA.Research.Z2Reverse.InternalLambdaEmbedding

/-!
Internal recursion on lambda codes with a parameter that changes under binders.
Totality and definability come from Foundation's `UformulaRec1`, applied to the
internal formula encoding. All parameters and indices range over the model.
-/

namespace FregeanECA.Research.Z2Reverse.InternalBinderRecursion

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaEmbedding
open scoped FFL.FirstOrder

structure Blueprint where
  bvar : 𝚺₁.Semisentence 3
  fvar : 𝚺₁.Semisentence 3
  app : 𝚺₁.Semisentence 4
  lam : 𝚺₁.Semisentence 3
  change : 𝚺₁.Semisentence 2

namespace Blueprint

def formulaBlueprint (β : Blueprint) : UformulaRec1.Blueprint where
  rel := .mkSigma “y p k r v. ∃ t i, !nthDef t v 0 ∧ !sndIdxDef i t ∧ !β.bvar y p i”
  nrel := .mkSigma “y p k r v. ∃ t i, !nthDef t v 0 ∧ !sndIdxDef i t ∧ !β.fvar y p i”
  verum := .mkSigma “y p. y = 0”
  falsum := .mkSigma “y p. y = 0”
  and := .mkSigma “y p s t u v. !β.app y p u v”
  or := .mkSigma “y p s t u v. !β.app y p u v”
  all := .mkSigma “y p s u. !β.lam y p u”
  exs := .mkSigma “y p s u. !β.lam y p u”
  allChanges := β.change
  exsChanges := β.change

noncomputable def resultFormula (β : Blueprint) : 𝚺₁.Semisentence 3 := .mkSigma
  “y p t. ∃ e, !encodeFormula e t ∧ !(β.formulaBlueprint.result ℒₒᵣ) y p e”

end Blueprint

variable (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

structure Construction (β : Blueprint) where
  bvar : V → V → V
  fvar : V → V → V
  app : V → V → V → V
  lam : V → V → V
  change : V → V
  bvar_defined : 𝚺₁-Function₂ bvar via β.bvar
  fvar_defined : 𝚺₁-Function₂ fvar via β.fvar
  app_defined : 𝚺₁-Function₃ app via β.app
  lam_defined : 𝚺₁-Function₂ lam via β.lam
  change_defined : 𝚺₁-Function₁ change via β.change

variable {V}

namespace Construction

variable {β : Blueprint} (c : Construction V β)

noncomputable def formulaConstruction : UformulaRec1.Construction V β.formulaBlueprint where
  rel p _ _ v := c.bvar p (sndIdx v.[0])
  nrel p _ _ v := c.fvar p (sndIdx v.[0])
  verum _ := 0
  falsum _ := 0
  and p _ _ u v := c.app p u v
  or p _ _ u v := c.app p u v
  all p _ u := c.lam p u
  exs p _ u := c.lam p u
  allChanges := c.change
  exsChanges := c.change
  rel_defined := .mk fun v => by
    have := c.bvar_defined
    simp [Blueprint.formulaBlueprint]
  nrel_defined := .mk fun v => by
    have := c.fvar_defined
    simp [Blueprint.formulaBlueprint]
  verum_defined := .mk fun v => by simp [Blueprint.formulaBlueprint]
  falsum_defined := .mk fun v => by simp [Blueprint.formulaBlueprint]
  and_defined := .mk fun v => by
    have := c.app_defined
    simp [Blueprint.formulaBlueprint]
  or_defined := .mk fun v => by
    have := c.app_defined
    simp [Blueprint.formulaBlueprint]
  all_defined := .mk fun v => by
    have := c.lam_defined
    simp [Blueprint.formulaBlueprint]
  exs_defined := .mk fun v => by
    have := c.lam_defined
    simp [Blueprint.formulaBlueprint]
  allChanges_defined := c.change_defined
  exChanges_defined := c.change_defined

noncomputable def result (param term : V) : V :=
  c.formulaConstruction.result ℒₒᵣ param (encodeTerm term)

theorem result_defined : 𝚺₁-Function₂ c.result via β.resultFormula := .mk fun v => by
  have := c.formulaConstruction.result_defined (L := ℒₒᵣ)
  simp [Blueprint.resultFormula, result]

theorem resultDelta_defined : 𝚫₁-Function₂ c.result via β.resultFormula.graphDelta :=
  c.result_defined.graph_delta

instance result_definable : 𝚺₁-Function₂ c.result := c.result_defined.to_definable

instance result_definable' (Γ m) : Γ-[m + 1]-Function₂ c.result :=
  c.result_definable.of_sigmaOne

@[simp] theorem result_bvar (param i : V) :
    c.result param (InternalLambdaCode.bvar i) = c.bvar param i := by
  rw [result, encode_bvar,
    c.formulaConstruction.result_rel (L := ℒₒᵣ) (param := param)
      (k := 2) (R := 0) (v := ?[qqBvar i, qqBvar i]) (by simp) (by simp)]
  simp [formulaConstruction, sndIdx, qqBvar]

@[simp] theorem result_fvar (param i : V) :
    c.result param (InternalLambdaCode.fvar i) = c.fvar param i := by
  rw [result, encode_fvar,
    c.formulaConstruction.result_nrel (L := ℒₒᵣ) (param := param)
      (k := 2) (R := 0) (v := ?[qqFvar i, qqFvar i]) (by simp) (by simp)]
  simp [formulaConstruction, sndIdx, qqFvar]

theorem result_app (param s t : V) (hs : IsTerm s) (ht : IsTerm t) :
    c.result param (InternalLambdaCode.app s t) =
      c.app param (c.result param s) (c.result param t) := by
  simp [result, encode_app s t hs ht, encode_valid s hs, encode_valid t ht,
    formulaConstruction]

theorem result_lam (param s : V) (hs : IsTerm s) :
    c.result param (InternalLambdaCode.lam s) =
      c.lam param (c.result (c.change param) s) := by
  simp [result, encode_lam s hs, encode_valid s hs, formulaConstruction]

end Construction

end FregeanECA.Research.Z2Reverse.InternalBinderRecursion

