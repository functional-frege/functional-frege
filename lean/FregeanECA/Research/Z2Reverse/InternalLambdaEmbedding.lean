import FregeanECA.Research.Z2Reverse.InternalFreeSubstitution
import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Basic

/-!
Internal lambda syntax embedded into internal formula syntax as a data format.
Formula truth plays no role: positive/negative atoms distinguish bound/free
variables, conjunction stores application, and universal binding stores lambda.
This lets Foundation's parameter-changing recursor operate on lambda codes.
-/

namespace FregeanECA.Research.Z2Reverse.InternalLambdaEmbedding

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Recursion

def blueprint : Bootstrapping.Language.TermRec.Blueprint 0 where
  bvar := .mkSigma
    “y i. ∃ t w, !qqBvarDef t i ∧ !mkVec₂Def w t t ∧ !qqRelDef y 2 0 w”
  fvar := .mkSigma
    “y i. ∃ t w, !qqFvarDef t i ∧ !mkVec₂Def w t t ∧ !qqNRelDef y 2 0 w”
  func := .mkSigma
    “y k f v w.
      (k = 1 ∧ ∃ s, !nthDef s w 0 ∧ !qqAllDef y s) ∨
      (k ≠ 1 ∧ ∃ s t, !nthDef s w 0 ∧ !nthDef t w 1 ∧ !qqAndDef y s t)”

open Classical in
noncomputable def construction : Bootstrapping.Language.TermRec.Construction V blueprint where
  bvar _ i := qqRel 2 0 ?[qqBvar i, qqBvar i]
  fvar _ i := qqNRel 2 0 ?[qqFvar i, qqFvar i]
  func _ k _ _ w := if k = 1 then qqAll w.[0] else qqAnd w.[0] w.[1]
  bvar_defined := .mk fun v => by simp [blueprint]
  fvar_defined := .mk fun v => by simp [blueprint]
  func_defined := .mk fun v => by
    by_cases h : v 1 = 1 <;> simp [blueprint, h]

end Recursion

noncomputable def encodeTerm (t : V) : V :=
  Recursion.construction.result language ![] t

noncomputable def encodeFormula : 𝚺₁.Semisentence 2 :=
  Recursion.blueprint.result language

instance encode_defined : 𝚺₁-Function₁ (encodeTerm : V → V) via encodeFormula :=
  Recursion.construction.result_defined

instance encodeDelta_defined :
    𝚫₁-Function₁ (encodeTerm : V → V) via encodeFormula.graphDelta :=
  encode_defined.graph_delta

instance encode_definable : 𝚺₁-Function₁ (encodeTerm : V → V) :=
  encode_defined.to_definable

instance encode_definable' (Γ m) : Γ-[m + 1]-Function₁ (encodeTerm : V → V) :=
  encode_definable.of_sigmaOne

@[simp] theorem encode_bvar (i : V) :
    encodeTerm (bvar i) = qqRel 2 0 ?[qqBvar i, qqBvar i] := by
  simp [encodeTerm, bvar, Recursion.construction]

@[simp] theorem encode_fvar (i : V) :
    encodeTerm (fvar i) = qqNRel 2 0 ?[qqFvar i, qqFvar i] := by
  simp [encodeTerm, fvar, Recursion.construction]

theorem encode_lam (s : V) (hs : IsTerm s) :
    encodeTerm (lam s) = qqAll (encodeTerm s) := by
  have hvec : IsUTermVec language (1 : V) ?[s] := IsUTermVec.adjoin₁_iff.mpr hs
  have computation := Recursion.construction.result_func (L := language) (param := ![])
    (k := (1 : V)) (f := (0 : V)) (v := ?[s]) (w := ?[encodeTerm s])
    (by simp) hvec (by simp) (by
      intro i hi
      have : i = 0 := by simpa using hi
      subst i
      simp [encodeTerm])
  simpa [encodeTerm, lam, Recursion.construction] using computation

theorem encode_app (s t : V) (hs : IsTerm s) (ht : IsTerm t) :
    encodeTerm (app s t) = qqAnd (encodeTerm s) (encodeTerm t) := by
  have hvec : IsUTermVec language (2 : V) ?[s, t] := IsUTermVec.mkSeq₂_iff.mpr ⟨hs, ht⟩
  have computation := Recursion.construction.result_func (L := language) (param := ![])
    (k := (2 : V)) (f := (0 : V)) (v := ?[s, t]) (w := ?[encodeTerm s, encodeTerm t])
    (by simp) hvec (by simp [one_add_one_eq_two]) (by
      intro i hi
      rcases (lt_two_iff_le_one.trans le_one_iff_eq_zero_or_one).mp hi with rfl | rfl <;>
        simp [encodeTerm])
  simpa [encodeTerm, app, Recursion.construction] using computation

@[simp] theorem arithmetic_zero_relation : (ℒₒᵣ).IsRel (2 : V) 0 := by
  simpa [Bootstrapping.Arithmetic.eqIndex] using!
    (Bootstrapping.Arithmetic.LOR_rel_eqIndex (V := V))

theorem encode_valid : ∀ t : V, IsTerm t → IsUFormula ℒₒᵣ (encodeTerm t) := by
  refine InternalLambdaCode.induction 𝚺
    (P := fun t => IsUFormula ℒₒᵣ (encodeTerm t)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i; simp
  · intro i; simp
  · intro s hs ih; simpa [encode_lam s hs] using ih
  · intro s t hs ht ihs iht
    simpa [encode_app s t hs ht] using And.intro ihs iht

end FregeanECA.Research.Z2Reverse.InternalLambdaEmbedding
