import FregeanECA.Research.Z2Reverse.InternalBoundSubstitution
import FregeanECA.Research.Z2Reverse.ArithmeticCodeAtoms

/-!
The total numeric presentation of a quotient of internal open lambda terms.
Invalid or ill-scoped codes denote the fixed open variable zero. Conversion
equivalence and application congruence are explicit inputs; no ECA laws or
nontriviality are assumed or asserted by this presentation component.
-/

namespace FregeanECA.Research.Z2Reverse.InternalTermQuotient

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev Scoped (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :=
  {t : V // IsScoped 0 t}

open Classical in
noncomputable def normalize (t : V) : V := if IsScoped 0 t then t else fvar 0

noncomputable def normalizeFormula : 𝚺₁.Semisentence 2 := .mkSigma
  “y t. (!isScopedFormula.sigma 0 t ∧ y = t) ∨
    (¬!isScopedFormula.pi 0 t ∧ !qqFvarDef y 0)”

instance normalize_defined : 𝚺₁-Function₁ (normalize : V → V) via normalizeFormula :=
  .mk fun v => by
    by_cases h : IsScoped 0 (v 1) <;> simp [normalizeFormula, normalize, fvar, h]

instance normalizeDelta_defined :
    𝚫₁-Function₁ (normalize : V → V) via normalizeFormula.graphDelta :=
  normalize_defined.graph_delta

instance normalize_definable : 𝚺₁-Function₁ (normalize : V → V) :=
  normalize_defined.to_definable

instance normalize_definable' (Γ m) : Γ-[m + 1]-Function₁ (normalize : V → V) :=
  normalize_definable.of_sigmaOne

theorem normalize_scoped (t : V) : IsScoped 0 (normalize t) := by
  classical
  by_cases h : IsScoped 0 t <;> simp [normalize, h]

theorem normalize_of_scoped (t : V) (h : IsScoped 0 t) : normalize t = t := by
  classical
  simp [normalize, h]

noncomputable def normalized (t : V) : Scoped V := ⟨normalize t, normalize_scoped t⟩

noncomputable def scopedApp (s t : Scoped V) : Scoped V :=
  ⟨app s.val t.val, (isScoped_app_iff 0 s.val t.val).mpr ⟨s.property, t.property⟩⟩

noncomputable def applyCode (s t : V) : V := app (normalize s) (normalize t)

noncomputable def applyCodeFormula : 𝚺₁.Semisentence 3 := .mkSigma
  “y s t. ∃ a b, !normalizeFormula a s ∧ !normalizeFormula b t ∧ !appFormula y a b”

instance applyCode_defined :
    𝚺₁-Function₂ (applyCode : V → V → V) via applyCodeFormula := .mk fun v => by
  simp [applyCodeFormula, applyCode]

instance applyCode_definable : 𝚺₁-Function₂ (applyCode : V → V → V) :=
  applyCode_defined.to_definable

theorem applyCode_scoped (s t : V) : IsScoped 0 (applyCode s t) :=
  (isScoped_app_iff 0 _ _).mpr ⟨normalize_scoped s, normalize_scoped t⟩

noncomputable def constantK : V := lam (lam (bvar 1))

noncomputable def constantS : V :=
  lam (lam (lam (app (app (bvar 2) (bvar 0)) (app (bvar 1) (bvar 0)))))

theorem constantK_scoped : IsScoped 0 (constantK : V) := by
  simp [constantK]

theorem constantS_scoped : IsScoped 0 (constantS : V) := by
  simp [constantS, one_add_one_eq_two]

structure Conversion (V : Type*) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] where
  relation : V → V → Prop
  equivalence : Equivalence relation
  app_congr : ∀ s s' t t', IsScoped 0 s → IsScoped 0 s' →
    IsScoped 0 t → IsScoped 0 t' → relation s s' → relation t t' →
      relation (app s t) (app s' t')

namespace Conversion

variable (c : Conversion V)

def setoid : Setoid (Scoped V) where
  r s t := c.relation s.val t.val
  iseqv := ⟨fun s => c.equivalence.refl s.val,
    fun h => c.equivalence.symm h, fun h₁ h₂ => c.equivalence.trans h₁ h₂⟩

def Object := Quotient c.setoid

def ofTerm (t : Scoped V) : c.Object := Quotient.mk c.setoid t

noncomputable def decode (t : V) : c.Object := c.ofTerm (normalized t)

theorem decode_onto : Function.Surjective c.decode := by
  intro x
  refine Quotient.inductionOn x ?_
  intro t
  refine ⟨t.val, ?_⟩
  change Quotient.mk c.setoid (normalized t.val) = Quotient.mk c.setoid t
  apply congrArg (Quotient.mk c.setoid)
  apply Subtype.ext
  exact normalize_of_scoped t.val t.property

theorem decode_eq_iff (s t : V) :
    c.decode s = c.decode t ↔ c.relation (normalize s) (normalize t) :=
  Quotient.eq

noncomputable def application (s t : c.Object) : c.Object :=
  Quotient.map₂ scopedApp
    (fun s s' hs t t' ht => c.app_congr s.val s'.val t.val t'.val
      s.property s'.property t.property t'.property hs ht) s t

theorem application_decode (s t : V) :
    c.decode (applyCode s t) = c.application (c.decode s) (c.decode t) := by
  change Quotient.mk c.setoid (normalized (applyCode s t)) =
    Quotient.mk c.setoid (scopedApp (normalized s) (normalized t))
  congr 1
  apply Subtype.ext
  exact normalize_of_scoped _ (applyCode_scoped s t)

noncomputable def presentation : RelationCoding.Presentation c.Object V where
  decode := c.decode
  onto := c.decode_onto
  tuple := ArithmeticCodeAtoms.tupleValue (fun x y => ⟪x, y⟫)

noncomputable def codeOperations :
    c.presentation.CodeOperations c.application (c.decode constantK) (c.decode constantS) where
  apply := applyCode
  constantK := constantK
  constantS := constantS
  apply_law := c.application_decode
  k_law := rfl
  s_law := rfl

end Conversion
end FregeanECA.Research.Z2Reverse.InternalTermQuotient

#print axioms FregeanECA.Research.Z2Reverse.InternalTermQuotient.Conversion.decode_onto
#print axioms FregeanECA.Research.Z2Reverse.InternalTermQuotient.Conversion.decode_eq_iff
#print axioms FregeanECA.Research.Z2Reverse.InternalTermQuotient.Conversion.application_decode
