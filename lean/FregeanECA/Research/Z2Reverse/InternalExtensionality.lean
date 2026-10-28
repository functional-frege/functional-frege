import FregeanECA.Research.Z2Reverse.InternalBindFreeLaws
import FregeanECA.Research.Z2Reverse.InternalConversionCongruence

/-!
Extensionality of internal open-term conversion. A fresh internal free name
is abstracted by a definable operation, so the argument works for nonstandard
syntax and nonstandard conversion certificates as well as standard terms.
-/
namespace FregeanECA.Research.Z2Reverse.InternalExtensionality

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open InternalBindFree InternalParallelBeta InternalEtaReduction
open InternalConversionCongruence InternalPaths
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem parallel_bindFree {n s t : V} (h : Parallel n s t) (name : V) :
    Parallel (n + 1) (bindFree s name n) (bindFree t name n) := by
  have all : ∀ n s t : V, Parallel n s t → ∀ name,
      Parallel (n + 1) (bindFree s name n) (bindFree t name n) := by
    apply parallel_induction_pa
      (P := fun n s t => ∀ name, Parallel (n + 1) (bindFree s name n) (bindFree t name n))
    · apply Language.Definable.all
      apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
      definability
    · intro n i hi name
      simp only [bindFree_bvar]
      exact Parallel.bvar _ _ (lt_of_lt_of_le hi (by simp))
    · intro n i name
      by_cases hi : i = name
      · subst i
        simp only [bindFree_fvar_same]
        exact Parallel.bvar _ _ (by simp)
      · rw [bindFree_fvar_ne i name n hi]
        exact Parallel.fvar _ _
    · intro n a a' b b' ha hb iha ihb name
      rw [bindFree_app a b name n ha.scopes.1.term hb.scopes.1.term,
        bindFree_app a' b' name n ha.scopes.2.term hb.scopes.2.term]
      exact (iha name).app (ihb name)
    · intro n a a' ha ih name
      rw [bindFree_lam a name n ha.scopes.1.term,
        bindFree_lam a' name n ha.scopes.2.term]
      exact (ih name).lam
    · intro n a a' b b' ha hb iha ihb name
      rw [bindFree_app (lam a) b name n (by simpa using ha.scopes.1.term) hb.scopes.1.term,
        bindFree_lam a name n ha.scopes.1.term,
        bindFree_beta a' b' name n ha.scopes.2.term hb.scopes.2.term]
      exact (iha name).beta (ihb name)
  exact all n s t h name

theorem bindFree_expansion (t name depth : V) (ht : IsTerm t) :
    bindFree (expansion t) name depth = expansion (bindFree t name depth) := by
  have hw := InternalBoundShift.preserves_terms t ht 0 1
  unfold expansion
  rw [bindFree_lam _ name depth (by simp [hw]),
    bindFree_app _ _ name (depth + 1) hw (by simp), bindFree_bvar,
    bindFree_shift t ht name depth 0 1 (by simp)]

theorem eta_bindFree {n s t : V} (h : Step n s t) (name : V) :
    Step (n + 1) (bindFree s name n) (bindFree t name n) := by
  have all : ∀ n s t : V, Step n s t → ∀ name,
      Step (n + 1) (bindFree s name n) (bindFree t name n) := by
    apply step_induction
      (P := fun n s t => ∀ name, Step (n + 1) (bindFree s name n) (bindFree t name n))
    · apply Language.Definable.all
      apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
      definability
    · intro n t ht name
      rw [bindFree_expansion t name n ht.term]
      exact Step.eta (InternalBindFree.preserves_scope t ht.term name n ht)
    · intro n a b q h ih hq name
      rw [bindFree_app a q name n h.scopes.1.term hq.term,
        bindFree_app b q name n h.scopes.2.term hq.term]
      exact (ih name).app_left (InternalBindFree.preserves_scope q hq.term name n hq)
    · intro n a b q h ih hq name
      rw [bindFree_app q a name n hq.term h.scopes.1.term,
        bindFree_app q b name n hq.term h.scopes.2.term]
      exact (ih name).app_right (InternalBindFree.preserves_scope q hq.term name n hq)
    · intro n a b h ih name
      rw [bindFree_lam a name n h.scopes.1.term,
        bindFree_lam b name n h.scopes.2.term]
      exact (ih name).lam
  exact all n s t h name

theorem convert_bindFree {n s t : V}
    (h : Convert (fun a b => Parallel n a b ∨ Step n a b) s t) (name : V) :
    Convert (fun a b => Parallel (n + 1) a b ∨ Step (n + 1) a b)
      (bindFree s name n) (bindFree t name n) := by
  apply map_convert _ _ (union_definable _) (union_definable _) (fun t => bindFree t name n) ?_ ?_ h
  · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
    definability
  · intro a b edge
    exact edge.elim (fun h => Or.inl (parallel_bindFree h name))
      (fun h => Or.inr (eta_bindFree h name))

theorem abstractFree_convert {s t : V} (h : conversion.relation s t) (name : V) :
    conversion.relation (abstractFree s name) (abstractFree t name) :=
  convert_lam (convert_bindFree h name)

theorem abstractFree_fresh_convert (t name : V) (ht : IsScoped 0 t)
    (hfresh : freeBound t ≤ name) :
    conversion.relation (abstractFree (app t (fvar name)) name) t := by
  rw [InternalAbstraction.abstractFree_fresh_application t name ht.term hfresh]
  have eta := Step.eta ht
  rw [expansion, shift_of_scoped t ht.term 0 1 ht] at eta
  exact convert_single (Or.inr eta)

/-- Agreement on every argument implies equality of the internal open terms. -/
theorem extensional {s t : V} (hs : IsScoped 0 s) (ht : IsScoped 0 t)
    (pointwise : ∀ q, IsScoped 0 q → conversion.relation (app s q) (app t q)) :
    conversion.relation s t := by
  let name := max (freeBound s) (freeBound t)
  have h := abstractFree_convert (pointwise (fvar name) (by simp)) name
  have left := abstractFree_fresh_convert s name hs (le_max_left _ _)
  have right := abstractFree_fresh_convert t name ht (le_max_right _ _)
  exact conversion.equivalence.trans (conversion.equivalence.symm left)
    (conversion.equivalence.trans h right)

/-- Extensionality is inherited by the quotient's application operation. -/
theorem quotient_extensional (x y : (conversion (V := V)).Object)
    (pointwise : ∀ z, conversion.application x z = conversion.application y z) : x = y := by
  revert pointwise
  refine Quotient.inductionOn x ?_
  intro s
  refine Quotient.inductionOn y ?_
  intro t h
  apply Quotient.sound
  apply extensional s.property t.property
  intro q hq
  exact Quotient.exact (h (conversion.ofTerm ⟨q, hq⟩))

end FregeanECA.Research.Z2Reverse.InternalExtensionality

#print axioms FregeanECA.Research.Z2Reverse.InternalExtensionality.extensional
#print axioms FregeanECA.Research.Z2Reverse.InternalExtensionality.quotient_extensional
