import FregeanECA.Research.Z2Reverse.InternalBindFree
import FregeanECA.Research.Z2Reverse.InternalBoundSubstitution

/-!
The internal beta law for abstraction of a free name, with capture avoidance
proved uniformly for arbitrary model-valued syntax codes and binder depths.
These are syntax-operation identities, not yet a confluence or nontriviality
theorem for internal beta-eta conversion.
-/

namespace FregeanECA.Research.Z2Reverse.InternalAbstraction

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBindFree
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- After binding a free name, substitution for that binder is the original
free-name substitution. The replacement has no escaping bound indices. -/
theorem substitute_bindFree : ∀ t : V, IsTerm t → ∀ name depth replacement,
    IsScoped depth t → IsScoped 0 replacement →
    InternalBoundSubstitution.substitute (bindFree t name depth) depth replacement =
      InternalFreeSubstitution.substitute t name replacement := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ name depth replacement, IsScoped depth t → IsScoped 0 replacement →
      InternalBoundSubstitution.substitute (bindFree t name depth) depth replacement =
        InternalFreeSubstitution.substitute t name replacement) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i name depth replacement hi _
    rw [bindFree_bvar,
      InternalBoundSubstitution.substitute_bvar_lt i depth replacement
        ((isScoped_bvar_iff depth i).mp hi),
      InternalFreeSubstitution.substitute_bvar]
  · intro i name depth replacement _ _
    by_cases h : i = name
    · subst i; simp
    · simp [bindFree_fvar_ne i name depth h,
        InternalFreeSubstitution.substitute_fvar_ne i name replacement h]
  · intro s hs ih name depth replacement ht hr
    rw [bindFree_lam s name depth hs,
      InternalBoundSubstitution.substitute_lam _ depth replacement
        (InternalBindFree.preserves_terms s hs name (depth + 1)),
      InternalBoundShift.shift_of_scoped replacement hr.term 0 1 hr,
      ih name (depth + 1) replacement ((isScoped_lam_iff depth s).mp ht) hr,
      InternalFreeSubstitution.substitute_lam s name replacement hs]
  · intro s t hs ht ihs iht name depth replacement hscope hr
    obtain ⟨hs', ht'⟩ := (isScoped_app_iff depth s t).mp hscope
    rw [bindFree_app s t name depth hs ht,
      InternalBoundSubstitution.substitute_app _ _ depth replacement
        (InternalBindFree.preserves_terms s hs name depth)
        (InternalBindFree.preserves_terms t ht name depth),
      ihs name depth replacement hs' hr, iht name depth replacement ht' hr,
      InternalFreeSubstitution.substitute_app s t name replacement hs ht]

theorem beta_bindFree (t name replacement : V)
    (ht : IsScoped 0 t) (hr : IsScoped 0 replacement) :
    InternalBoundSubstitution.beta (bindFree t name 0) replacement =
      InternalFreeSubstitution.substitute t name replacement :=
  substitute_bindFree t ht.term name 0 replacement ht hr

/-- The body obtained by abstracting a fresh argument has the eta shape. -/
theorem abstractFree_fresh_application (t name : V) (ht : IsTerm t)
    (hfresh : freeBound t ≤ name) :
    abstractFree (app t (fvar name)) name = lam (app t (bvar 0)) := by
  rw [abstractFree, bindFree_app t (fvar name) name 0 ht (by simp),
    fresh_bindFree t ht name 0 hfresh, bindFree_fvar_same]

end FregeanECA.Research.Z2Reverse.InternalAbstraction

#print axioms FregeanECA.Research.Z2Reverse.InternalAbstraction.substitute_bindFree
#print axioms FregeanECA.Research.Z2Reverse.InternalAbstraction.beta_bindFree
#print axioms FregeanECA.Research.Z2Reverse.InternalAbstraction.abstractFree_fresh_application
