import FregeanECA.Research.Z2Reverse.InternalAbstraction

/-!
Binding a free name commutes with weakening and capture-avoiding bound
substitution. All names, binder depths and syntax codes are model elements.
-/
namespace FregeanECA.Research.Z2Reverse.InternalBindFree

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bindFree_shift : ∀ t : V, IsTerm t → ∀ name depth cutoff increment,
    cutoff ≤ depth →
    bindFree (shift t cutoff increment) name (depth + increment) =
      shift (bindFree t name depth) cutoff increment := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ name depth cutoff increment, cutoff ≤ depth →
      bindFree (shift t cutoff increment) name (depth + increment) =
        shift (bindFree t name depth) cutoff increment) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i name depth cutoff increment _
    by_cases hi : i < cutoff
    · simp [shift_bvar_lt i cutoff increment hi]
    · simp [shift_bvar_ge i cutoff increment (not_lt.mp hi)]
  · intro i name depth cutoff increment hc
    by_cases hi : i = name
    · subst i
      simp [shift_bvar_ge depth cutoff increment hc]
    · simp [bindFree_fvar_ne i name _ hi]
  · intro t ht ih name depth cutoff increment hc
    rw [shift_lam t cutoff increment ht,
      bindFree_lam _ name (depth + increment)
        (InternalBoundShift.preserves_terms t ht (cutoff + 1) increment),
      bindFree_lam t name depth ht,
      shift_lam _ cutoff increment (InternalBindFree.preserves_terms t ht name (depth + 1))]
    congr 1
    simpa [add_assoc, add_comm, add_left_comm] using
      ih name (depth + 1) (cutoff + 1) increment (by simpa [add_comm] using add_le_add_right hc (1 : V))
  · intro s t hs ht ihs iht name depth cutoff increment hc
    rw [shift_app s t cutoff increment hs ht,
      bindFree_app _ _ name (depth + increment)
        (InternalBoundShift.preserves_terms s hs cutoff increment)
        (InternalBoundShift.preserves_terms t ht cutoff increment),
      bindFree_app s t name depth hs ht,
      shift_app _ _ cutoff increment
        (InternalBindFree.preserves_terms s hs name depth)
        (InternalBindFree.preserves_terms t ht name depth),
      ihs name depth cutoff increment hc, iht name depth cutoff increment hc]

theorem bindFree_substitute : ∀ t : V, IsTerm t → ∀ name depth cutoff replacement,
    IsTerm replacement → cutoff ≤ depth →
    bindFree (substitute t cutoff replacement) name depth =
      substitute (bindFree t name (depth + 1)) cutoff (bindFree replacement name depth) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ name depth cutoff replacement,
      IsTerm replacement → cutoff ≤ depth →
      bindFree (substitute t cutoff replacement) name depth =
        substitute (bindFree t name (depth + 1)) cutoff (bindFree replacement name depth))
    ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i name depth cutoff replacement _ _
    rcases lt_trichotomy i cutoff with hi | rfl | hi
    · simp [substitute_bvar_lt i cutoff _ hi]
    · simp
    · simp [substitute_bvar_gt i cutoff _ hi]
  · intro i name depth cutoff replacement _ hc
    by_cases hi : i = name
    · subst i
      simp [substitute_bvar_gt (depth + 1) cutoff _ (lt_succ_iff_le.mpr hc)]
    · simp [bindFree_fvar_ne i name _ hi]
  · intro t ht ih name depth cutoff replacement hr hc
    rw [substitute_lam t cutoff replacement ht,
      bindFree_lam _ name depth
        (InternalBoundSubstitution.preserves_terms t ht (cutoff + 1) _
          (InternalBoundShift.preserves_terms replacement hr 0 1)),
      bindFree_lam t name (depth + 1) ht,
      substitute_lam _ cutoff _ (InternalBindFree.preserves_terms t ht name (depth + 1 + 1)),
      ih name (depth + 1) (cutoff + 1) (shift replacement 0 1)
        (InternalBoundShift.preserves_terms replacement hr 0 1) (by simpa [add_comm] using add_le_add_right hc (1 : V)),
      bindFree_shift replacement hr name depth 0 1 (by simp)]
  · intro s t hs ht ihs iht name depth cutoff replacement hr hc
    rw [substitute_app s t cutoff replacement hs ht,
      bindFree_app _ _ name depth
        (InternalBoundSubstitution.preserves_terms s hs cutoff replacement hr)
        (InternalBoundSubstitution.preserves_terms t ht cutoff replacement hr),
      bindFree_app s t name (depth + 1) hs ht,
      substitute_app _ _ cutoff _
        (InternalBindFree.preserves_terms s hs name (depth + 1))
        (InternalBindFree.preserves_terms t ht name (depth + 1)),
      ihs name depth cutoff replacement hr hc, iht name depth cutoff replacement hr hc]

theorem bindFree_beta (body argument name depth : V)
    (hb : IsTerm body) (ha : IsTerm argument) :
    bindFree (beta body argument) name depth =
      beta (bindFree body name (depth + 1)) (bindFree argument name depth) :=
  bindFree_substitute body hb name depth 0 argument ha (by simp)

end FregeanECA.Research.Z2Reverse.InternalBindFree

#print axioms FregeanECA.Research.Z2Reverse.InternalBindFree.bindFree_shift
#print axioms FregeanECA.Research.Z2Reverse.InternalBindFree.bindFree_substitute
#print axioms FregeanECA.Research.Z2Reverse.InternalBindFree.bindFree_beta
