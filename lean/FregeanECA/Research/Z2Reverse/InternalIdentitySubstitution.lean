import FregeanECA.Research.Z2Reverse.InternalBoundSubstitution

/-! Removing a binder after shifting strictly above it, while substituting
that same variable, is the identity. This is the outer eta / inner beta overlap
identity, for arbitrary internally coded terms rather than external syntax. -/

namespace FregeanECA.Research.Z2Reverse.InternalBoundSubstitution

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem substitute_shift_above : ∀ t : V, IsTerm t → ∀ cutoff,
    substitute (shift t (cutoff + 1) 1) cutoff (bvar cutoff) = t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff,
      substitute (shift t (cutoff + 1) 1) cutoff (bvar cutoff) = t) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff
    rcases lt_trichotomy i cutoff with hi | rfl | hi
    · have hi' : i < cutoff + 1 := lt_of_lt_of_le hi (by simp)
      rw [shift_bvar_lt i (cutoff + 1) 1 hi', substitute_bvar_lt i cutoff (bvar cutoff) hi]
    · rw [shift_bvar_lt i (i + 1) 1 (by simp), substitute_bvar_eq]
    · have hge : cutoff + 1 ≤ i := succ_le_iff_lt.mpr hi
      have hgt : cutoff < i + 1 := lt_of_lt_of_le hi (by simp)
      rw [shift_bvar_ge i (cutoff + 1) 1 hge,
        substitute_bvar_gt (i + 1) cutoff (bvar cutoff) hgt]
      simp
  · intro i cutoff; simp
  · intro s hs ih cutoff
    rw [shift_lam s (cutoff + 1) 1 hs,
      substitute_lam _ cutoff (bvar cutoff)
        (InternalBoundShift.preserves_terms s hs ((cutoff + 1) + 1) 1),
      shift_bvar_ge cutoff 0 1 (by simp), ih (cutoff + 1)]
  · intro s t hs ht ihs iht cutoff
    rw [shift_app s t (cutoff + 1) 1 hs ht,
      substitute_app _ _ cutoff (bvar cutoff)
        (InternalBoundShift.preserves_terms s hs (cutoff + 1) 1)
        (InternalBoundShift.preserves_terms t ht (cutoff + 1) 1),
      ihs cutoff, iht cutoff]

theorem beta_shift_one_identity (t : V) (ht : IsTerm t) :
    beta (shift t 1 1) (bvar 0) = t := by
  simpa [beta] using substitute_shift_above t ht 0

end FregeanECA.Research.Z2Reverse.InternalBoundSubstitution

#print axioms FregeanECA.Research.Z2Reverse.InternalBoundSubstitution.substitute_shift_above
#print axioms FregeanECA.Research.Z2Reverse.InternalBoundSubstitution.beta_shift_one_identity
