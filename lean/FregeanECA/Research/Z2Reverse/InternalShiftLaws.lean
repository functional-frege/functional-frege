import FregeanECA.Research.Z2Reverse.InternalBoundShift

/-! Algebra of internal binder shifts, proved using definable term induction. -/

namespace FregeanECA.Research.Z2Reverse.InternalBoundShift

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shift_interchange : ∀ t : V, IsTerm t → ∀ lower upper first second,
    lower ≤ upper →
    shift (shift t lower first) (upper + first) second =
      shift (shift t upper second) lower first := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ lower upper first second, lower ≤ upper →
      shift (shift t lower first) (upper + first) second =
        shift (shift t upper second) lower first) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i lower upper first second hle
    by_cases hl : i < lower
    · have hu : i < upper := lt_of_lt_of_le hl hle
      have hu' : i < upper + first := lt_of_lt_of_le hu (by simp)
      rw [shift_bvar_lt i lower first hl, shift_bvar_lt i (upper + first) second hu',
        shift_bvar_lt i upper second hu, shift_bvar_lt i lower first hl]
    · have hl' : lower ≤ i := not_lt.mp hl
      by_cases hu : i < upper
      · have hu' : i + first < upper + first := by
          simpa [add_comm] using add_lt_add_right hu first
        rw [shift_bvar_ge i lower first hl',
          shift_bvar_lt (i + first) (upper + first) second hu',
          shift_bvar_lt i upper second hu, shift_bvar_ge i lower first hl']
      · have hu' : upper ≤ i := not_lt.mp hu
        have hua : upper + first ≤ i + first := by
          simpa [add_comm] using add_le_add_right hu' first
        have hlb : lower ≤ i + second := le_trans hl' (by simp)
        rw [shift_bvar_ge i lower first hl',
          shift_bvar_ge (i + first) (upper + first) second hua,
          shift_bvar_ge i upper second hu', shift_bvar_ge (i + second) lower first hlb]
        simp [add_comm, add_left_comm]
  · intro i lower upper first second _; simp
  · intro s hs ih lower upper first second hle
    rw [shift_lam s lower first hs,
      shift_lam _ (upper + first) second (preserves_terms s hs (lower + 1) first),
      shift_lam s upper second hs,
      shift_lam _ lower first (preserves_terms s hs (upper + 1) second)]
    have hle' : lower + 1 ≤ upper + 1 := by
      simpa [add_comm] using add_le_add_right hle (1 : V)
    have h := ih (lower + 1) (upper + 1) first second hle'
    simpa [add_assoc, add_comm, add_left_comm] using congrArg lam h
  · intro s t hs ht ihs iht lower upper first second hle
    rw [shift_app s t lower first hs ht,
      shift_app _ _ (upper + first) second (preserves_terms s hs lower first)
        (preserves_terms t ht lower first),
      shift_app s t upper second hs ht,
      shift_app _ _ lower first (preserves_terms s hs upper second)
        (preserves_terms t ht upper second),
      ihs lower upper first second hle, iht lower upper first second hle]

end FregeanECA.Research.Z2Reverse.InternalBoundShift
