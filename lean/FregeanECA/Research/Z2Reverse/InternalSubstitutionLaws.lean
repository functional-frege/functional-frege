import FregeanECA.Research.Z2Reverse.InternalBoundSubstitution
import FregeanECA.Research.Z2Reverse.InternalShiftLaws

/-! Internal substitution and renaming identities used by conversion proofs. -/

namespace FregeanECA.Research.Z2Reverse.InternalBoundSubstitution

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shift_substitute_of_le : ∀ t : V, IsTerm t → ∀ lower cutoff replacement increment,
    lower ≤ cutoff → IsTerm replacement →
    shift (substitute t cutoff replacement) lower increment =
      substitute (shift t lower increment) (cutoff + increment)
        (shift replacement lower increment) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ lower cutoff replacement increment,
      lower ≤ cutoff → IsTerm replacement →
      shift (substitute t cutoff replacement) lower increment =
        substitute (shift t lower increment) (cutoff + increment)
          (shift replacement lower increment)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i lower cutoff replacement increment hle _
    rcases lt_trichotomy i cutoff with hi | rfl | hi
    · rw [substitute_bvar_lt i cutoff replacement hi]
      by_cases hl : i < lower
      · have hi' : i < cutoff + increment := lt_of_lt_of_le hi (by simp)
        rw [shift_bvar_lt i lower increment hl,
          substitute_bvar_lt i (cutoff + increment) _ hi']
      · have hl' : lower ≤ i := not_lt.mp hl
        have hi' : i + increment < cutoff + increment := by
          simpa [add_comm] using add_lt_add_right hi increment
        rw [shift_bvar_ge i lower increment hl',
          substitute_bvar_lt (i + increment) (cutoff + increment) _ hi']
    · rw [substitute_bvar_eq, shift_bvar_ge i lower increment hle,
        substitute_bvar_eq]
    · have hl : lower ≤ i := le_trans hle (le_of_lt hi)
      have hl' : lower ≤ i - 1 := le_trans hle (le_sub_one_of_lt hi)
      have hi' : cutoff + increment < i + increment := by
        simpa [add_comm] using add_lt_add_right hi increment
      rw [substitute_bvar_gt i cutoff replacement hi,
        shift_bvar_ge (i - 1) lower increment hl', shift_bvar_ge i lower increment hl,
        substitute_bvar_gt (i + increment) (cutoff + increment) _ hi']
      have hpos : 1 ≤ i := one_le_of_zero_lt i (lt_of_le_of_lt (by simp) hi)
      apply congrArg bvar
      calc
        i - 1 + increment = increment + (i - 1) := add_comm _ _
        _ = increment + i - 1 := (add_sub_of_le hpos increment).symm
        _ = i + increment - 1 := by rw [add_comm increment i]
  · intro i lower cutoff replacement increment _ _; simp
  · intro s hs ih lower cutoff replacement increment hle hr
    have hsr := InternalBoundShift.preserves_terms replacement hr 0 1
    rw [substitute_lam s cutoff replacement hs,
      shift_lam _ lower increment (preserves_terms s hs (cutoff + 1) _ hsr),
      shift_lam s lower increment hs,
      substitute_lam _ (cutoff + increment) _
        (InternalBoundShift.preserves_terms s hs (lower + 1) increment)]
    have hle' : lower + 1 ≤ cutoff + 1 := by
      simpa [add_comm] using add_le_add_right hle (1 : V)
    have h := ih (lower + 1) (cutoff + 1) (shift replacement 0 1) increment hle' hsr
    rw [shift_interchange replacement hr 0 lower 1 increment (by simp)] at h
    simpa [add_assoc, add_comm, add_left_comm] using congrArg lam h
  · intro s t hs ht ihs iht lower cutoff replacement increment hle hr
    rw [substitute_app s t cutoff replacement hs ht,
      shift_app _ _ lower increment (preserves_terms s hs cutoff replacement hr)
        (preserves_terms t ht cutoff replacement hr),
      shift_app s t lower increment hs ht,
      substitute_app _ _ (cutoff + increment) _
        (InternalBoundShift.preserves_terms s hs lower increment)
        (InternalBoundShift.preserves_terms t ht lower increment),
      ihs lower cutoff replacement increment hle hr,
      iht lower cutoff replacement increment hle hr]

/-- Composition of two binder removals, with the original upper index restored. -/
theorem substitute_comp : ∀ t : V, IsTerm t → ∀ lower upper first second,
    lower ≤ upper → IsTerm first → IsTerm second →
    substitute (substitute t lower first) upper second =
      substitute (substitute t (upper + 1) (shift second lower 1)) lower
        (substitute first upper second) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ lower upper first second,
      lower ≤ upper → IsTerm first → IsTerm second →
      substitute (substitute t lower first) upper second =
        substitute (substitute t (upper + 1) (shift second lower 1)) lower
          (substitute first upper second)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i lower upper first second hlu _ hs
    rcases lt_trichotomy i lower with hi | rfl | hi
    · have hiu : i < upper := lt_of_lt_of_le hi hlu
      have hiu' : i < upper + 1 := lt_of_lt_of_le hiu (by simp)
      rw [substitute_bvar_lt i lower first hi, substitute_bvar_lt i upper second hiu,
        substitute_bvar_lt i (upper + 1) _ hiu', substitute_bvar_lt i lower _ hi]
    · have hiu : i < upper + 1 := lt_succ_iff_le.mpr hlu
      rw [substitute_bvar_eq, substitute_bvar_lt i (upper + 1) _ hiu, substitute_bvar_eq]
    · rcases zero_or_succ i with rfl | ⟨p, rfl⟩
      · simp at hi
      · rw [substitute_bvar_gt (p + 1) lower first hi]
        simp only [add_sub_self]
        rcases lt_trichotomy p upper with hp | rfl | hp
        · have hpu : p + 1 < upper + 1 := by
            simpa [add_comm] using add_lt_add_right hp (1 : V)
          rw [substitute_bvar_lt p upper second hp,
            substitute_bvar_lt (p + 1) (upper + 1) _ hpu,
            substitute_bvar_gt (p + 1) lower _ hi]
          simp
        · rw [substitute_bvar_eq, substitute_bvar_eq, substitute_shift second hs lower _]
        · have hpu : upper + 1 < p + 1 := by
            simpa [add_comm] using add_lt_add_right hp (1 : V)
          have hlp : lower < p := lt_of_le_of_lt hlu hp
          rw [substitute_bvar_gt p upper second hp,
            substitute_bvar_gt (p + 1) (upper + 1) _ hpu]
          simp only [add_sub_self]
          rw [substitute_bvar_gt p lower _ hlp]
  · intro i lower upper first second _ _ _; simp
  · intro s hs ih lower upper first second hlu hf hg
    have hsf := InternalBoundShift.preserves_terms first hf 0 1
    have hsg := InternalBoundShift.preserves_terms second hg 0 1
    have hsg' := InternalBoundShift.preserves_terms second hg lower 1
    rw [substitute_lam s lower first hs,
      substitute_lam _ upper second (preserves_terms s hs (lower + 1) _ hsf),
      substitute_lam s (upper + 1) (shift second lower 1) hs,
      substitute_lam _ lower (substitute first upper second)
        (preserves_terms s hs ((upper + 1) + 1) _
          (InternalBoundShift.preserves_terms _ hsg' 0 1))]
    have hlu' : lower + 1 ≤ upper + 1 := by
      simpa [add_comm] using add_le_add_right hlu (1 : V)
    have h := ih (lower + 1) (upper + 1) (shift first 0 1) (shift second 0 1)
      hlu' hsf hsg
    rw [shift_interchange second hg 0 lower 1 1 (by simp)] at h
    rw [shift_substitute_of_le first hf 0 upper second 1 (by simp) hg]
    exact congrArg lam h
  · intro s t hs ht ihs iht lower upper first second hlu hf hg
    have hsg := InternalBoundShift.preserves_terms second hg lower 1
    rw [substitute_app s t lower first hs ht,
      substitute_app _ _ upper second (preserves_terms s hs lower first hf)
        (preserves_terms t ht lower first hf),
      substitute_app s t (upper + 1) (shift second lower 1) hs ht,
      substitute_app _ _ lower (substitute first upper second)
        (preserves_terms s hs (upper + 1) _ hsg)
        (preserves_terms t ht (upper + 1) _ hsg),
      ihs lower upper first second hlu hf hg,
      iht lower upper first second hlu hf hg]

/-- Shift a position above the binder being removed. -/
theorem shift_substitute_above : ∀ t : V, IsTerm t → ∀ cutoff upper replacement increment,
    cutoff ≤ upper → IsTerm replacement →
    shift (substitute t cutoff replacement) upper increment =
      substitute (shift t (upper + 1) increment) cutoff
        (shift replacement upper increment) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff upper replacement increment,
      cutoff ≤ upper → IsTerm replacement →
      shift (substitute t cutoff replacement) upper increment =
        substitute (shift t (upper + 1) increment) cutoff
          (shift replacement upper increment)) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff upper replacement increment hcu _
    rcases lt_trichotomy i cutoff with hi | rfl | hi
    · have hiu : i < upper := lt_of_lt_of_le hi hcu
      have hiu' : i < upper + 1 := lt_of_lt_of_le hiu (by simp)
      rw [substitute_bvar_lt i cutoff replacement hi, shift_bvar_lt i upper increment hiu,
        shift_bvar_lt i (upper + 1) increment hiu', substitute_bvar_lt i cutoff _ hi]
    · have hiu : i < upper + 1 := lt_succ_iff_le.mpr hcu
      rw [substitute_bvar_eq, shift_bvar_lt i (upper + 1) increment hiu, substitute_bvar_eq]
    · rcases zero_or_succ i with rfl | ⟨p, rfl⟩
      · simp at hi
      · rw [substitute_bvar_gt (p + 1) cutoff replacement hi]
        simp only [add_sub_self]
        by_cases hp : p < upper
        · have hpu : p + 1 < upper + 1 := by
            simpa [add_comm] using add_lt_add_right hp (1 : V)
          rw [shift_bvar_lt p upper increment hp, shift_bvar_lt (p + 1) (upper + 1) increment hpu,
            substitute_bvar_gt (p + 1) cutoff _ hi]
          simp
        · have hpu : upper + 1 ≤ p + 1 := by
            simpa [add_comm] using add_le_add_right (not_lt.mp hp) (1 : V)
          have hi' : cutoff < p + 1 + increment := lt_of_lt_of_le hi (by simp)
          rw [shift_bvar_ge p upper increment (not_lt.mp hp),
            shift_bvar_ge (p + 1) (upper + 1) increment hpu,
            substitute_bvar_gt (p + 1 + increment) cutoff _ hi']
          rw [show p + 1 + increment = (p + increment) + 1 by ac_rfl]
          simp
  · intro i cutoff upper replacement increment _ _; simp
  · intro s hs ih cutoff upper replacement increment hcu hr
    have hsr := InternalBoundShift.preserves_terms replacement hr 0 1
    rw [substitute_lam s cutoff replacement hs,
      shift_lam _ upper increment (preserves_terms s hs (cutoff + 1) _ hsr),
      shift_lam s (upper + 1) increment hs,
      substitute_lam _ cutoff _
        (InternalBoundShift.preserves_terms s hs ((upper + 1) + 1) increment)]
    have hcu' : cutoff + 1 ≤ upper + 1 := by
      simpa [add_comm] using add_le_add_right hcu (1 : V)
    have h := ih (cutoff + 1) (upper + 1) (shift replacement 0 1) increment hcu' hsr
    rw [shift_interchange replacement hr 0 upper 1 increment (by simp)] at h
    exact congrArg lam h
  · intro s t hs ht ihs iht cutoff upper replacement increment hcu hr
    rw [substitute_app s t cutoff replacement hs ht,
      shift_app _ _ upper increment (preserves_terms s hs cutoff replacement hr)
        (preserves_terms t ht cutoff replacement hr),
      shift_app s t (upper + 1) increment hs ht,
      substitute_app _ _ cutoff _
        (InternalBoundShift.preserves_terms s hs (upper + 1) increment)
        (InternalBoundShift.preserves_terms t ht (upper + 1) increment),
      ihs cutoff upper replacement increment hcu hr,
      iht cutoff upper replacement increment hcu hr]

theorem substitute_beta (body argument cutoff replacement : V)
    (hb : IsTerm body) (ha : IsTerm argument) (hr : IsTerm replacement) :
    substitute (beta body argument) cutoff replacement =
      beta (substitute body (cutoff + 1) (shift replacement 0 1))
        (substitute argument cutoff replacement) :=
  substitute_comp body hb 0 cutoff argument replacement (by simp) ha hr

theorem shift_beta (body argument cutoff increment : V)
    (hb : IsTerm body) (ha : IsTerm argument) :
    shift (beta body argument) cutoff increment =
      beta (shift body (cutoff + 1) increment) (shift argument cutoff increment) :=
  shift_substitute_above body hb 0 cutoff argument increment (by simp) ha

end FregeanECA.Research.Z2Reverse.InternalBoundSubstitution
