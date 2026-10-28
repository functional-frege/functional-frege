import FregeanECA.Research.Z2Reverse.InternalBoundSubstitution

/-!
Arithmetic absence of a bound-variable index, with the index adjusted under
binders. This supplies the internal side condition for eta reduction and the
inverse of weakening, without quantifying over arbitrary external supports.
-/

namespace FregeanECA.Research.Z2Reverse.InternalAvoidsIndex

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

namespace Recursion

def blueprint : InternalBinderRecursion.Blueprint where
  bvar := .mkSigma “y p i. (i = p ∧ y = 0) ∨ (i ≠ p ∧ y = 1)”
  fvar := .mkSigma “y p i. y = 1”
  app := .mkSigma “y p s t. (s = 1 ∧ t = 1 ∧ y = 1) ∨ ((s ≠ 1 ∨ t ≠ 1) ∧ y = 0)”
  lam := .mkSigma “y p s. y = s”
  change := .mkSigma “q p. q = p + 1”

open Classical in
noncomputable def construction : InternalBinderRecursion.Construction V blueprint where
  bvar p i := if i = p then 0 else 1
  fvar _ _ := 1
  app _ s t := if s = 1 ∧ t = 1 then 1 else 0
  lam _ s := s
  change p := p + 1
  bvar_defined := .mk fun v => by
    by_cases h : v 2 = v 1 <;> simp [blueprint, h]
  fvar_defined := .mk fun v => by simp [blueprint]
  app_defined := .mk fun v => by
    by_cases hs : v 2 = 1 <;> by_cases ht : v 3 = 1 <;> simp [blueprint, hs, ht]
  lam_defined := .mk fun v => by simp [blueprint]
  change_defined := .mk fun v => by simp [blueprint]

end Recursion

noncomputable def check (index term : V) : V := Recursion.construction.result index term

instance check_definable : 𝚺₁-Function₂ (check : V → V → V) :=
  Recursion.construction.result_defined.to_definable

instance check_definable' (Γ m) : Γ-[m + 1]-Function₂ (check : V → V → V) :=
  check_definable.of_sigmaOne

def AvoidsIndex (term index : V) : Prop := IsTerm term ∧ check index term = 1

instance avoids_definable (Γ m) : Γ-[m + 1]-Relation (AvoidsIndex (V := V)) := by
  unfold AvoidsIndex
  definability

theorem AvoidsIndex.term {t index : V} (h : AvoidsIndex t index) : IsTerm t := h.1

@[simp] theorem avoids_bvar_iff (i index : V) :
    AvoidsIndex (bvar i) index ↔ i ≠ index := by
  by_cases h : i = index <;> simp [AvoidsIndex, check, Recursion.construction, h]

@[simp] theorem avoids_fvar (i index : V) : AvoidsIndex (fvar i) index := by
  simp [AvoidsIndex, check, Recursion.construction]

theorem check_app (s t index : V) (hs : IsTerm s) (ht : IsTerm t) :
    check index (app s t) =
      if check index s = 1 ∧ check index t = 1 then 1 else 0 := by
  classical
  exact Recursion.construction.result_app index s t hs ht

theorem check_lam (s index : V) (hs : IsTerm s) :
    check index (lam s) = check (index + 1) s := by
  exact Recursion.construction.result_lam index s hs

@[simp] theorem avoids_app_iff (s t index : V) :
    AvoidsIndex (app s t) index ↔ AvoidsIndex s index ∧ AvoidsIndex t index := by
  by_cases hs : IsTerm s <;> by_cases ht : IsTerm t
  · simp only [AvoidsIndex, isTerm_app_iff, hs, ht, true_and, check_app s t index hs ht]
    split <;> simp_all
  all_goals simp [AvoidsIndex, hs, ht]

@[simp] theorem avoids_lam_iff (s index : V) :
    AvoidsIndex (lam s) index ↔ AvoidsIndex s (index + 1) := by
  by_cases hs : IsTerm s
  · simp [AvoidsIndex, hs, check_lam s index hs]
  · simp [AvoidsIndex, hs]

/-- Weakening inserts an index which does not occur in the resulting term. -/
theorem shift_avoids : ∀ t : V, IsTerm t → ∀ cutoff,
    AvoidsIndex (shift t cutoff 1) cutoff := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff, AvoidsIndex (shift t cutoff 1) cutoff) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff
    by_cases h : i < cutoff
    · rw [shift_bvar_lt i cutoff 1 h, avoids_bvar_iff]
      exact ne_of_lt h
    · have hge : cutoff ≤ i := not_lt.mp h
      rw [shift_bvar_ge i cutoff 1 hge, avoids_bvar_iff]
      exact ne_of_gt (lt_succ_iff_le.mpr hge)
  · intro i cutoff; simp
  · intro s hs ih cutoff
    simpa [shift_lam s cutoff 1 hs] using ih (cutoff + 1)
  · intro s t hs ht ihs iht cutoff
    simpa [shift_app s t cutoff 1 hs ht] using And.intro (ihs cutoff) (iht cutoff)

/-- Removing an absent index and inserting it again recovers the term. -/
theorem shift_substitute_of_avoids : ∀ t : V, IsTerm t → ∀ cutoff replacement,
    IsTerm replacement → AvoidsIndex t cutoff →
    shift (substitute t cutoff replacement) cutoff 1 = t := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff replacement, IsTerm replacement → AvoidsIndex t cutoff →
      shift (substitute t cutoff replacement) cutoff 1 = t) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff replacement _ h
    have hne : i ≠ cutoff := (avoids_bvar_iff i cutoff).mp h
    rcases lt_or_gt_of_ne hne with hi | hi
    · rw [substitute_bvar_lt i cutoff replacement hi, shift_bvar_lt i cutoff 1 hi]
    · rw [substitute_bvar_gt i cutoff replacement hi,
        shift_bvar_ge (i - 1) cutoff 1 (le_sub_one_of_lt hi)]
      have hpos : 1 ≤ i := one_le_of_zero_lt i (lt_of_le_of_lt (by simp) hi)
      simp [tsub_add_cancel_of_le hpos]
  · intro i cutoff replacement _ _; simp
  · intro s hs ih cutoff replacement hr h
    have hsr := InternalBoundShift.preserves_terms replacement hr 0 1
    rw [substitute_lam s cutoff replacement hs,
      shift_lam _ cutoff 1 (InternalBoundSubstitution.preserves_terms s hs (cutoff + 1) _ hsr),
      ih (cutoff + 1) _ hsr ((avoids_lam_iff s cutoff).mp h)]
  · intro s t hs ht ihs iht cutoff replacement hr h
    obtain ⟨hs', ht'⟩ := (avoids_app_iff s t cutoff).mp h
    rw [substitute_app s t cutoff replacement hs ht,
      shift_app _ _ cutoff 1 (InternalBoundSubstitution.preserves_terms s hs cutoff replacement hr)
        (InternalBoundSubstitution.preserves_terms t ht cutoff replacement hr),
      ihs cutoff replacement hr hs', iht cutoff replacement hr ht']

theorem avoids_iff_shift (t cutoff : V) :
    AvoidsIndex t cutoff ↔ ∃ s, IsTerm s ∧ t = shift s cutoff 1 := by
  constructor
  · intro h
    refine ⟨substitute t cutoff (fvar 0),
      InternalBoundSubstitution.preserves_terms t h.term cutoff (fvar 0) (by simp), ?_⟩
    exact (shift_substitute_of_avoids t h.term cutoff (fvar 0) (by simp) h).symm
  · rintro ⟨s, hs, rfl⟩
    exact shift_avoids s hs cutoff

/-- Absence is transported with an index at or above the weakening cutoff. -/
theorem avoids_shift_above : ∀ t : V, IsTerm t → ∀ cutoff index increment,
    cutoff ≤ index →
    (AvoidsIndex (shift t cutoff increment) (index + increment) ↔ AvoidsIndex t index) := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff index increment, cutoff ≤ index →
      (AvoidsIndex (shift t cutoff increment) (index + increment) ↔ AvoidsIndex t index))
    ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff index increment hci
    by_cases hi : i < cutoff
    · have hix : i < index := lt_of_lt_of_le hi hci
      have hix' : i < index + increment := lt_of_lt_of_le hix (by simp)
      simp [shift_bvar_lt i cutoff increment hi, ne_of_lt hix, ne_of_lt hix']
    · rw [shift_bvar_ge i cutoff increment (not_lt.mp hi), avoids_bvar_iff, avoids_bvar_iff]
      simp
  · intro i cutoff index increment _; simp
  · intro s hs ih cutoff index increment hci
    rw [shift_lam s cutoff increment hs, avoids_lam_iff, avoids_lam_iff]
    have hci' : cutoff + 1 ≤ index + 1 := by
      simpa [add_comm] using add_le_add_right hci (1 : V)
    simpa [add_assoc, add_comm, add_left_comm] using ih (cutoff + 1) (index + 1) increment hci'
  · intro s t hs ht ihs iht cutoff index increment hci
    rw [shift_app s t cutoff increment hs ht, avoids_app_iff, avoids_app_iff,
      ihs cutoff index increment hci, iht cutoff index increment hci]

theorem avoids_shift_zero_one (t index : V) (ht : IsTerm t) :
    AvoidsIndex (shift t 0 1) (index + 1) ↔ AvoidsIndex t index :=
  avoids_shift_above t ht 0 index 1 (by simp)

theorem shift_one_injective (s t cutoff : V) (hs : IsTerm s) (ht : IsTerm t)
    (h : shift s cutoff 1 = shift t cutoff 1) : s = t := by
  have same := congrArg (fun u => substitute u cutoff (fvar 0)) h
  simpa [substitute_shift s hs cutoff (fvar 0), substitute_shift t ht cutoff (fvar 0)] using same

/-- Removing a lower binder transports absence down by one. -/
theorem avoids_substitute_of_le : ∀ t : V, IsTerm t → ∀ cutoff index replacement,
    cutoff ≤ index → AvoidsIndex t (index + 1) → AvoidsIndex replacement index →
    AvoidsIndex (substitute t cutoff replacement) index := by
  refine InternalLambdaCode.induction 𝚷
    (P := fun t => ∀ cutoff index replacement, cutoff ≤ index →
      AvoidsIndex t (index + 1) → AvoidsIndex replacement index →
      AvoidsIndex (substitute t cutoff replacement) index) ?_ ?_ ?_ ?_ ?_
  · definability
  · intro i cutoff index replacement hci ht hr
    have hne : i ≠ index + 1 := (avoids_bvar_iff i (index + 1)).mp ht
    rcases lt_trichotomy i cutoff with hi | rfl | hi
    · rw [substitute_bvar_lt i cutoff replacement hi, avoids_bvar_iff]
      exact ne_of_lt (lt_of_lt_of_le hi hci)
    · simpa using hr
    · rw [substitute_bvar_gt i cutoff replacement hi, avoids_bvar_iff]
      intro heq
      have hpos : 1 ≤ i := one_le_of_zero_lt i (lt_of_le_of_lt (by simp) hi)
      have hback : i - 1 + 1 = i := tsub_add_cancel_of_le hpos
      apply hne
      rw [heq] at hback
      exact hback.symm
  · intro i cutoff index replacement _ _ _; simp
  · intro s hs ih cutoff index replacement hci ht hr
    rw [substitute_lam s cutoff replacement hs, avoids_lam_iff]
    have hci' : cutoff + 1 ≤ index + 1 := by
      simpa [add_comm] using add_le_add_right hci (1 : V)
    exact ih (cutoff + 1) (index + 1) _ hci'
      ((avoids_lam_iff s (index + 1)).mp ht)
      ((avoids_shift_zero_one replacement index hr.term).mpr hr)
  · intro s t hs ht ihs iht cutoff index replacement hci h hr
    obtain ⟨hs', ht'⟩ := (avoids_app_iff s t (index + 1)).mp h
    rw [substitute_app s t cutoff replacement hs ht, avoids_app_iff]
    exact ⟨ihs cutoff index replacement hci hs' hr, iht cutoff index replacement hci ht' hr⟩

theorem avoids_beta (body argument index : V)
    (hb : AvoidsIndex body (index + 1)) (ha : AvoidsIndex argument index) :
    AvoidsIndex (beta body argument) index :=
  avoids_substitute_of_le body hb.term 0 index argument (by simp) hb ha

end FregeanECA.Research.Z2Reverse.InternalAvoidsIndex

#print axioms FregeanECA.Research.Z2Reverse.InternalAvoidsIndex.shift_avoids
#print axioms FregeanECA.Research.Z2Reverse.InternalAvoidsIndex.shift_substitute_of_avoids
#print axioms FregeanECA.Research.Z2Reverse.InternalAvoidsIndex.avoids_iff_shift
