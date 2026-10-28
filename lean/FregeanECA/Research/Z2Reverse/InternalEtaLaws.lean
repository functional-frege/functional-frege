import FregeanECA.Research.Z2Reverse.InternalEtaReduction

/-! Structural laws for internally coded eta reduction. -/
namespace FregeanECA.Research.Z2Reverse.InternalEtaReduction
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open InternalAvoidsIndex
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem shift_expansion (t cutoff increment : V) (ht : IsTerm t) :
    shift (expansion t) cutoff increment = expansion (shift t cutoff increment) := by
  have hw := InternalBoundShift.preserves_terms t ht 0 1
  unfold expansion
  rw [shift_lam _ cutoff increment (by simp [hw]),
    shift_app _ _ (cutoff + 1) increment hw (by simp),
    shift_bvar_lt 0 (cutoff + 1) increment (by simp)]
  rw [InternalBoundShift.shift_interchange t ht 0 cutoff 1 increment (by simp)]

theorem substitute_expansion (t cutoff replacement : V) (ht : IsTerm t)
    (hr : IsTerm replacement) :
    substitute (expansion t) cutoff replacement = expansion (substitute t cutoff replacement) := by
  have hw := InternalBoundShift.preserves_terms t ht 0 1
  unfold expansion
  rw [substitute_lam _ cutoff replacement (by simp [hw]),
    substitute_app _ _ (cutoff + 1) (shift replacement 0 1) hw (by simp),
    substitute_bvar_lt 0 (cutoff + 1) (shift replacement 0 1) (by simp)]
  rw [← shift_substitute_of_le t ht 0 cutoff replacement 1 (by simp) hr]

theorem step_shift {n s t : V} (h : Step n s t) (cutoff increment : V) :
    Step (n + increment) (shift s cutoff increment) (shift t cutoff increment) := by
  have all : ∀ n s t : V, Step n s t → ∀ cutoff increment,
      Step (n + increment) (shift s cutoff increment) (shift t cutoff increment) := by
    apply step_induction (P := fun n s t => ∀ cutoff increment,
      Step (n + increment) (shift s cutoff increment) (shift t cutoff increment))
    · apply Language.Definable.all
      apply Language.Definable.all
      apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
      definability
    · intro n u hu cutoff increment
      rw [shift_expansion u cutoff increment hu.term]
      exact Step.eta (InternalBoundShift.preserves_scope u hu.term n cutoff increment hu)
    · intro n a b q h ih hq cutoff increment
      rw [shift_app a q cutoff increment h.scopes.1.term hq.term,
        shift_app b q cutoff increment h.scopes.2.term hq.term]
      exact (ih cutoff increment).app_left (InternalBoundShift.preserves_scope q hq.term n cutoff increment hq)
    · intro n a b q h ih hq cutoff increment
      rw [shift_app q a cutoff increment hq.term h.scopes.1.term,
        shift_app q b cutoff increment hq.term h.scopes.2.term]
      exact (ih cutoff increment).app_right (InternalBoundShift.preserves_scope q hq.term n cutoff increment hq)
    · intro n a b h ih cutoff increment
      rw [shift_lam a cutoff increment h.scopes.1.term,
        shift_lam b cutoff increment h.scopes.2.term]
      apply Step.lam
      simpa [add_assoc, add_comm, add_left_comm] using ih (cutoff + 1) increment
  exact all n s t h cutoff increment

theorem step_substitute {n s t replacement : V} (h : Step (n + 1) s t)
    (hr : IsScoped n replacement) (cutoff : V) (hc : cutoff ≤ n) :
    Step n (substitute s cutoff replacement) (substitute t cutoff replacement) := by
  have all : ∀ d s t : V, Step d s t → ∀ n cutoff replacement,
      d = n + 1 → cutoff ≤ n → IsScoped n replacement →
        Step n (substitute s cutoff replacement) (substitute t cutoff replacement) := by
    apply step_induction (P := fun d s t => ∀ n cutoff replacement,
      d = n + 1 → cutoff ≤ n → IsScoped n replacement →
        Step n (substitute s cutoff replacement) (substitute t cutoff replacement))
    · apply Language.Definable.all
      apply Language.Definable.all
      apply Language.Definable.all
      apply Language.Definable.imp
      · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
      · apply Language.Definable.imp
        · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
        · apply Language.Definable.imp
          · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
          · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
    · intro d u hu n cutoff r eq hc hr
      subst d
      rw [substitute_expansion u cutoff r hu.term hr.term]
      exact Step.eta (InternalBoundSubstitution.preserves_scope u hu.term n cutoff r hc hr hu)
    · intro d a b q h ih hq n cutoff r eq hc hr
      subst d
      rw [substitute_app a q cutoff r h.scopes.1.term hq.term,
        substitute_app b q cutoff r h.scopes.2.term hq.term]
      exact (ih n cutoff r rfl hc hr).app_left
        (InternalBoundSubstitution.preserves_scope q hq.term n cutoff r hc hr hq)
    · intro d a b q h ih hq n cutoff r eq hc hr
      subst d
      rw [substitute_app q a cutoff r hq.term h.scopes.1.term,
        substitute_app q b cutoff r hq.term h.scopes.2.term]
      exact (ih n cutoff r rfl hc hr).app_right
        (InternalBoundSubstitution.preserves_scope q hq.term n cutoff r hc hr hq)
    · intro d a b h ih n cutoff r eq hc hr
      subst d
      rw [substitute_lam a cutoff r h.scopes.1.term,
        substitute_lam b cutoff r h.scopes.2.term]
      apply Step.lam
      exact ih (n + 1) (cutoff + 1) _ rfl
        (by simpa [add_comm] using add_le_add_right hc (1 : V))
        (InternalBoundShift.preserves_scope r hr.term n 0 1 hr)
  exact all (n + 1) s t h n cutoff replacement rfl hc hr

theorem step_avoids {n s t : V} (h : Step n s t) (index : V)
    (hs : AvoidsIndex s index) : AvoidsIndex t index := by
  have all : ∀ n s t : V, Step n s t → ∀ index,
      AvoidsIndex s index → AvoidsIndex t index := by
    apply step_induction (P := fun _ s t => ∀ index, AvoidsIndex s index → AvoidsIndex t index)
    · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚷₁)
      definability
    · intro n u hu index h
      have hb := (avoids_lam_iff _ _).mp h
      have hw := ((avoids_app_iff _ _ _).mp hb).1
      exact (avoids_shift_zero_one u index hu.term).mp hw
    · intro n a b q h ih hq index hs
      obtain ⟨ha, hq⟩ := (avoids_app_iff _ _ _).mp hs
      exact (avoids_app_iff _ _ _).mpr ⟨ih index ha, hq⟩
    · intro n a b q h ih hq index hs
      obtain ⟨hq, ha⟩ := (avoids_app_iff _ _ _).mp hs
      exact (avoids_app_iff _ _ _).mpr ⟨hq, ih index ha⟩
    · intro n a b h ih index hs
      exact (avoids_lam_iff _ _).mpr (ih (index + 1) ((avoids_lam_iff _ _).mp hs))
  exact all n s t h index hs

/-- A reduction of a weakened term is itself a weakened reduction. -/
theorem step_unshift {n s t : V} (hs : IsScoped n s)
    (h : Step (n + 1) (shift s 0 1) t) :
    ∃ u, Step n s u ∧ t = shift u 0 1 := by
  have ht := step_avoids h 0 (shift_avoids s hs.term 0)
  have reduced := step_substitute h (isScoped_fvar n 0) 0 (by simp)
  rw [substitute_shift s hs.term 0 (fvar 0)] at reduced
  exact ⟨_, reduced, (shift_substitute_of_avoids t h.scopes.2.term 0 (fvar 0) (by simp) ht).symm⟩

theorem no_step_bvar (n i t : V) : ¬ Step n (bvar i) t := by
  intro h
  rcases step_cases h with ⟨u, _, eq, _⟩ | ⟨a, b, q, _, eq, _⟩ |
    ⟨a, b, q, _, eq, _⟩ | ⟨a, b, eq, _⟩
  · exact bvar_ne_lam _ _ eq
  · exact bvar_ne_app _ _ _ eq
  · exact bvar_ne_app _ _ _ eq
  · exact bvar_ne_lam _ _ eq

theorem no_step_fvar (n i t : V) : ¬ Step n (fvar i) t := by
  intro h
  rcases step_cases h with ⟨u, _, eq, _⟩ | ⟨a, b, q, _, eq, _⟩ |
    ⟨a, b, q, _, eq, _⟩ | ⟨a, b, eq, _⟩
  · exact fvar_ne_lam _ _ eq
  · exact fvar_ne_app _ _ _ eq
  · exact fvar_ne_app _ _ _ eq
  · exact fvar_ne_lam _ _ eq

theorem step_app_inv {n a b t : V} (h : Step n (app a b) t) :
    (∃ a', t = app a' b ∧ Step n a a') ∨ (∃ b', t = app a b' ∧ Step n b b') := by
  rcases step_cases h with ⟨u, _, eq, _⟩ | ⟨s, t, q, _, eq, out, step⟩ |
    ⟨s, t, q, _, eq, out, step⟩ | ⟨s, t, eq, _⟩
  · exact False.elim (lam_ne_app _ _ _ eq.symm)
  · obtain ⟨rfl, rfl⟩ := (app_inj _ _ _ _).mp eq
    exact Or.inl ⟨t, out, step⟩
  · obtain ⟨rfl, rfl⟩ := (app_inj _ _ _ _).mp eq
    exact Or.inr ⟨t, out, step⟩
  · exact False.elim (lam_ne_app _ _ _ eq.symm)

theorem step_lam_inv {n s t : V} (h : Step n (lam s) t) :
    (∃ u, IsScoped n u ∧ s = app (shift u 0 1) (bvar 0) ∧ t = u) ∨
    (∃ u, t = lam u ∧ Step (n + 1) s u) := by
  rcases step_cases h with ⟨u, hu, eq, out⟩ | ⟨a, b, q, _, eq, _⟩ |
    ⟨a, b, q, _, eq, _⟩ | ⟨a, b, eq, out, step⟩
  · exact Or.inl ⟨u, hu, (lam_inj _ _).mp eq, out⟩
  · exact False.elim (lam_ne_app _ _ _ eq)
  · exact False.elim (lam_ne_app _ _ _ eq)
  · have same := (lam_inj _ _).mp eq
    subst a
    exact Or.inr ⟨b, out, step⟩

end FregeanECA.Research.Z2Reverse.InternalEtaReduction
