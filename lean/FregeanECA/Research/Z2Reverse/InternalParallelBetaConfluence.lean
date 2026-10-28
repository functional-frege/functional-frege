import FregeanECA.Research.Z2Reverse.InternalParallelBeta
import FregeanECA.Research.Z2Reverse.InternalSubstitutionLaws
import FregeanECA.Research.Z2Reverse.InternalCompleteDevelopment

/-! Preservation and diamond proofs for internally certified parallel beta.
All inductions require first-order definability and run over source-model
numbers; there is no external inductive reduction relation in the proof. -/

namespace FregeanECA.Research.Z2Reverse.InternalParallelBeta
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open InternalCompleteDevelopment
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Eliminate numeric certificates into any first-order definable relation
preserved by the five rules. This is derived from certificate induction. -/
theorem parallel_induction_pa {P : V → V → V → Prop}
    (hP : Language.DefinableRel₃ ℒₒᵣ P)
    (hb : ∀ n i, i < n → P n (bvar i) (bvar i))
    (hf : ∀ n i, P n (fvar i) (fvar i))
    (ha : ∀ n a a' b b', Parallel n a a' → Parallel n b b' →
      P n a a' → P n b b' → P n (app a b) (app a' b'))
    (hl : ∀ n a a', Parallel (n + 1) a a' → P (n + 1) a a' → P n (lam a) (lam a'))
    (hβ : ∀ n a a' b b', Parallel (n + 1) a a' → Parallel n b b' →
      P (n + 1) a a' → P n b b' → P n (app (lam a) b) (beta a' b')) :
    ∀ n s t, Parallel n s t → P n s t := by
  have hmeta : Language.DefinablePred ℒₒᵣ (fun d : V => P (depth d) (source d) (target d)) := by
    let := hP
    apply Language.DefinableRel₃.comp
    all_goals
      apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
      definability
  have all : ∀ d : V, Certificate d → P (depth d) (source d) (target d) := by
    apply certificate_induction_pa hmeta
    intro C ih d h
    obtain ⟨n, _, s, _, t, _, r, _, p, _, q, _, rfl, scopeS, _, step⟩ := h
    simp only [depth_node, source_node, target_node]
    rcases step with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, hp, hq, dp, dq, rfl, rfl⟩ | ⟨_, hp, dp, rfl, rfl⟩ |
      ⟨_, hp, hq, dp, dq, rfl, rfl⟩
    · exact hb n p ((isScoped_bvar_iff n p).mp scopeS)
    · exact hf n p
    · exact ha n _ _ _ _ ⟨p, (ih p hp).1, dp, rfl, rfl⟩ ⟨q, (ih q hq).1, dq, rfl, rfl⟩
        (by simpa only [dp] using (ih p hp).2) (by simpa only [dq] using (ih q hq).2)
    · exact hl n _ _ ⟨p, (ih p hp).1, dp, rfl, rfl⟩
        (by simpa only [dp] using (ih p hp).2)
    · exact hβ n _ _ _ _ ⟨p, (ih p hp).1, dp, rfl, rfl⟩ ⟨q, (ih q hq).1, dq, rfl, rfl⟩
        (by simpa only [dp] using (ih p hp).2) (by simpa only [dq] using (ih q hq).2)
  rintro n s t ⟨d, hd, hn, hs, ht⟩
  simpa only [hn, hs, ht] using all d hd

theorem parallel_lam_inv {n s t : V} (h : Parallel n (lam s) t) :
    ∃ s', t = lam s' ∧ Parallel (n + 1) s s' := by
  rcases parallel_cases h with ⟨i, _, eq, _⟩ | ⟨i, eq, _⟩ |
    ⟨a, a', b, b', eq, _⟩ | ⟨a, a', eq, out, step⟩ | ⟨a, a', b, b', eq, _⟩
  · exact False.elim (bvar_ne_lam i s eq.symm)
  · exact False.elim (fvar_ne_lam i s eq.symm)
  · exact False.elim (lam_ne_app s a b eq)
  · have same := (lam_inj s a).mp eq
    subst a
    exact ⟨a', out, step⟩
  · exact False.elim (lam_ne_app s (lam a) b eq)

theorem parallel_shift {n s t : V} (h : Parallel n s t) (cutoff increment : V) :
    Parallel (n + increment) (shift s cutoff increment) (shift t cutoff increment) := by
  have all : ∀ n s t : V, Parallel n s t → ∀ cutoff increment,
      Parallel (n + increment) (shift s cutoff increment) (shift t cutoff increment) := by
    apply parallel_induction_pa
      (P := fun n s t => ∀ cutoff increment,
        Parallel (n + increment) (shift s cutoff increment) (shift t cutoff increment))
    · apply Language.Definable.all
      apply Language.Definable.all
      apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
      definability
    · intro n i hi cutoff increment
      by_cases hc : i < cutoff
      · rw [shift_bvar_lt i cutoff increment hc]
        exact Parallel.bvar _ _ (lt_of_lt_of_le hi (by simp))
      · rw [shift_bvar_ge i cutoff increment (not_lt.mp hc)]
        exact Parallel.bvar _ _ (by simpa [add_comm] using add_lt_add_right hi increment)
    · intro n i cutoff increment
      simp only [shift_fvar]
      exact Parallel.fvar _ _
    · intro n a a' b b' ha hb iha ihb cutoff increment
      rw [shift_app a b cutoff increment ha.scopes.1.term hb.scopes.1.term,
        shift_app a' b' cutoff increment ha.scopes.2.term hb.scopes.2.term]
      exact (iha cutoff increment).app (ihb cutoff increment)
    · intro n a a' ha ih cutoff increment
      rw [shift_lam a cutoff increment ha.scopes.1.term,
        shift_lam a' cutoff increment ha.scopes.2.term]
      apply Parallel.lam
      simpa [add_assoc, add_comm, add_left_comm] using ih (cutoff + 1) increment
    · intro n a a' b b' ha hb iha ihb cutoff increment
      rw [shift_app (lam a) b cutoff increment (by simpa using ha.scopes.1.term) hb.scopes.1.term,
        shift_lam a cutoff increment ha.scopes.1.term,
        shift_beta a' b' cutoff increment ha.scopes.2.term hb.scopes.2.term]
      apply Parallel.beta _ (ihb cutoff increment)
      simpa [add_assoc, add_comm, add_left_comm] using iha (cutoff + 1) increment
  exact all n s t h cutoff increment

theorem parallel_substitute {n s t r r' : V} (h : Parallel (n + 1) s t)
    (replacement : Parallel n r r') (cutoff : V) (hc : cutoff ≤ n) :
    Parallel n (substitute s cutoff r) (substitute t cutoff r') := by
  have all : ∀ d s t : V, Parallel d s t → ∀ n cutoff r r',
      d = n + 1 → cutoff ≤ n → Parallel n r r' →
        Parallel n (substitute s cutoff r) (substitute t cutoff r') := by
    apply parallel_induction_pa (P := fun d s t => ∀ n cutoff r r',
      d = n + 1 → cutoff ≤ n → Parallel n r r' →
        Parallel n (substitute s cutoff r) (substitute t cutoff r'))
    · apply Language.Definable.all
      apply Language.Definable.all
      apply Language.Definable.all
      apply Language.Definable.all
      apply Language.Definable.imp
      · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
      · apply Language.Definable.imp
        · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
        · apply Language.Definable.imp
          · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
          · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
    · intro d i hi n cutoff r r' eq hc hr
      subst d
      rcases lt_trichotomy i cutoff with hi' | rfl | hi'
      · rw [substitute_bvar_lt i cutoff r hi', substitute_bvar_lt i cutoff r' hi']
        exact Parallel.bvar n i (lt_of_lt_of_le hi' hc)
      · simpa only [substitute_bvar_eq] using hr
      · rw [substitute_bvar_gt i cutoff r hi', substitute_bvar_gt i cutoff r' hi']
        apply Parallel.bvar
        have hpos : 0 < i := lt_of_le_of_lt (by simp) hi'
        exact (tsub_lt_iff_left (one_le_of_zero_lt i hpos)).mpr (by simpa [add_comm] using hi)
    · intro d i n cutoff r r' eq hc hr
      simp only [substitute_fvar]
      exact Parallel.fvar _ _
    · intro d a a' b b' ha hb iha ihb n cutoff r r' eq hc hr
      rw [substitute_app a b cutoff r ha.scopes.1.term hb.scopes.1.term,
        substitute_app a' b' cutoff r' ha.scopes.2.term hb.scopes.2.term]
      exact (iha n cutoff r r' eq hc hr).app (ihb n cutoff r r' eq hc hr)
    · intro d a a' ha ih n cutoff r r' eq hc hr
      subst d
      rw [substitute_lam a cutoff r ha.scopes.1.term,
        substitute_lam a' cutoff r' ha.scopes.2.term]
      apply Parallel.lam
      exact ih (n + 1) (cutoff + 1) _ _ rfl
        (by simpa [add_comm] using add_le_add_right hc (1 : V)) (parallel_shift hr 0 1)
    · intro d a a' b b' ha hb iha ihb n cutoff r r' eq hc hr
      subst d
      rw [substitute_app (lam a) b cutoff r (by simpa using ha.scopes.1.term) hb.scopes.1.term,
        substitute_lam a cutoff r ha.scopes.1.term,
        substitute_beta a' b' cutoff r' ha.scopes.2.term hb.scopes.2.term hr.scopes.2.term]
      apply Parallel.beta _ (ihb n cutoff r r' rfl hc hr)
      exact iha (n + 1) (cutoff + 1) _ _ rfl
        (by simpa [add_comm] using add_le_add_right hc (1 : V)) (parallel_shift hr 0 1)
  exact all (n + 1) s t h n cutoff r r' rfl hc replacement

theorem parallel_lam_iff {n s t : V} : Parallel n (lam s) (lam t) ↔ Parallel (n + 1) s t := by
  constructor
  · intro h
    obtain ⟨u, eq, step⟩ := parallel_lam_inv h
    have same := (lam_inj t u).mp eq
    subst u
    exact step
  · exact Parallel.lam

/-- Every internal parallel reduct continues to the development of its
source. The beta case uses capture-avoiding substitution preservation. -/
theorem continues_to_complete {n s t : V} (h : Parallel n s t) :
    Parallel n t (complete s) := by
  have all : ∀ n s t : V, Parallel n s t → Parallel n t (complete s) := by
    apply parallel_induction_pa (P := fun n s t => Parallel n t (complete s))
    · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
      definability
    · intro n i hi
      simpa only [complete_bvar] using Parallel.bvar n i hi
    · intro n i
      simpa only [complete_fvar] using Parallel.fvar n i
    · intro n a a' b b' ha hb iha ihb
      by_cases hl : IsLam a
      · obtain ⟨body, rfl⟩ := (isLam_iff a).mp hl
        have hbody : IsTerm body := (isTerm_lam_iff body).mp ha.scopes.1.term
        obtain ⟨body', rfl, _⟩ := parallel_lam_inv ha
        have developed : Parallel (n + 1) body' (complete body) :=
          parallel_lam_iff.mp (by simpa only [complete_lam body hbody] using iha)
        rw [complete_app_lam body b hbody hb.scopes.1.term]
        exact developed.beta ihb
      · rw [complete_app_of_not_lam a b ha.scopes.1.term hb.scopes.1.term hl]
        exact iha.app ihb
    · intro n a a' ha ih
      rw [complete_lam a ha.scopes.1.term]
      exact ih.lam
    · intro n a a' b b' ha hb iha ihb
      rw [complete_app_lam a b ha.scopes.1.term hb.scopes.1.term]
      exact parallel_substitute iha ihb 0 (by simp)
  exact all n s t h

/-- Parallel beta has the diamond property on the arithmetic model's own
scoped codes, including its nonstandard terms and derivation certificates. -/
theorem parallel_diamond {n s left right : V}
    (first : Parallel n s left) (second : Parallel n s right) :
    ∃ common : V, Parallel n left common ∧ Parallel n right common :=
  ⟨complete s, continues_to_complete first, continues_to_complete second⟩

theorem parallel_to_complete {n s : V} (hs : IsScoped n s) : Parallel n s (complete s) :=
  continues_to_complete (Parallel.refl n s hs)

end FregeanECA.Research.Z2Reverse.InternalParallelBeta
