import FregeanECA.Research.Z2Reverse.InternalParallelBetaConfluence
import FregeanECA.Research.Z2Reverse.InternalEtaPaths
import FregeanECA.Research.Z2Reverse.InternalIdentitySubstitution
import FregeanECA.Research.Z2Reverse.InternalCommutationLift

/-! Mixed parallel-beta / eta forks on internally coded lambda terms. -/

namespace FregeanECA.Research.Z2Reverse.InternalBetaEtaCommutation
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open InternalAvoidsIndex InternalParallelBeta
open InternalEtaReduction (Step Steps expansion)
open scoped FFL.FirstOrder
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem parallel_avoids {n s t : V} (h : Parallel n s t) (index : V)
    (hs : AvoidsIndex s index) : AvoidsIndex t index := by
  have all : ∀ n s t : V, Parallel n s t → ∀ index,
      AvoidsIndex s index → AvoidsIndex t index := by
    apply parallel_induction_pa (P := fun _ s t => ∀ index, AvoidsIndex s index → AvoidsIndex t index)
    · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚷₁)
      definability
    · intro n i hi index h; exact h
    · intro n i index h; exact h
    · intro n a a' b b' ha hb iha ihb index h
      obtain ⟨ha, hb⟩ := (avoids_app_iff _ _ _).mp h
      exact (avoids_app_iff _ _ _).mpr ⟨iha index ha, ihb index hb⟩
    · intro n a a' ha ih index h
      exact (avoids_lam_iff _ _).mpr (ih (index + 1) ((avoids_lam_iff _ _).mp h))
    · intro n a a' b b' ha hb iha ihb index h
      obtain ⟨hbody, harg⟩ := (avoids_app_iff _ _ _).mp h
      exact avoids_beta a' b' index
        (iha (index + 1) ((avoids_lam_iff _ _).mp hbody)) (ihb index harg)
  exact all n s t h index hs

/-- A parallel reduct of a weakened term can be decoded at the original
binder depth. The cutoff, like the certificate, belongs to the model. -/
theorem parallel_unshift {n s t : V} (hs : IsScoped n s) (cutoff : V) (hc : cutoff ≤ n)
    (h : Parallel (n + 1) (shift s cutoff 1) t) :
    ∃ u, Parallel n s u ∧ t = shift u cutoff 1 := by
  have avoids := parallel_avoids h cutoff (shift_avoids s hs.term cutoff)
  have reduced := parallel_substitute h (Parallel.fvar n 0) cutoff hc
  rw [substitute_shift s hs.term cutoff (fvar 0)] at reduced
  exact ⟨_, reduced,
    (shift_substitute_of_avoids t h.scopes.2.term cutoff (fvar 0) (by simp) avoids).symm⟩

theorem parallel_bvar_inv {n i t : V} (h : Parallel n (bvar i) t) : t = bvar i := by
  rcases parallel_cases h with ⟨j, _, eq, out⟩ | ⟨j, eq, _⟩ |
    ⟨a, a', b, b', eq, _⟩ | ⟨a, a', eq, _⟩ | ⟨a, a', b, b', eq, _⟩
  · exact out.trans eq.symm
  · exact False.elim (bvar_ne_fvar i j eq)
  · exact False.elim (bvar_ne_app i a b eq)
  · exact False.elim (bvar_ne_lam i a eq)
  · exact False.elim (bvar_ne_app i (lam a) b eq)

theorem shift_lam_inv (t body cutoff : V) (ht : IsTerm t) (eq : shift t cutoff 1 = lam body) :
    ∃ original, t = lam original ∧ body = shift original (cutoff + 1) 1 := by
  rcases (InternalLambdaCode.case_iff t).mp ht with
    ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨s, hs, rfl⟩ | ⟨s, u, hs, hu, rfl⟩
  · by_cases hi : i < cutoff
    · rw [shift_bvar_lt i cutoff 1 hi] at eq
      exact False.elim (bvar_ne_lam _ _ eq)
    · rw [shift_bvar_ge i cutoff 1 (not_lt.mp hi)] at eq
      exact False.elim (bvar_ne_lam _ _ eq)
  · rw [shift_fvar] at eq
    exact False.elim (fvar_ne_lam _ _ eq)
  · rw [shift_lam s cutoff 1 hs] at eq
    exact ⟨s, rfl, ((lam_inj _ _).mp eq).symm⟩
  · rw [shift_app s u cutoff 1 hs hu] at eq
    exact False.elim (lam_ne_app _ _ _ eq.symm)

/-- The two ways parallel beta can reduce the body of an eta expansion. -/
theorem parallel_eta_body {n u body : V} (hu : IsScoped n u)
    (h : Parallel (n + 1) (app (shift u 0 1) (bvar 0)) body) :
    (∃ v, Parallel n u v ∧ body = app (shift v 0 1) (bvar 0)) ∨
    (∃ a a', u = lam a ∧ Parallel (n + 1) a a' ∧ body = a') := by
  rcases parallel_cases h with ⟨i, _, eq, _⟩ | ⟨i, eq, _⟩ |
    ⟨a, a', b, b', eq, out, ha, hb⟩ | ⟨a, a', eq, _⟩ |
    ⟨a, a', b, b', eq, out, ha, hb⟩
  · exact False.elim (bvar_ne_app _ _ _ eq.symm)
  · exact False.elim (fvar_ne_app _ _ _ eq.symm)
  · obtain ⟨rfl, rfl⟩ := (app_inj _ _ _ _).mp eq
    have same := parallel_bvar_inv hb
    subst b'
    obtain ⟨v, hv, rfl⟩ := parallel_unshift hu 0 (by simp) ha
    exact Or.inl ⟨v, hv, out⟩
  · exact False.elim (lam_ne_app _ _ _ eq.symm)
  · obtain ⟨shape, rfl⟩ := (app_inj _ _ _ _).mp eq
    have same := parallel_bvar_inv hb
    subst b'
    obtain ⟨original, rfl, shapeBody⟩ := shift_lam_inv u a 0 hu.term shape
    have originalScope := (isScoped_lam_iff _ _).mp hu
    simp only [zero_add] at shapeBody
    subst a
    obtain ⟨reduced, hred, shapeReduced⟩ := parallel_unshift originalScope 1 (by simp) ha
    rw [shapeReduced, beta_shift_one_identity reduced hred.scopes.2.term] at out
    exact Or.inr ⟨original, reduced, rfl, hred, out⟩

theorem parallel_outer_eta {n u t : V} (hu : IsScoped n u)
    (h : Parallel n (expansion u) t) : ∃ common, Steps n t common ∧ Parallel n u common := by
  obtain ⟨body, rfl, inside⟩ := parallel_lam_inv h
  rcases parallel_eta_body hu inside with ⟨v, hv, rfl⟩ | ⟨a, a', rfl, ha, rfl⟩
  · exact ⟨v, InternalEtaReduction.Steps.single (Step.eta hv.scopes.2), hv⟩
  · exact ⟨_, InternalEtaReduction.Steps.refl _ _, ha.lam⟩

theorem beta_eta_body (u argument : V) (hu : IsTerm u) (_ha : IsTerm argument) :
    beta (app (shift u 0 1) (bvar 0)) argument = app u argument := by
  unfold beta
  rw [substitute_app _ _ 0 argument (InternalBoundShift.preserves_terms u hu 0 1) (by simp),
    substitute_shift u hu 0 argument, substitute_bvar_eq]

theorem parallel_apply_eta_body {n u body argument argument' : V} (hu : IsScoped n u)
    (hbody : Parallel (n + 1) (app (shift u 0 1) (bvar 0)) body)
    (harg : Parallel n argument argument') : Parallel n (app u argument) (beta body argument') := by
  rcases parallel_eta_body hu hbody with ⟨v, hv, rfl⟩ | ⟨a, a', rfl, ha, rfl⟩
  · rw [beta_eta_body v argument' hv.scopes.2.term harg.scopes.2.term]
    exact hv.app harg
  · exact ha.beta harg

local instance parallel_firstOrder : Language.DefinableRel₃ ℒₒᵣ (Parallel (V := V)) :=
  InternalPAInduction.definable_of_hierarchy parallel_definable
local instance eta_firstOrder : Language.DefinableRel₃ ℒₒᵣ (Step (V := V)) :=
  InternalPAInduction.definable_of_hierarchy InternalEtaReduction.step_definable

/-- A parallel-beta/eta fork joins by an internal eta path after beta and
one parallel-beta reduction after eta. -/
theorem mixed_fork {n s left right : V} (hb : Parallel n s left) (he : Step n s right) :
    ∃ common, Steps n left common ∧ Parallel n right common := by
  have all : ∀ n s t : V, Parallel n s t → ∀ u, Step n s u →
      ∃ common, Steps n t common ∧ Parallel n u common := by
    apply parallel_induction_pa (P := fun n s t => ∀ u, Step n s u →
      ∃ common, Steps n t common ∧ Parallel n u common)
    · definability
    · intro n i hi u h
      exact False.elim (InternalEtaReduction.no_step_bvar n i u h)
    · intro n i u h
      exact False.elim (InternalEtaReduction.no_step_fvar n i u h)
    · intro n a a' b b' ha hb iha ihb u he
      rcases InternalEtaReduction.step_app_inv he with ⟨a'', rfl, heLeft⟩ | ⟨b'', rfl, heRight⟩
      · obtain ⟨common, fromBeta, fromEta⟩ := iha a'' heLeft
        exact ⟨app common b', fromBeta.app_left hb.scopes.2, fromEta.app hb⟩
      · obtain ⟨common, fromBeta, fromEta⟩ := ihb b'' heRight
        exact ⟨app a' common, fromBeta.app_right ha.scopes.2, ha.app fromEta⟩
    · intro n a a' ha ih u he
      rcases InternalEtaReduction.step_lam_inv he with ⟨v, hv, shape, rfl⟩ | ⟨a'', rfl, heBody⟩
      · subst a
        exact parallel_outer_eta hv ha.lam
      · obtain ⟨common, fromBeta, fromEta⟩ := ih a'' heBody
        exact ⟨lam common, fromBeta.lam, fromEta.lam⟩
    · intro n a a' b b' ha hb iha ihb u he
      rcases InternalEtaReduction.step_app_inv he with ⟨function, rfl, heFunction⟩ | ⟨argument, rfl, heArgument⟩
      · rcases InternalEtaReduction.step_lam_inv heFunction with ⟨v, hv, shape, rfl⟩ | ⟨body, rfl, heBody⟩
        · subst a
          exact ⟨beta a' b', InternalEtaReduction.Steps.refl _ _, parallel_apply_eta_body hv ha hb⟩
        · obtain ⟨common, fromBeta, fromEta⟩ := iha body heBody
          exact ⟨beta common b', InternalEtaReduction.steps_substitute fromBeta hb.scopes.2 0 (by simp),
            fromEta.beta hb⟩
      · obtain ⟨common, fromBeta, fromEta⟩ := ihb argument heArgument
        exact ⟨beta a' common,
          InternalEtaReduction.steps_substitute_replacement ha.scopes.2 hb.scopes.2 fromBeta 0 (by simp),
          ha.beta fromEta⟩
  exact all n s left hb right he

/-- The two relations commute on internally finite paths, including
nonstandard path lengths. No confluence premise is used here. -/
theorem commute (n : V) : InternalCombinedConfluence.Commute (Parallel n) (Step n) := by
  apply InternalCommutationLift.commute_of_strongFork
    (Parallel n) (Step n) (by definability) (InternalEtaReduction.step_firstOrder_at n)
  intro x y z hb he
  exact mixed_fork hb he

end FregeanECA.Research.Z2Reverse.InternalBetaEtaCommutation
