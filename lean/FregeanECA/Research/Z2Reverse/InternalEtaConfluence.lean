import FregeanECA.Research.Z2Reverse.InternalEtaLaws
import FregeanECA.Research.Z2Reverse.InternalConfluence

/-!
Strong confluence and Church-Rosser for internally coded eta reduction.
The critical overlap is resolved by the checked unshift theorem. Both the
rule induction and the subsequent path inductions range over model numbers.
-/
namespace FregeanECA.Research.Z2Reverse.InternalEtaReduction
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalAvoidsIndex
open InternalPaths
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- At most one eta step. Equality is not counted as a contraction. -/
def Optional (n s t : V) : Prop := Step n s t ∨ s = t

instance optional_definable : 𝚺₁-Relation₃ (Optional (V := V)) := by
  unfold Optional
  definability

theorem Optional.refl (n s : V) : Optional n s s := Or.inr rfl

theorem Optional.app_left {n s t q : V} (h : Optional n s t) (hq : IsScoped n q) :
    Optional n (app s q) (app t q) := by
  rcases h with h | rfl
  · exact Or.inl (h.app_left hq)
  · exact Or.inr rfl

theorem Optional.app_right {n s t q : V} (h : Optional n s t) (hq : IsScoped n q) :
    Optional n (app q s) (app q t) := by
  rcases h with h | rfl
  · exact Or.inl (h.app_right hq)
  · exact Or.inr rfl

theorem Optional.lam {n s t : V} (h : Optional (n + 1) s t) :
    Optional n (InternalLambdaCode.lam s) (InternalLambdaCode.lam t) := by
  rcases h with h | rfl
  · exact Or.inl h.lam
  · exact Or.inr rfl

/-- Resolve an arbitrary eta contraction against the outermost contraction. -/
theorem outer_overlap {n u t : V} (hu : IsScoped n u) (h : Step n (expansion u) t) :
    ∃ common, Optional n u common ∧ Optional n t common := by
  rcases step_lam_inv h with ⟨v, hv, eq, rfl⟩ | ⟨body, rfl, hbody⟩
  · have same := (app_inj _ _ _ _).mp eq
    have uv := shift_one_injective u t 0 hu.term hv.term same.1
    subst t
    exact ⟨u, Optional.refl _ _, Optional.refl _ _⟩
  · rcases step_app_inv hbody with ⟨w, rfl, hw⟩ | ⟨w, rfl, hw⟩
    · obtain ⟨v, hv, rfl⟩ := step_unshift hu hw
      exact ⟨v, Or.inl hv, Or.inl (Step.eta hv.scopes.2)⟩
    · exact False.elim (no_step_bvar _ _ _ hw)

/-- Every one-step fork joins by at most one step on either side. -/
theorem step_diamond {n s left right : V} (first : Step n s left) (second : Step n s right) :
    ∃ common, Optional n left common ∧ Optional n right common := by
  have all : ∀ n s left : V, Step n s left → ∀ right, Step n s right →
      ∃ common, Optional n left common ∧ Optional n right common := by
    apply step_induction (P := fun n s left => ∀ right, Step n s right →
      ∃ common, Optional n left common ∧ Optional n right common)
    · apply Language.Definable.all
      apply Language.Definable.imp
      · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
      · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁); definability
    · intro n u hu right second
      exact outer_overlap hu second
    · intro n a b q hab ih hq right second
      rcases step_app_inv second with ⟨a', rfl, ha'⟩ | ⟨q', rfl, hq'⟩
      · obtain ⟨c, hc, hc'⟩ := ih a' ha'
        exact ⟨app c q, hc.app_left hq, hc'.app_left hq⟩
      · exact ⟨app b q', Or.inl (hq'.app_right hab.scopes.2),
          Or.inl (hab.app_left hq'.scopes.2)⟩
    · intro n a b q hab ih hq right second
      rcases step_app_inv second with ⟨q', rfl, hq'⟩ | ⟨a', rfl, ha'⟩
      · exact ⟨app q' b, Or.inl (hq'.app_left hab.scopes.2),
          Or.inl (hab.app_right hq'.scopes.2)⟩
      · obtain ⟨c, hc, hc'⟩ := ih a' ha'
        exact ⟨app q c, hc.app_right hq, hc'.app_right hq⟩
    · intro n a b hab ih right second
      rcases step_lam_inv second with ⟨u, hu, rfl, rfl⟩ | ⟨a', rfl, ha'⟩
      · obtain ⟨c, hc, hc'⟩ := outer_overlap hu hab.lam
        exact ⟨c, hc', hc⟩
      · obtain ⟨c, hc, hc'⟩ := ih a' ha'
        exact ⟨lam c, hc.lam, hc'.lam⟩
  exact all n s left first right second

theorem optional_diamond (n : V) : InternalConfluence.Diamond (Optional n) := by
  intro source left right first second
  rcases first with first | rfl
  · rcases second with second | rfl
    · exact step_diamond first second
    · exact ⟨left, Optional.refl _ _, Or.inl first⟩
  · exact ⟨right, second, Optional.refl _ _⟩

theorem step_fo_definable (n : V) : Language.DefinableRel ℒₒᵣ (Step n) := by
  apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
  definability

theorem optional_fo_definable (n : V) : Language.DefinableRel ℒₒᵣ (Optional n) := by
  apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
  definability

/-- Optional steps do not alter internally coded reachability. -/
theorem reach_optional_iff (n s t : V) : Reach (Optional n) s t ↔ Reach (Step n) s t := by
  constructor
  · apply reach_induction (Optional n) (optional_fo_definable n)
      (reach_definable (Step n) (step_fo_definable n)) (reach_refl (Step n))
    intro x y z edge path
    rcases edge with edge | rfl
    · exact reach_trans (Step n) (step_fo_definable n) (reach_single edge) path
    · exact path
  · exact reach_mono (fun _ _ h => Or.inl h)

/-- Confluence for eta paths, including paths of nonstandard model length. -/
theorem eta_confluent {n s left right : V}
    (first : Reach (Step n) s left) (second : Reach (Step n) s right) :
    ∃ common, Reach (Step n) left common ∧ Reach (Step n) right common := by
  obtain ⟨common, fromLeft, fromRight⟩ := InternalConfluence.reach_confluent
    (Optional n) (optional_fo_definable n) (optional_diamond n)
    s left ((reach_optional_iff n s left).mpr first)
    right ((reach_optional_iff n s right).mpr second)
  exact ⟨common, (reach_optional_iff n left common).mp fromLeft,
    (reach_optional_iff n right common).mp fromRight⟩

/-- An internally finite eta conversion has a common eta reduct. -/
theorem eta_church_rosser {n left right : V} (h : Convert (Step n) left right) :
    ∃ common, Reach (Step n) left common ∧ Reach (Step n) right common := by
  have lifted : Convert (Optional n) left right :=
    reach_mono (fun _ _ h => h.elim (fun h => Or.inl (Or.inl h))
      (fun h => Or.inr (Or.inl h))) h
  obtain ⟨common, fromLeft, fromRight⟩ := InternalConfluence.convert_has_common_reduct
    (Optional n) (optional_fo_definable n) (optional_diamond n) left right lifted
  exact ⟨common, (reach_optional_iff n left common).mp fromLeft,
    (reach_optional_iff n right common).mp fromRight⟩

theorem normal_forms_convert_iff {n left right : V}
    (leftNormal : InternalConfluence.Normal (Step n) left)
    (rightNormal : InternalConfluence.Normal (Step n) right) :
    Convert (Step n) left right ↔ left = right := by
  constructor
  · intro h
    obtain ⟨common, hl, hr⟩ := eta_church_rosser h
    exact (InternalConfluence.normal_reach_eq leftNormal hl).trans
      (InternalConfluence.normal_reach_eq rightNormal hr).symm
  · rintro rfl
    exact convert_refl _ _

end FregeanECA.Research.Z2Reverse.InternalEtaReduction

