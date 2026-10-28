import FregeanECA.Research.Z2Reverse.InternalEtaLaws
import FregeanECA.Research.Z2Reverse.InternalPaths

/-! Context and substitution transport for model-valued eta paths. -/

namespace FregeanECA.Research.Z2Reverse.InternalEtaReduction
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open InternalPaths InternalPAInduction
open scoped FFL.FirstOrder
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

local instance step_firstOrder : Language.DefinableRel₃ ℒₒᵣ (Step (V := V)) :=
  definable_of_hierarchy step_definable
local instance scoped_firstOrder : Language.DefinableRel ℒₒᵣ (IsScoped (V := V)) :=
  definable_of_hierarchy scoped_definable
local instance len_firstOrder : Language.DefinableFunction₁ ℒₒᵣ (len : V → V) :=
  definable_of_hierarchy len_definable
local instance nth_firstOrder : Language.DefinableFunction₂ ℒₒᵣ (nth : V → V → V) :=
  definable_of_hierarchy nth_definable
local instance lam_firstOrder : Language.DefinableFunction₁ ℒₒᵣ (lam : V → V) :=
  definable_of_hierarchy lam_definable
local instance app_firstOrder : Language.DefinableFunction₂ ℒₒᵣ (app : V → V → V) :=
  definable_of_hierarchy app_definable
local instance shift_firstOrder : Language.DefinableFunction₃ ℒₒᵣ (shift : V → V → V → V) :=
  definable_of_hierarchy shift_definable
local instance substitute_firstOrder : Language.DefinableFunction₃ ℒₒᵣ (substitute : V → V → V → V) :=
  definable_of_hierarchy substitution_definable

def Steps (n : V) : V → V → Prop := Reach (Step n)

instance steps_firstOrder : Language.DefinableRel₃ ℒₒᵣ (Steps (V := V)) := by
  unfold Steps Reach InternalPaths.Certificate
  definability

theorem step_firstOrder_at (n : V) : Language.DefinableRel ℒₒᵣ (Step n) := by definability
theorem steps_firstOrder_at (n : V) : Language.DefinableRel ℒₒᵣ (Steps n) := by definability

theorem Steps.refl (n t : V) : Steps n t t := reach_refl _ _
theorem Steps.single {n s t : V} (h : Step n s t) : Steps n s t := reach_single h
theorem Steps.trans {n s t u : V} (h : Steps n s t) (g : Steps n t u) : Steps n s u :=
  reach_trans _ (step_firstOrder_at n) h g

theorem Steps.scoped {n s t : V} (h : Steps n s t) (hs : IsScoped n s) : IsScoped n t := by
  have hP : Language.DefinableRel ℒₒᵣ (fun s t : V => IsScoped n s → IsScoped n t) := by definability
  exact reach_induction (Step n) (step_firstOrder_at n) hP (fun _ h => h)
    (fun _ _ _ edge ih _ => ih edge.scopes.2) s t h hs

/-- Mapping a coded path is justified by definable path induction. -/
theorem map_reach (R S : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    (hS : Language.DefinableRel ℒₒᵣ S) (f : V → V)
    (hf : Language.DefinableFunction₁ ℒₒᵣ f)
    (edge : ∀ x y, R x y → S (f x) (f y)) :
    ∀ x y, Reach R x y → Reach S (f x) (f y) := by
  let := reach_definable S hS
  let := hf
  have hP : Language.DefinableRel ℒₒᵣ (fun x y : V => Reach S (f x) (f y)) := by definability
  refine reach_induction R hR hP (fun x => reach_refl S (f x)) ?_
  intro x y z h ih
  exact reach_trans S hS (reach_single (edge x y h)) ih

theorem Steps.lam {n s t : V} (h : Steps (n + 1) s t) : Steps n (lam s) (lam t) :=
  map_reach (Step (n + 1)) (Step n) (step_firstOrder_at _) (step_firstOrder_at _) InternalLambdaCode.lam lam_firstOrder
    (fun _ _ h => h.lam) _ _ h

theorem Steps.app_left {n s t q : V} (h : Steps n s t) (hq : IsScoped n q) :
    Steps n (app s q) (app t q) :=
  map_reach _ _ (step_firstOrder_at _) (step_firstOrder_at _) (fun s => app s q)
    (by definability) (fun _ _ h => h.app_left hq) _ _ h

theorem Steps.app_right {n s t q : V} (h : Steps n s t) (hq : IsScoped n q) :
    Steps n (app q s) (app q t) :=
  map_reach _ _ (step_firstOrder_at _) (step_firstOrder_at _) (fun s => app q s)
    (by definability) (fun _ _ h => h.app_right hq) _ _ h

theorem steps_shift {n s t : V} (h : Steps n s t) (cutoff increment : V) :
    Steps (n + increment) (shift s cutoff increment) (shift t cutoff increment) :=
  map_reach _ _ (step_firstOrder_at _) (step_firstOrder_at _) (fun s => shift s cutoff increment)
    (by definability) (fun _ _ h => step_shift h cutoff increment) _ _ h

theorem steps_substitute {n s t r : V} (h : Steps (n + 1) s t)
    (hr : IsScoped n r) (cutoff : V) (hc : cutoff ≤ n) :
    Steps n (substitute s cutoff r) (substitute t cutoff r) :=
  map_reach _ _ (step_firstOrder_at _) (step_firstOrder_at _) (fun s => substitute s cutoff r)
    (by definability) (fun _ _ h => step_substitute h hr cutoff hc) _ _ h

/-- An internally finite eta path in the replacement induces an internally
finite path after substitution, even when a nonstandard body duplicates it. -/
theorem steps_substitute_replacement {n body r r' : V} (hb : IsScoped (n + 1) body)
    (hr : IsScoped n r) (path : Steps n r r') (cutoff : V) (hc : cutoff ≤ n) :
    Steps n (substitute body cutoff r) (substitute body cutoff r') := by
  have all : ∀ d body : V, IsScoped d body → ∀ n cutoff r r',
      d = n + 1 → cutoff ≤ n → IsScoped n r → Steps n r r' →
        Steps n (substitute body cutoff r) (substitute body cutoff r') := by
    apply InternalPAInduction.scoped_induction (P := fun d body => ∀ n cutoff r r',
      d = n + 1 → cutoff ≤ n → IsScoped n r → Steps n r r' →
        Steps n (substitute body cutoff r) (substitute body cutoff r'))
    · definability
    · intro d i hi n cutoff r r' eq hc hr path
      rcases lt_trichotomy i cutoff with hi | rfl | hi
      · rw [substitute_bvar_lt i cutoff r hi, substitute_bvar_lt i cutoff r' hi]
        exact Steps.refl _ _
      · simpa only [substitute_bvar_eq] using path
      · rw [substitute_bvar_gt i cutoff r hi, substitute_bvar_gt i cutoff r' hi]
        exact Steps.refl _ _
    · intro d i n cutoff r r' eq hc hr path
      simp only [substitute_fvar]
      exact Steps.refl _ _
    · intro d s hs ih n cutoff r r' eq hc hr path
      subst d
      rw [substitute_lam s cutoff r hs.term, substitute_lam s cutoff r' hs.term]
      apply Steps.lam
      exact ih (n + 1) (cutoff + 1) _ _ rfl
        (by simpa [add_comm] using add_le_add_right hc (1 : V))
        (InternalBoundShift.preserves_scope r hr.term n 0 1 hr) (steps_shift path 0 1)
    · intro d s t hs ht ihs iht n cutoff r r' eq hc hr path
      subst d
      rw [substitute_app s t cutoff r hs.term ht.term,
        substitute_app s t cutoff r' hs.term ht.term]
      have hr' := path.scoped hr
      exact ((ihs n cutoff r r' rfl hc hr path).app_left
        (InternalBoundSubstitution.preserves_scope t ht.term n cutoff r hc hr ht)).trans
        ((iht n cutoff r r' rfl hc hr path).app_right
          (InternalBoundSubstitution.preserves_scope s hs.term n cutoff r' hc hr' hs))
  exact all (n + 1) body hb n cutoff r r' rfl hc hr path

end FregeanECA.Research.Z2Reverse.InternalEtaReduction
