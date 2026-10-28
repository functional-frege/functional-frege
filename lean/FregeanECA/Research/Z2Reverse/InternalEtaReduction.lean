import FregeanECA.Research.Z2Reverse.InternalParallelBeta
import FregeanECA.Research.Z2Reverse.InternalAvoidsIndex
import FregeanECA.Research.Z2Reverse.InternalSubstitutionLaws

/-!
Internally finite eta derivations in arbitrary arithmetic models. Every node,
child certificate, binder depth and fixedpoint stage ranges over the model.
Eta contraction is expressed by explicit weakening, which enforces its usual
fresh-variable side condition without an external syntactic predicate.
-/

namespace FregeanECA.Research.Z2Reverse.InternalEtaReduction
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open InternalParallelBeta (node depth source target nodeFormula sourceFormula targetFormula
  depth_node source_node target_node components_lt_node)
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def expansion (t : V) : V := lam (app (shift t 0 1) (bvar 0))

noncomputable def expansionFormula : 𝚺₁.Semisentence 2 := .mkSigma
  “s t. ∃ u v w, !shiftFormula u t 0 1 ∧ !qqBvarDef v 0 ∧ !appFormula w u v ∧ !lamFormula s w”

instance expansion_defined : 𝚺₁-Function₁ (expansion : V → V) via expansionFormula :=
  .mk fun v => by simp [expansionFormula, expansion, bvar]

instance expansionDelta_defined :
    𝚫₁-Function₁ (expansion : V → V) via expansionFormula.graphDelta :=
  expansion_defined.graph_delta

instance expansion_definable : 𝚫₁-Function₁ (expansion : V → V) :=
  expansionDelta_defined.to_definable

instance expansion_definable' (Γ m) : Γ-[m + 1]-Function₁ (expansion : V → V) :=
  expansion_definable.of_deltaOne

theorem expansion_scoped {n t : V} (ht : IsScoped n t) : IsScoped n (expansion t) := by
  apply (isScoped_lam_iff _ _).mpr
  apply (isScoped_app_iff _ _ _).mpr
  exact ⟨InternalBoundShift.preserves_scope t ht.term n 0 1 ht, by simp⟩

/-- Tags 0,1,2,3 are root eta, left application, right application, lambda. -/
def Rule (C : Set V) (n s t r p q : V) : Prop :=
  (r = 0 ∧ s = expansion p ∧ t = p) ∨
  (r = 1 ∧ p ∈ C ∧ depth p = n ∧ s = app (source p) q ∧ t = app (target p) q) ∨
  (r = 2 ∧ p ∈ C ∧ depth p = n ∧ s = app q (source p) ∧ t = app q (target p)) ∨
  (r = 3 ∧ p ∈ C ∧ depth p = n + 1 ∧ s = lam (source p) ∧ t = lam (target p))

local instance appDelta_defined : 𝚫₁-Function₂ (app : V → V → V) via appFormula.graphDelta :=
  app_defined.graph_delta
local instance lamDelta_defined : 𝚫₁-Function₁ (lam : V → V) via lamFormula.graphDelta :=
  lam_defined.graph_delta

noncomputable def ruleFormula : 𝚫₁.Semisentence 7 := .mkDelta
  (.mkSigma “n s t r p q C.
    (r = 0 ∧ !expansionFormula s p ∧ t = p) ∨
    (r = 1 ∧ p ∈ C ∧ !fstIdxDef n p ∧
      ∃ sp tp, !sourceFormula sp p ∧ !targetFormula tp p ∧ !appFormula s sp q ∧ !appFormula t tp q) ∨
    (r = 2 ∧ p ∈ C ∧ !fstIdxDef n p ∧
      ∃ sp tp, !sourceFormula sp p ∧ !targetFormula tp p ∧ !appFormula s q sp ∧ !appFormula t q tp) ∨
    (r = 3 ∧ p ∈ C ∧ !fstIdxDef (n + 1) p ∧
      ∃ sp tp, !sourceFormula sp p ∧ !targetFormula tp p ∧ !lamFormula s sp ∧ !lamFormula t tp)”)
  (.mkPi “n s t r p q C.
    (r = 0 ∧ !expansionFormula.graphDelta.pi s p ∧ t = p) ∨
    (r = 1 ∧ p ∈ C ∧ !fstIdxDef n p ∧
      ∀ sp, !sourceFormula sp p → ∀ tp, !targetFormula tp p → !appFormula.graphDelta.pi s sp q ∧ !appFormula.graphDelta.pi t tp q) ∨
    (r = 2 ∧ p ∈ C ∧ !fstIdxDef n p ∧
      ∀ sp, !sourceFormula sp p → ∀ tp, !targetFormula tp p → !appFormula.graphDelta.pi s q sp ∧ !appFormula.graphDelta.pi t q tp) ∨
    (r = 3 ∧ p ∈ C ∧ !fstIdxDef (n + 1) p ∧
      ∀ sp, !sourceFormula sp p → ∀ tp, !targetFormula tp p → !lamFormula.graphDelta.pi s sp ∧ !lamFormula.graphDelta.pi t tp)”)

instance rule_defined : 𝚫₁.Defined
    (fun v : Fin 7 → V => Rule {x | x ∈ v 6} (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
    ruleFormula := .mk ⟨by intro v; simp [ruleFormula, eq_comm],
      by intro v; simp [ruleFormula, Rule, depth, eq_comm]⟩

theorem Rule.monotone {C C' : Set V} (h : C ⊆ C') {n s t r p q : V}
    (step : Rule C n s t r p q) : Rule C' n s t r p q := by
  rcases step with h₀ | ⟨hr, hp, rest⟩ | ⟨hr, hp, rest⟩ | ⟨hr, hp, rest⟩
  · exact Or.inl h₀
  · exact Or.inr (Or.inl ⟨hr, h hp, rest⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, h hp, rest⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hr, h hp, rest⟩))

theorem Rule.restrict {C : Set V} {d n s t r p q : V}
    (hp : p < d) (_hq : q < d) (step : Rule C n s t r p q) :
    Rule {x ∈ C | x < d} n s t r p q := by
  rcases step with h₀ | ⟨hr, hCp, rest⟩ | ⟨hr, hCp, rest⟩ | ⟨hr, hCp, rest⟩
  · exact Or.inl h₀
  · exact Or.inr (Or.inl ⟨hr, ⟨hCp, hp⟩, rest⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, ⟨hCp, hp⟩, rest⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hr, ⟨hCp, hp⟩, rest⟩))

def Phi (C : Set V) (d : V) : Prop :=
  ∃ n < d, ∃ s < d, ∃ t < d, ∃ r < d, ∃ p < d, ∃ q < d,
    d = node n s t r p q ∧ IsScoped n s ∧ IsScoped n t ∧ Rule C n s t r p q

noncomputable def blueprint : Fixpoint.Blueprint 0 := ⟨.mkDelta
  (.mkSigma “d C. ∃ n < d, ∃ s < d, ∃ t < d, ∃ r < d, ∃ p < d, ∃ q < d,
    !nodeFormula d n s t r p q ∧ !isScopedFormula.sigma n s ∧ !isScopedFormula.sigma n t ∧
    !ruleFormula.sigma n s t r p q C”)
  (.mkPi “d C. ∃ n < d, ∃ s < d, ∃ t < d, ∃ r < d, ∃ p < d, ∃ q < d,
    !nodeFormula d n s t r p q ∧ !isScopedFormula.pi n s ∧ !isScopedFormula.pi n t ∧
    !ruleFormula.pi n s t r p q C”)⟩

theorem phi_defined : 𝚫₁.Defined
    (fun v : Fin 2 → V => Phi {x | x ∈ v 1} (v 0)) blueprint.core :=
  .mk ⟨by intro v; simp [blueprint], by intro v; simp [blueprint, Phi]⟩

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun _ => Phi
  defined := phi_defined
  monotone := by
    rintro C C' h _ d ⟨n, hn, s, hs, t, ht, r, hr, p, hp, q, hq, eq, scopeS, scopeT, step⟩
    exact ⟨n, hn, s, hs, t, ht, r, hr, p, hp, q, hq, eq, scopeS, scopeT, step.monotone h⟩

instance : (construction (V := V)).StrongFinite where
  strong_finite := by
    rintro C _ d ⟨n, hn, s, hs, t, ht, r, hr, p, hp, q, hq, eq, scopeS, scopeT, step⟩
    exact ⟨n, hn, s, hs, t, ht, r, hr, p, hp, q, hq, eq, scopeS, scopeT, step.restrict hp hq⟩

/-- Internally finite proof trees, obtained by model-valued fixedpoint stages. -/
def Certificate (proof : V) : Prop := construction.Fixpoint ![] proof

noncomputable def certificateFormula : 𝚫₁.Semisentence 1 := blueprint.fixpointDefΔ₁

instance certificate_defined : 𝚫₁-Predicate (Certificate (V := V)) via certificateFormula :=
  construction.fixpoint_definedΔ₁

instance certificate_definable : 𝚫₁-Predicate (Certificate (V := V)) :=
  certificate_defined.to_definable

instance certificate_definable' (Γ m) : Γ-[m + 1]-Predicate (Certificate (V := V)) :=
  certificate_definable.of_deltaOne

theorem certificate_iff (d : V) : Certificate d ↔ Phi {p | Certificate p} d :=
  construction.case

theorem certificate_stage {d : V} (h : Certificate d) :
    ∃ stage : V, d ∈ construction.limSeq ![] stage := h

theorem Certificate.scopes {d : V} (h : Certificate d) :
    IsScoped (depth d) (source d) ∧ IsScoped (depth d) (target d) := by
  obtain ⟨n, _, s, _, t, _, r, _, p, _, q, _, rfl, hs, ht, _⟩ := (certificate_iff d).mp h
  simpa using And.intro hs ht

def CertificateOf (proof n s t : V) : Prop :=
  Certificate proof ∧ depth proof = n ∧ source proof = s ∧ target proof = t

def Step (n s t : V) : Prop := ∃ proof, CertificateOf proof n s t

noncomputable def certificateOfFormula : 𝚫₁.Semisentence 4 := .mkDelta
  (.mkSigma “d n s t. !certificateFormula.sigma d ∧ !fstIdxDef n d ∧ !sourceFormula s d ∧ !targetFormula t d”)
  (.mkPi “d n s t. !certificateFormula.pi d ∧ !fstIdxDef n d ∧ !sourceFormula s d ∧ !targetFormula t d”)

instance certificateOf_defined : 𝚫₁-Relation₄ (CertificateOf (V := V)) via certificateOfFormula :=
  .mk ⟨by intro v; simp [certificateOfFormula],
    by intro v; simp [certificateOfFormula, CertificateOf, depth, eq_comm]⟩

instance certificateOf_definable : 𝚫₁-Relation₄ (CertificateOf (V := V)) :=
  certificateOf_defined.to_definable

instance certificateOf_definable' (Γ m) : Γ-[m + 1]-Relation₄ (CertificateOf (V := V)) :=
  certificateOf_definable.of_deltaOne

noncomputable def stepFormula : 𝚺₁.Semisentence 3 := .mkSigma
  “n s t. ∃ d, !certificateOfFormula.sigma d n s t”

instance step_defined : 𝚺₁-Relation₃ (Step (V := V)) via stepFormula :=
  .mk fun v => by simp [stepFormula, Step]

instance step_definable : 𝚺₁-Relation₃ (Step (V := V)) := step_defined.to_definable

instance step_definable' : 𝚺-[0 + 1]-Relation₃ (Step (V := V)) :=
  step_definable

theorem CertificateOf.scopes {d n s t : V} (h : CertificateOf d n s t) :
    IsScoped n s ∧ IsScoped n t := by
  simpa only [h.2.1, h.2.2.1, h.2.2.2] using h.1.scopes

theorem Step.scopes {n s t : V} (h : Step n s t) : IsScoped n s ∧ IsScoped n t := by
  obtain ⟨d, hd⟩ := h
  exact hd.scopes

theorem node_certificate {n s t r p q : V} (hs : IsScoped n s) (ht : IsScoped n t)
    (step : Rule {d | Certificate d} n s t r p q) :
    CertificateOf (node n s t r p q) n s t := by
  obtain ⟨hn, hs', ht', hr, hp, hq⟩ := components_lt_node n s t r p q
  refine ⟨(certificate_iff _).mpr ?_, by simp, by simp, by simp⟩
  exact ⟨n, hn, s, hs', t, ht', r, hr, p, hp, q, hq, rfl, hs, ht, step⟩

theorem CertificateOf.eta {n t : V} (ht : IsScoped n t) :
    CertificateOf (node n (expansion t) t 0 t 0) n (expansion t) t := by
  apply node_certificate (expansion_scoped ht) ht
  exact Or.inl ⟨rfl, rfl, rfl⟩

theorem CertificateOf.app_left {n s t q p : V}
    (hp : CertificateOf p n s t) (hq : IsScoped n q) :
    CertificateOf (node n (app s q) (app t q) 1 p q) n (app s q) (app t q) := by
  apply node_certificate
    ((isScoped_app_iff _ _ _).mpr ⟨hp.scopes.1, hq⟩)
    ((isScoped_app_iff _ _ _).mpr ⟨hp.scopes.2, hq⟩)
  exact Or.inr (Or.inl ⟨rfl, hp.1, hp.2.1,
    by simp only [hp.2.2.1], by simp only [hp.2.2.2]⟩)

theorem CertificateOf.app_right {n s t q p : V}
    (hp : CertificateOf p n s t) (hq : IsScoped n q) :
    CertificateOf (node n (app q s) (app q t) 2 p q) n (app q s) (app q t) := by
  apply node_certificate
    ((isScoped_app_iff _ _ _).mpr ⟨hq, hp.scopes.1⟩)
    ((isScoped_app_iff _ _ _).mpr ⟨hq, hp.scopes.2⟩)
  exact Or.inr (Or.inr (Or.inl ⟨rfl, hp.1, hp.2.1,
    by simp only [hp.2.2.1], by simp only [hp.2.2.2]⟩))

theorem CertificateOf.lam {n s t p : V} (hp : CertificateOf p (n + 1) s t) :
    CertificateOf (node n (InternalLambdaCode.lam s) (InternalLambdaCode.lam t) 3 p 0)
      n (InternalLambdaCode.lam s) (InternalLambdaCode.lam t) := by
  apply node_certificate ((isScoped_lam_iff _ _).mpr hp.scopes.1)
    ((isScoped_lam_iff _ _).mpr hp.scopes.2)
  exact Or.inr (Or.inr (Or.inr ⟨rfl, hp.1, hp.2.1,
    by simp only [hp.2.2.1], by simp only [hp.2.2.2]⟩))

theorem Step.eta {n t : V} (ht : IsScoped n t) : Step n (expansion t) t :=
  ⟨_, CertificateOf.eta ht⟩

theorem Step.app_left {n s t q : V} (h : Step n s t) (hq : IsScoped n q) :
    Step n (app s q) (app t q) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨_, hp.app_left hq⟩

theorem Step.app_right {n s t q : V} (h : Step n s t) (hq : IsScoped n q) :
    Step n (app q s) (app q t) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨_, hp.app_right hq⟩

theorem Step.lam {n s t : V} (h : Step (n + 1) s t) :
    Step n (InternalLambdaCode.lam s) (InternalLambdaCode.lam t) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨_, hp.lam⟩

/-- Inversion recovers one of the four rules, including scoped context terms. -/
theorem step_cases {n s t : V} (h : Step n s t) :
    (∃ u, IsScoped n u ∧ s = expansion u ∧ t = u) ∨
    (∃ a b q, IsScoped n q ∧ s = app a q ∧ t = app b q ∧ Step n a b) ∨
    (∃ a b q, IsScoped n q ∧ s = app q a ∧ t = app q b ∧ Step n a b) ∨
    (∃ a b, s = lam a ∧ t = lam b ∧ Step (n + 1) a b) := by
  obtain ⟨d, hd, hn, hs, ht⟩ := h
  obtain ⟨nn, _, ss, _, tt, _, r, _, p, _, q, _, eq, scopeS, scopeT, rule⟩ :=
    (certificate_iff d).mp hd
  subst d
  simp only [depth_node, source_node, target_node] at hn hs ht
  subst nn ss tt
  rcases rule with ⟨_, eqS, eqT⟩ | ⟨_, hp, dp, eqS, eqT⟩ |
    ⟨_, hp, dp, eqS, eqT⟩ | ⟨_, hp, dp, eqS, eqT⟩
  · exact Or.inl ⟨p, eqT ▸ scopeT, eqS, eqT⟩
  · exact Or.inr (Or.inl ⟨source p, target p, q,
      ((isScoped_app_iff _ _ _).mp (eqS ▸ scopeS)).2, eqS, eqT,
      ⟨p, hp, dp, rfl, rfl⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨source p, target p, q,
      ((isScoped_app_iff _ _ _).mp (eqS ▸ scopeS)).1, eqS, eqT,
      ⟨p, hp, dp, rfl, rfl⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨source p, target p, eqS, eqT,
      ⟨p, hp, dp, rfl, rfl⟩⟩))

/-- Certificate induction with an explicit arithmetic-hierarchy witness. -/
theorem certificate_induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (step : ∀ C : Set V, (∀ d ∈ C, Certificate d ∧ P d) →
      ∀ d, Phi C d → P d) : ∀ d, Certificate d → P d :=
  construction.induction hP step

section PA
variable [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Full PA permits arbitrary first-order definable certificate properties;
the definability premise cannot be dropped for a nonstandard source model. -/
theorem certificate_induction_pa {P : V → Prop} (hP : Language.DefinablePred ℒₒᵣ P)
    (step : ∀ C : Set V, (∀ d ∈ C, Certificate d ∧ P d) →
      ∀ d, Phi C d → P d) : ∀ d, Certificate d → P d := by
  have hCertificate : Language.DefinablePred ℒₒᵣ (Certificate (V := V)) :=
    InternalPAInduction.definable_of_hierarchy certificate_definable
  refine InternalPAInduction.order_induction
    (P := fun d => Certificate d → P d) (Language.Definable.imp hCertificate hP) ?_
  intro d ih hd
  have restricted :=  Fixpoint.Construction.StrongFinite.strong_finite
    ((construction (V := V)).case.mp hd)
  exact step {e | Certificate e ∧ e < d}
    (fun e he => ⟨he.1, ih e he.2 he.1⟩) d restricted


/-- Rule induction for arbitrary first-order definable properties of both endpoints.
Its induction is over the model-valued certificate, not an external proof tree. -/
theorem step_induction {P : V → V → V → Prop}
    (hP : Language.DefinableRel₃ ℒₒᵣ P)
    (eta : ∀ n u, IsScoped n u → P n (expansion u) u)
    (left : ∀ n a b q, Step n a b → P n a b → IsScoped n q → P n (app a q) (app b q))
    (right : ∀ n a b q, Step n a b → P n a b → IsScoped n q → P n (app q a) (app q b))
    (under : ∀ n a b, Step (n + 1) a b → P (n + 1) a b → P n (lam a) (lam b)) :
    ∀ n s t, Step n s t → P n s t := by
  have hD : Language.DefinableFunction₁ ℒₒᵣ (depth : V → V) :=
    InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁) (by unfold depth; definability)
  have hS : Language.DefinableFunction₁ ℒₒᵣ (source : V → V) :=
    InternalPAInduction.definable_of_hierarchy (InternalParallelBeta.source_definable 𝚺₁)
  have hT : Language.DefinableFunction₁ ℒₒᵣ (target : V → V) :=
    InternalPAInduction.definable_of_hierarchy (InternalParallelBeta.target_definable 𝚺₁)
  have all : ∀ d, Certificate d → P (depth d) (source d) (target d) := by
    apply certificate_induction_pa (P := fun d => P (depth d) (source d) (target d))
      (hP.comp hD hS hT)
    intro C ih d hd
    obtain ⟨n, _, s, _, t, _, r, _, p, _, q, _, rfl, scopeS, scopeT, rule⟩ := hd
    simp only [depth_node, source_node, target_node]
    rcases rule with ⟨_, rfl, rfl⟩ | ⟨_, hp, dp, rfl, rfl⟩ |
      ⟨_, hp, dp, rfl, rfl⟩ | ⟨_, hp, dp, rfl, rfl⟩
    · exact eta n _ scopeT
    · exact left n (source p) (target p) q ⟨p, (ih p hp).1, dp, rfl, rfl⟩
        (dp ▸ (ih p hp).2) ((isScoped_app_iff _ _ _).mp scopeS).2
    · exact right n (source p) (target p) q ⟨p, (ih p hp).1, dp, rfl, rfl⟩
        (dp ▸ (ih p hp).2) ((isScoped_app_iff _ _ _).mp scopeS).1
    · exact under n (source p) (target p) ⟨p, (ih p hp).1, dp, rfl, rfl⟩
        (dp ▸ (ih p hp).2)
  rintro n s t ⟨d, hd, hn, hs, ht⟩
  simpa only [hn, hs, ht] using all d hd

end PA

end FregeanECA.Research.Z2Reverse.InternalEtaReduction

