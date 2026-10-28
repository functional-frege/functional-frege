import FregeanECA.Research.Z2Reverse.InternalBoundSubstitution
import FregeanECA.Research.Z2Reverse.InternalPAInduction
import Foundation.FirstOrder.Arithmetic.HFS.Fixpoint

/-!
Parallel beta certificates in arbitrary arithmetic models. Certificates,
their subtrees, and the fixedpoint-stage bounds are numbers of the model.
The fixedpoint construction does not use an external inductive relation.
-/

namespace FregeanECA.Research.Z2Reverse.InternalParallelBeta
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open InternalLambdaCode InternalLambdaScope InternalBoundSubstitution
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def node (depth source target rule left right : V) : V :=
  ⟪depth, source, target, rule, left, right⟫ + 1

noncomputable abbrev depth (proof : V) : V := fstIdx proof
noncomputable def source (proof : V) : V := π₁ (sndIdx proof)
noncomputable def target (proof : V) : V := π₁ (π₂ (sndIdx proof))

def nodeFormula : 𝚺₀.Semisentence 7 := .mkSigma
  “d n s t r p q. ∃ x < d, !pair₆Def x n s t r p q ∧ d = x + 1”

instance node_defined : 𝚺₀.DefinedFunction
    (fun v : Fin 6 → V => node (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) nodeFormula :=
  .mk fun v => by simp_all [nodeFormula, node]

def sourceFormula : 𝚺₀.Semisentence 2 := .mkSigma
  “s d. ∃ a <⁺ d, !sndIdxDef a d ∧ !pi₁Def s a”

def targetFormula : 𝚺₀.Semisentence 2 := .mkSigma
  “t d. ∃ a <⁺ d, !sndIdxDef a d ∧ ∃ b <⁺ a, !pi₂Def b a ∧ !pi₁Def t b”

instance source_defined : 𝚺₀-Function₁ (source : V → V) via sourceFormula :=
  .mk fun v => by simp [sourceFormula, source]

instance target_defined : 𝚺₀-Function₁ (target : V → V) via targetFormula :=
  .mk fun v => by simp [targetFormula, target]

instance source_definable (Γ) : Γ-Function₁ (source : V → V) := source_defined.to_definable.of_zero
instance target_definable (Γ) : Γ-Function₁ (target : V → V) := target_defined.to_definable.of_zero

@[simp] theorem depth_node (n s t r p q : V) : depth (node n s t r p q) = n := by
  simp [depth, node, fstIdx]
@[simp] theorem source_node (n s t r p q : V) : source (node n s t r p q) = s := by
  simp [source, node, sndIdx]
@[simp] theorem target_node (n s t r p q : V) : target (node n s t r p q) = t := by
  simp [target, node, sndIdx]

theorem components_lt_node (n s t r p q : V) :
    n < node n s t r p q ∧ s < node n s t r p q ∧ t < node n s t r p q ∧
      r < node n s t r p q ∧ p < node n s t r p q ∧ q < node n s t r p q := by
  have tail₅ : ⟪s, t, r, p, q⟫ ≤ ⟪n, s, t, r, p, q⟫ := le_pair_right _ _
  have tail₄ : ⟪t, r, p, q⟫ ≤ ⟪n, s, t, r, p, q⟫ := le_trans (le_pair_right _ _) tail₅
  have tail₃ : ⟪r, p, q⟫ ≤ ⟪n, s, t, r, p, q⟫ := le_trans (le_pair_right _ _) tail₄
  have tail₂ : ⟪p, q⟫ ≤ ⟪n, s, t, r, p, q⟫ := le_trans (le_pair_right _ _) tail₃
  exact ⟨le_iff_lt_succ.mp (le_pair_left _ _),
    le_iff_lt_succ.mp (le_trans (le_pair_left _ _) tail₅),
    le_iff_lt_succ.mp (le_trans (le_pair_left _ _) tail₄),
    le_iff_lt_succ.mp (le_trans (le_pair_left _ _) tail₃),
    le_iff_lt_succ.mp (le_trans (le_pair_left _ _) tail₂),
    le_iff_lt_succ.mp (le_trans (le_pair_right _ _) tail₂)⟩

/-- Rule tags 0/1 are bound/free variables; 2 is application, 3 abstraction,
and 4 contraction of a root beta redex after parallel premise reductions. -/
def Rule (C : Set V) (n s t r p q : V) : Prop :=
  (r = 0 ∧ s = bvar p ∧ t = s) ∨
  (r = 1 ∧ s = fvar p ∧ t = s) ∨
  (r = 2 ∧ p ∈ C ∧ q ∈ C ∧ depth p = n ∧ depth q = n ∧
    s = app (source p) (source q) ∧ t = app (target p) (target q)) ∨
  (r = 3 ∧ p ∈ C ∧ depth p = n + 1 ∧ s = lam (source p) ∧ t = lam (target p)) ∨
  (r = 4 ∧ p ∈ C ∧ q ∈ C ∧ depth p = n + 1 ∧ depth q = n ∧
    s = app (InternalLambdaCode.lam (source p)) (source q) ∧ t = beta (target p) (target q))

local instance appDelta_defined : 𝚫₁-Function₂ (InternalLambdaCode.app : V → V → V) via appFormula.graphDelta :=
  app_defined.graph_delta
local instance lamDelta_defined : 𝚫₁-Function₁ (InternalLambdaCode.lam : V → V) via lamFormula.graphDelta :=
  lam_defined.graph_delta

noncomputable def ruleFormula : 𝚫₁.Semisentence 7 := .mkDelta
  (.mkSigma “n s t r p q C.
    (r = 0 ∧ !qqBvarDef s p ∧ t = s) ∨
    (r = 1 ∧ !qqFvarDef s p ∧ t = s) ∨
    (r = 2 ∧ p ∈ C ∧ q ∈ C ∧ !fstIdxDef n p ∧ !fstIdxDef n q ∧
      ∃ sp sq tp tq, !sourceFormula sp p ∧ !sourceFormula sq q ∧
      !targetFormula tp p ∧ !targetFormula tq q ∧ !appFormula s sp sq ∧ !appFormula t tp tq) ∨
    (r = 3 ∧ p ∈ C ∧ !fstIdxDef (n + 1) p ∧
      ∃ sp tp, !sourceFormula sp p ∧ !targetFormula tp p ∧ !lamFormula s sp ∧ !lamFormula t tp) ∨
    (r = 4 ∧ p ∈ C ∧ q ∈ C ∧ !fstIdxDef (n + 1) p ∧ !fstIdxDef n q ∧
      ∃ sp sq tp tq l, !sourceFormula sp p ∧ !sourceFormula sq q ∧
      !targetFormula tp p ∧ !targetFormula tq q ∧ !lamFormula l sp ∧
      !appFormula s l sq ∧ !substitutionFormula t tp 0 tq)”)
  (.mkPi “n s t r p q C.
    (r = 0 ∧ !qqBvarDef s p ∧ t = s) ∨
    (r = 1 ∧ !qqFvarDef s p ∧ t = s) ∨
    (r = 2 ∧ p ∈ C ∧ q ∈ C ∧ !fstIdxDef n p ∧ !fstIdxDef n q ∧
      ∀ sp, !sourceFormula sp p → ∀ sq, !sourceFormula sq q →
      ∀ tp, !targetFormula tp p → ∀ tq, !targetFormula tq q → !appFormula.graphDelta.pi s sp sq ∧ !appFormula.graphDelta.pi t tp tq) ∨
    (r = 3 ∧ p ∈ C ∧ !fstIdxDef (n + 1) p ∧
      ∀ sp, !sourceFormula sp p → ∀ tp, !targetFormula tp p → !lamFormula.graphDelta.pi s sp ∧ !lamFormula.graphDelta.pi t tp) ∨
    (r = 4 ∧ p ∈ C ∧ q ∈ C ∧ !fstIdxDef (n + 1) p ∧ !fstIdxDef n q ∧
      ∀ sp, !sourceFormula sp p → ∀ sq, !sourceFormula sq q →
      ∀ tp, !targetFormula tp p → ∀ tq, !targetFormula tq q → ∀ l, !lamFormula l sp →
      !appFormula.graphDelta.pi s l sq ∧ !substitutionFormula.graphDelta.pi t tp 0 tq)”)

instance rule_defined : 𝚫₁.Defined
    (fun v : Fin 7 → V => Rule {x | x ∈ v 6} (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))
    ruleFormula := .mk ⟨by intro v; simp [ruleFormula, eq_comm],
      by intro v; simp [ruleFormula, Rule, bvar, fvar, depth, beta, eq_comm]⟩

theorem Rule.monotone {C C' : Set V} (h : C ⊆ C') {n s t r p q : V}
    (step : Rule C n s t r p q) : Rule C' n s t r p q := by
  rcases step with h₀ | h₁ | ⟨hr, hp, hq, rest⟩ | ⟨hr, hp, rest⟩ | ⟨hr, hp, hq, rest⟩
  · exact Or.inl h₀
  · exact Or.inr (Or.inl h₁)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, h hp, h hq, rest⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, h hp, rest⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, h hp, h hq, rest⟩)))

theorem Rule.restrict {C : Set V} {d n s t r p q : V}
    (hp : p < d) (hq : q < d) (step : Rule C n s t r p q) :
    Rule {x ∈ C | x < d} n s t r p q := by
  rcases step with h₀ | h₁ | ⟨hr, hCp, hCq, rest⟩ | ⟨hr, hCp, rest⟩ | ⟨hr, hCp, hCq, rest⟩
  · exact Or.inl h₀
  · exact Or.inr (Or.inl h₁)
  · exact Or.inr (Or.inr (Or.inl ⟨hr, ⟨hCp, hp⟩, ⟨hCq, hq⟩, rest⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hr, ⟨hCp, hp⟩, rest⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hr, ⟨hCp, hp⟩, ⟨hCq, hq⟩, rest⟩)))

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

def Parallel (n s t : V) : Prop := ∃ proof, CertificateOf proof n s t

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

noncomputable def parallelFormula : 𝚺₁.Semisentence 3 := .mkSigma
  “n s t. ∃ d, !certificateOfFormula.sigma d n s t”

instance parallel_defined : 𝚺₁-Relation₃ (Parallel (V := V)) via parallelFormula :=
  .mk fun v => by simp [parallelFormula, Parallel]

instance parallel_definable : 𝚺₁-Relation₃ (Parallel (V := V)) := parallel_defined.to_definable

instance parallel_definable' : 𝚺-[0 + 1]-Relation₃ (Parallel (V := V)) :=
  parallel_definable

theorem CertificateOf.scopes {d n s t : V} (h : CertificateOf d n s t) :
    IsScoped n s ∧ IsScoped n t := by
  simpa only [h.2.1, h.2.2.1, h.2.2.2] using h.1.scopes

theorem Parallel.scopes {n s t : V} (h : Parallel n s t) : IsScoped n s ∧ IsScoped n t := by
  obtain ⟨d, hd⟩ := h
  exact hd.scopes

theorem node_certificate {n s t r p q : V} (hs : IsScoped n s) (ht : IsScoped n t)
    (step : Rule {d | Certificate d} n s t r p q) :
    CertificateOf (node n s t r p q) n s t := by
  obtain ⟨hn, hs', ht', hr, hp, hq⟩ := components_lt_node n s t r p q
  refine ⟨(certificate_iff _).mpr ?_, by simp, by simp, by simp⟩
  exact ⟨n, hn, s, hs', t, ht', r, hr, p, hp, q, hq, rfl, hs, ht, step⟩

theorem CertificateOf.bvar (n i : V) (hi : i < n) :
    CertificateOf (node n (bvar i) (bvar i) 0 i 0) n (bvar i) (bvar i) := by
  apply node_certificate (by simpa) (by simpa)
  exact Or.inl ⟨rfl, rfl, rfl⟩

theorem CertificateOf.fvar (n i : V) :
    CertificateOf (node n (fvar i) (fvar i) 1 i 0) n (fvar i) (fvar i) := by
  apply node_certificate (by simp) (by simp)
  exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

theorem CertificateOf.app {n s s' t t' p q : V}
    (hp : CertificateOf p n s s') (hq : CertificateOf q n t t') :
    CertificateOf (node n (InternalLambdaCode.app s t) (InternalLambdaCode.app s' t') 2 p q) n (InternalLambdaCode.app s t) (InternalLambdaCode.app s' t') := by
  apply node_certificate
    ((isScoped_app_iff _ _ _).mpr ⟨hp.scopes.1, hq.scopes.1⟩)
    ((isScoped_app_iff _ _ _).mpr ⟨hp.scopes.2, hq.scopes.2⟩)
  exact Or.inr (Or.inr (Or.inl ⟨rfl, hp.1, hq.1, hp.2.1, hq.2.1,
    by simp only [hp.2.2.1, hq.2.2.1], by simp only [hp.2.2.2, hq.2.2.2]⟩))

theorem CertificateOf.lam {n s s' p : V} (hp : CertificateOf p (n + 1) s s') :
    CertificateOf (node n (InternalLambdaCode.lam s) (InternalLambdaCode.lam s') 3 p 0) n (InternalLambdaCode.lam s) (InternalLambdaCode.lam s') := by
  apply node_certificate ((isScoped_lam_iff _ _).mpr hp.scopes.1)
    ((isScoped_lam_iff _ _).mpr hp.scopes.2)
  exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hp.1, hp.2.1,
    by simp only [hp.2.2.1], by simp only [hp.2.2.2]⟩)))

theorem CertificateOf.beta {n s s' t t' p q : V}
    (hp : CertificateOf p (n + 1) s s') (hq : CertificateOf q n t t') :
    CertificateOf (node n (InternalLambdaCode.app (InternalLambdaCode.lam s) t) (InternalBoundSubstitution.beta s' t') 4 p q)
      n (InternalLambdaCode.app (InternalLambdaCode.lam s) t) (InternalBoundSubstitution.beta s' t') := by
  apply node_certificate
    ((isScoped_app_iff _ _ _).mpr ⟨(isScoped_lam_iff _ _).mpr hp.scopes.1, hq.scopes.1⟩)
    (beta_scoped hp.scopes.2 hq.scopes.2)
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hp.1, hq.1, hp.2.1, hq.2.1,
    by simp only [hp.2.2.1, hq.2.2.1], by simp only [hp.2.2.2, hq.2.2.2]⟩)))

theorem Parallel.bvar (n i : V) (hi : i < n) : Parallel n (bvar i) (bvar i) :=
  ⟨_, CertificateOf.bvar n i hi⟩

theorem Parallel.fvar (n i : V) : Parallel n (fvar i) (fvar i) :=
  ⟨_, CertificateOf.fvar n i⟩

theorem Parallel.app {n s s' t t' : V} (hs : Parallel n s s') (ht : Parallel n t t') :
    Parallel n (InternalLambdaCode.app s t) (InternalLambdaCode.app s' t') := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  exact ⟨_, hp.app hq⟩

theorem Parallel.lam {n s s' : V} (hs : Parallel (n + 1) s s') :
    Parallel n (InternalLambdaCode.lam s) (InternalLambdaCode.lam s') := by
  obtain ⟨p, hp⟩ := hs
  exact ⟨_, hp.lam⟩

theorem Parallel.beta {n s s' t t' : V} (hs : Parallel (n + 1) s s') (ht : Parallel n t t') :
    Parallel n (InternalLambdaCode.app (InternalLambdaCode.lam s) t) (InternalBoundSubstitution.beta s' t') := by
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  exact ⟨_, hp.beta hq⟩

/-- Exact elimination into the five parallel-beta rules. All premise depths
and both endpoints are recovered from the numeric child certificates. -/
theorem parallel_cases {n s t : V} (h : Parallel n s t) :
    (∃ i, i < n ∧ s = bvar i ∧ t = bvar i) ∨
    (∃ i, s = fvar i ∧ t = fvar i) ∨
    (∃ a a' b b', s = app a b ∧ t = app a' b' ∧ Parallel n a a' ∧ Parallel n b b') ∨
    (∃ a a', s = lam a ∧ t = lam a' ∧ Parallel (n + 1) a a') ∨
    (∃ a a' b b', s = app (InternalLambdaCode.lam a) b ∧ t = beta a' b' ∧
      Parallel (n + 1) a a' ∧ Parallel n b b') := by
  obtain ⟨d, hd, hn, hs, ht⟩ := h
  obtain ⟨nn, _, ss, _, tt, _, r, _, p, _, q, _, eq, scopeS, _, step⟩ :=
    (certificate_iff d).mp hd
  subst d
  simp only [depth_node, source_node, target_node] at hn hs ht
  subst nn ss tt
  rcases step with ⟨_, eqS, eqT⟩ | ⟨_, eqS, eqT⟩ |
    ⟨_, hp, hq, dp, dq, eqS, eqT⟩ | ⟨_, hp, dp, eqS, eqT⟩ |
    ⟨_, hp, hq, dp, dq, eqS, eqT⟩
  · exact Or.inl ⟨p, (isScoped_bvar_iff n p).mp (eqS ▸ scopeS), eqS, eqT.trans eqS⟩
  · exact Or.inr (Or.inl ⟨p, eqS, eqT.trans eqS⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨source p, target p, source q, target q, eqS, eqT,
      ⟨p, hp, dp, rfl, rfl⟩, ⟨q, hq, dq, rfl, rfl⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨source p, target p, eqS, eqT,
      ⟨p, hp, dp, rfl, rfl⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨source p, target p, source q, target q, eqS, eqT,
      ⟨p, hp, dp, rfl, rfl⟩, ⟨q, hq, dq, rfl, rfl⟩⟩)))

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

theorem Parallel.refl (n t : V) (ht : IsScoped n t) : Parallel n t t := by
  apply InternalPAInduction.scoped_induction (P := fun n t => Parallel n t t) ?_ ?_ ?_ ?_ ?_ n t ht
  · apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
    definability
  · exact Parallel.bvar
  · exact Parallel.fvar
  · intro n s _ hs; exact hs.lam
  · intro n s t _ _ hs ht; exact hs.app ht

end PA

end FregeanECA.Research.Z2Reverse.InternalParallelBeta





