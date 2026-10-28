import FregeanECA.Research.Z2Reverse.InternalPAInduction

/-!
Internally finite paths in arbitrary PA models.

A certificate is a Foundation-coded vector of vertices. Both its code and its
length belong to the arithmetic model, so nonstandard lengths are included.
Reachability is first-order definable when the edge relation is. No external
inductive transitive closure, external list of vertices, or standardness
assumption is used.
-/

namespace FregeanECA.Research.Z2Reverse.InternalPaths

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalPAInduction
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

local instance len_firstOrder : Language.DefinableFunction₁ ℒₒᵣ (len : V → V) :=
  definable_of_hierarchy len_definable

local instance nth_firstOrder : Language.DefinableFunction₂ ℒₒᵣ (nth : V → V → V) :=
  definable_of_hierarchy nth_definable

local instance adjoin_firstOrder :
    Language.DefinableFunction₂ ℒₒᵣ (adjoin : V → V → V) :=
  definable_of_hierarchy adjoin_definable

/-- A vector of `n + 1` vertices certifies `n` edges, for an internal `n : V`. -/
def Certificate (R : V → V → Prop) (code start finish : V) : Prop :=
  ∃ n : V, len code = n + 1 ∧ code.[0] = start ∧ code.[n] = finish ∧
    ∀ i < n, R code.[i] code.[i + 1]

def Reach (R : V → V → Prop) (start finish : V) : Prop :=
  ∃ code : V, Certificate R code start finish

theorem certificate_definable (R : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) :
    Language.DefinableRel₃ ℒₒᵣ (Certificate R) := by
  let := hR
  unfold Certificate
  definability

theorem reach_definable (R : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) : Language.DefinableRel ℒₒᵣ (Reach R) := by
  let := certificate_definable R hR
  unfold Reach
  definability

theorem Certificate.nonempty {R : V → V → Prop} {code x y : V}
    (h : Certificate R code x y) : code ≠ 0 := by
  obtain ⟨n, hn, _⟩ := h
  intro hz
  simp [hz] at hn

theorem Certificate.head {R : V → V → Prop} {code x y : V}
    (h : Certificate R code x y) : code.[0] = x := h.choose_spec.2.1

theorem certificate_singleton (R : V → V → Prop) (x : V) :
    Certificate R ?[x] x x := by
  exact ⟨0, by simp, by simp, by simp, by simp⟩

theorem certificate_prefix {R : V → V → Prop} {code x y z : V}
    (edge : R x y) (path : Certificate R code y z) :
    Certificate R (x ∷ code) x z := by
  obtain ⟨n, hn, hfirst, hlast, hedge⟩ := path
  refine ⟨n + 1, by simp [hn], by simp, by simpa using hlast, ?_⟩
  intro i hi
  rcases zero_or_succ i with rfl | ⟨j, rfl⟩
  · simpa [hfirst] using edge
  · simpa using hedge j (by simpa using hi)

theorem certificate_suffix {R : V → V → Prop} {code x y z : V}
    (path : Certificate R code x y) (edge : R y z) :
    Certificate R (concat code z) x z := by
  obtain ⟨n, hn, hfirst, hlast, hedge⟩ := path
  have hzero : (0 : V) < len code := by simp [hn]
  refine ⟨n + 1, by simp [hn], ?_, ?_, ?_⟩
  · simpa [concat_nth_lt code z hzero] using hfirst
  · simp [← hn]
  · intro i hi
    rcases lt_or_eq_of_le (le_iff_lt_succ.mpr hi) with hlt | rfl
    · rw [concat_nth_lt code z (by simpa [hn] using lt_trans hlt (show n < n + 1 by simp)),
        concat_nth_lt code z (by simpa [hn] using hlt)]
      exact hedge i hlt
    · rw [concat_nth_lt code z (by simp [hn]), concat_nth_len' code z hn, hlast]
      exact edge

/-- Peel the first vertex without assuming the coded vector is externally finite. -/
theorem certificate_adjoin_cases {R : V → V → Prop} {x code y : V}
    (path : Certificate R (x ∷ code) x y) :
    (code = 0 ∧ x = y) ∨ (R x code.[0] ∧ Certificate R code code.[0] y) := by
  obtain ⟨n, hn, _, hlast, hedge⟩ := path
  rcases zero_or_succ n with rfl | ⟨m, rfl⟩
  · have hz : code = 0 := len_zero_iff_eq_nil.mp (by simpa using hn)
    exact Or.inl ⟨hz, by simpa using hlast⟩
  · refine Or.inr ⟨?_, m, by simpa using hn, rfl, by simpa using hlast, ?_⟩
    · simpa using hedge 0 (by simp)
    · intro i hi
      simpa using hedge (i + 1) (by simpa using hi)

namespace Splice

def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y q. y = q”
  adjoin := .mkSigma “y x xs ih q. (xs = 0 ∧ y = q) ∨ (xs ≠ 0 ∧ !adjoinDef y x ih)”

open Classical in
noncomputable def construction : VecRec.Construction V blueprint where
  nil p := p 0
  adjoin p x xs ih := if xs = 0 then p 0 else x ∷ ih
  nil_defined := .mk fun v => by simp [blueprint]
  adjoin_defined := .mk fun v => by
    by_cases h : v 2 = 0 <;> simp [blueprint, h]

end Splice

/-- Concatenate two vertex vectors, omitting the last vertex of the first.
For path certificates that vertex equals the first vertex of the second. -/
noncomputable def splice (first second : V) : V :=
  Splice.construction.result ![second] first

def spliceFormula : 𝚺₁.Semisentence 3 := Splice.blueprint.resultDef

instance splice_defined : 𝚺₁-Function₂ (splice : V → V → V) via spliceFormula :=
  Splice.construction.result_defined

instance splice_definable : 𝚺₁-Function₂ (splice : V → V → V) :=
  splice_defined.to_definable

local instance splice_firstOrder :
    Language.DefinableFunction₂ ℒₒᵣ (splice : V → V → V) :=
  definable_of_hierarchy splice_definable

@[simp] theorem splice_nil (q : V) : splice 0 q = q := by
  simp [splice, Splice.construction]

@[simp] theorem splice_singleton (x q : V) : splice ?[x] q = q := by
  simp [splice, Splice.construction]

theorem splice_adjoin (x p q : V) (hp : p ≠ 0) :
    splice (x ∷ p) q = x ∷ splice p q := by
  simp [splice, Splice.construction, hp]

/-- PA induction on coded vectors for arbitrary first-order definable predicates. -/
theorem vector_induction {P : V → Prop} (hP : Language.DefinablePred ℒₒᵣ P)
    (nil : P 0) (cons : ∀ x xs, P xs → P (x ∷ xs)) : ∀ xs, P xs := by
  refine InternalPAInduction.order_induction hP ?_
  intro xs ih
  rcases nil_or_adjoin xs with rfl | ⟨x, tail, rfl⟩
  · exact nil
  · exact cons x tail (ih tail (lt_adjoin' x tail))

/-- Numeric concatenation witnesses composition, including nonstandard paths. -/
theorem certificate_splice (R : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) :
    ∀ p q x y z, Certificate R p x y → Certificate R q y z →
      Certificate R (splice p q) x z := by
  let := certificate_definable R hR
  have hP : Language.DefinablePred ℒₒᵣ (fun p : V =>
      ∀ q x y z, Certificate R p x y → Certificate R q y z →
        Certificate R (splice p q) x z) := by definability
  refine vector_induction hP ?_ ?_
  · intro q x y z hp _
    exact False.elim (hp.nonempty rfl)
  · intro a tail ih q x y z hp hq
    have hx : a = x := by simpa using hp.head
    subst x
    rcases certificate_adjoin_cases hp with ⟨rfl, rfl⟩ | ⟨edge, rest⟩
    · simpa using hq
    · rw [splice_adjoin a tail q rest.nonempty]
      exact certificate_prefix edge (ih q tail.[0] y z rest hq)

theorem reach_refl (R : V → V → Prop) (x : V) : Reach R x x :=
  ⟨?[x], certificate_singleton R x⟩

theorem reach_single {R : V → V → Prop} {x y : V} (edge : R x y) : Reach R x y :=
  ⟨?[x, y], certificate_prefix edge (certificate_singleton R y)⟩

theorem reach_trans (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    {x y z : V} (first : Reach R x y) (second : Reach R y z) : Reach R x z := by
  obtain ⟨p, hp⟩ := first
  obtain ⟨q, hq⟩ := second
  exact ⟨splice p q, certificate_splice R hR p q x y z hp hq⟩

/-- Eliminate internally finite paths into a first-order definable invariant.
The definability requirement is needed for induction on nonstandard codes. -/
theorem reach_induction (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    {P : V → V → Prop} (hP : Language.DefinableRel ℒₒᵣ P)
    (refl : ∀ x, P x x)
    (step : ∀ x y z, R x y → P y z → P x z) :
    ∀ x y, Reach R x y → P x y := by
  let := certificate_definable R hR
  let := hP
  have hInvariant : Language.DefinablePred ℒₒᵣ (fun code : V =>
      ∀ x y, Certificate R code x y → P x y) := by definability
  have all : ∀ code x y, Certificate R code x y → P x y := by
    refine vector_induction hInvariant ?_ ?_
    · intro x y path
      exact False.elim (path.nonempty rfl)
    · intro a tail ih x y path
      have hx : a = x := by simpa using path.head
      subst x
      rcases certificate_adjoin_cases path with ⟨rfl, rfl⟩ | ⟨edge, rest⟩
      · exact refl a
      · exact step a tail.[0] y edge (ih tail.[0] y rest)
  rintro x y ⟨code, path⟩
  exact all code x y path

namespace Reverse

def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. !concatDef y ih x”

noncomputable def construction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ x _ ih := concat ih x
  nil_defined := .mk fun v => by simp [blueprint]
  adjoin_defined := .mk fun v => by simp [blueprint]

end Reverse

noncomputable def reverse (code : V) : V := Reverse.construction.result ![] code

def reverseFormula : 𝚺₁.Semisentence 2 := Reverse.blueprint.resultDef

instance reverse_defined : 𝚺₁-Function₁ (reverse : V → V) via reverseFormula :=
  Reverse.construction.result_defined

instance reverse_definable : 𝚺₁-Function₁ (reverse : V → V) :=
  reverse_defined.to_definable

local instance reverse_firstOrder : Language.DefinableFunction₁ ℒₒᵣ (reverse : V → V) :=
  definable_of_hierarchy reverse_definable

@[simp] theorem reverse_nil : reverse (0 : V) = 0 := by
  simp [reverse, Reverse.construction]

@[simp] theorem reverse_adjoin (x code : V) : reverse (x ∷ code) = concat (reverse code) x := by
  simp [reverse, Reverse.construction]

omit [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem converse_definable (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R) :
    Language.DefinableRel ℒₒᵣ (fun x y => R y x) := hR.retraction ![1, 0]

/-- Reversing the internal vertex vector reverses every edge. -/
theorem certificate_reverse (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R) :
    ∀ code x y, Certificate R code x y →
      Certificate (fun a b => R b a) (reverse code) y x := by
  let := certificate_definable R hR
  let := certificate_definable (fun a b => R b a) (converse_definable R hR)
  have hP : Language.DefinablePred ℒₒᵣ (fun code : V =>
      ∀ x y, Certificate R code x y →
        Certificate (fun a b => R b a) (reverse code) y x) := by definability
  refine vector_induction hP ?_ ?_
  · intro x y path
    exact False.elim (path.nonempty rfl)
  · intro a tail ih x y path
    have hx : a = x := by simpa using path.head
    subst x
    rcases certificate_adjoin_cases path with ⟨rfl, rfl⟩ | ⟨edge, rest⟩
    · simpa using certificate_singleton (fun a b => R b a) a
    · rw [reverse_adjoin]
      exact certificate_suffix (ih tail.[0] y rest) edge

theorem reach_converse (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    {x y : V} (path : Reach R x y) : Reach (fun a b => R b a) y x := by
  obtain ⟨code, cert⟩ := path
  exact ⟨reverse code, certificate_reverse R hR code x y cert⟩

theorem Certificate.mono {R S : V → V → Prop} (hRS : ∀ x y, R x y → S x y)
    {code x y : V} (path : Certificate R code x y) : Certificate S code x y := by
  obtain ⟨n, hn, hx, hy, edges⟩ := path
  exact ⟨n, hn, hx, hy, fun i hi => hRS _ _ (edges i hi)⟩

theorem reach_mono {R S : V → V → Prop} (hRS : ∀ x y, R x y → S x y)
    {x y : V} (path : Reach R x y) : Reach S x y := by
  obtain ⟨code, cert⟩ := path
  exact ⟨code, cert.mono hRS⟩

theorem reach_symmetric (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    (symm : ∀ x y, R x y → R y x) {x y : V} (path : Reach R x y) : Reach R y x :=
  reach_mono (fun a b h => symm b a h) (reach_converse R hR path)

/-- Internally finite zigzags, suitable for conversion once `R` is reduction. -/
def Convert (R : V → V → Prop) : V → V → Prop := Reach (fun x y => R x y ∨ R y x)

omit [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] in
theorem symmetric_step_definable (R : V → V → Prop)
    (hR : Language.DefinableRel ℒₒᵣ R) :
    Language.DefinableRel ℒₒᵣ (fun x y => R x y ∨ R y x) :=
  Language.Definable.or hR (converse_definable R hR)

theorem convert_definable (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R) :
    Language.DefinableRel ℒₒᵣ (Convert R) :=
  reach_definable _ (symmetric_step_definable R hR)

theorem convert_refl (R : V → V → Prop) (x : V) : Convert R x x := reach_refl _ x

theorem convert_single {R : V → V → Prop} {x y : V} (h : R x y) : Convert R x y :=
  reach_single (Or.inl h)

theorem convert_symm (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    {x y : V} (h : Convert R x y) : Convert R y x :=
  reach_symmetric _ (symmetric_step_definable R hR) (fun _ _ h => h.symm) h

theorem convert_trans (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R)
    {x y z : V} (hxy : Convert R x y) (hyz : Convert R y z) : Convert R x z :=
  reach_trans _ (symmetric_step_definable R hR) hxy hyz

theorem convert_equivalence (R : V → V → Prop) (hR : Language.DefinableRel ℒₒᵣ R) :
    Equivalence (Convert R) :=
  ⟨convert_refl R, fun h => convert_symm R hR h, fun h₁ h₂ => convert_trans R hR h₁ h₂⟩

end FregeanECA.Research.Z2Reverse.InternalPaths
