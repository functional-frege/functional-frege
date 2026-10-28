import FregeanECA.Part2.HumeFinite

/-! Bijections witnessed by the model's actual binary relation sort.
Inverse and composition graphs are supplied by explicit comprehension
formulas, not by unrestricted external graph availability. -/

namespace FregeanECA.Part2.HumeBijections
open Positive Arithmetic HumeOrder HumeFinite
universe u v
variable {D : Type u} {R : Nat → Type v}

structure GraphBijection (M : Interpretation D R) (A B : D → Prop) (G : R 1) : Prop where
  support : ∀ x y, member2 M G x y → A x ∧ B y
  total : ∀ x, A x → ∃ y, member2 M G x y
  onto : ∀ y, B y → ∃ x, member2 M G x y
  functional : ∀ x y z, member2 M G x y → member2 M G x z → y = z
  injective : ∀ x y z, member2 M G x z → member2 M G y z → x = y

def OnNumbers (M : Interpretation D R) (N P : R 0) (x : D) : Prop :=
  member M N x ∧ member M P x

def Equinumerous (M : Interpretation D R) (N P Q : R 0) : Prop :=
  ∃ G : R 1, GraphBijection M (OnNumbers M N P) (OnNumbers M N Q) G

def FiniteSize (M : Interpretation D R) (N P : R 0) (n : D) : Prop :=
  member M N n ∧ ∃ G : R 1,
    GraphBijection M (OnNumbers M N P) (InSegment M N n) G

theorem inverse (M : Interpretation D R) (full : HasFullComprehension M)
    {A B : D → Prop} {G : R 1} (bij : GraphBijection M A B G) :
    ∃ H : R 1, GraphBijection M B A H := by
  obtain ⟨H, law⟩ := full_has_inverse M full G
  refine ⟨H, ?_⟩
  constructor
  · intro x y h
    exact (bij.support y x ((law x y).mp h)).symm
  · intro x hx
    obtain ⟨y, h⟩ := bij.onto x hx
    exact ⟨y, (law x y).mpr h⟩
  · intro y hy
    obtain ⟨x, h⟩ := bij.total y hy
    exact ⟨x, (law x y).mpr h⟩
  · intro x y z hxy hxz
    exact bij.injective y z x ((law x y).mp hxy) ((law x z).mp hxz)
  · intro x y z hxz hyz
    exact bij.functional z x y ((law x z).mp hxz) ((law y z).mp hyz)

def compositionFormula : Applicative.Formula :=
  .existsObject (.conjunction (binary 0 (.var 1) (.var 0))
    (binary 1 (.var 0) (.var 2)))

theorem full_has_composition (M : Interpretation D R) (full : HasFullComprehension M)
    (G H : R 1) : ∃ C : R 1, ∀ x z,
      member2 M C x z ↔ ∃ y, member2 M G x y ∧ member2 M H y z := by
  let predicates := pushPredicate (pushPredicate (basePredicates M full) 1 H) 1 G
  obtain ⟨C, law⟩ := full.comprehend 1 compositionFormula (fun _ => M.constantK) predicates
  refine ⟨C, ?_⟩
  intro x z
  have evaluated := law (pair x z)
  simp only [compositionFormula, Applicative.Formula.truth, binary_truth,
    Positive.Term.value, pushObject] at evaluated
  exact evaluated

theorem compose (M : Interpretation D R) (full : HasFullComprehension M)
    {A B C : D → Prop} {G H : R 1}
    (first : GraphBijection M A B G) (second : GraphBijection M B C H) :
    ∃ J : R 1, GraphBijection M A C J := by
  obtain ⟨J, law⟩ := full_has_composition M full G H
  refine ⟨J, ?_⟩
  constructor
  · intro x z h
    obtain ⟨y, hxy, hyz⟩ := (law x z).mp h
    exact ⟨(first.support x y hxy).1, (second.support y z hyz).2⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := first.total x hx
    obtain ⟨z, hyz⟩ := second.total y (first.support x y hxy).2
    exact ⟨z, (law x z).mpr ⟨y, hxy, hyz⟩⟩
  · intro z hz
    obtain ⟨y, hyz⟩ := second.onto z hz
    obtain ⟨x, hxy⟩ := first.onto y (second.support y z hyz).1
    exact ⟨x, (law x z).mpr ⟨y, hxy, hyz⟩⟩
  · intro x y z hxy hxz
    obtain ⟨a, hxa, hay⟩ := (law x y).mp hxy
    obtain ⟨b, hxb, hbz⟩ := (law x z).mp hxz
    have same := first.functional x a b hxa hxb
    subst b
    exact second.functional a y z hay hbz
  · intro x y z hxz hyz
    obtain ⟨a, hxa, haz⟩ := (law x z).mp hxz
    obtain ⟨b, hyb, hbz⟩ := (law y z).mp hyz
    have same := second.injective a b z haz hbz
    subst b
    exact first.injective x y a hxa hyb

theorem finite_size_unique (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {n m : D}
    (hn : FiniteSize M N P n) (hm : FiniteSize M N P m) : n = m := by
  obtain ⟨nn, G, gn⟩ := hn
  obtain ⟨nm, H, hm⟩ := hm
  obtain ⟨I, ig⟩ := inverse M full gn
  obtain ⟨J, j⟩ := compose M full ig hm
  exact bijection_bounds_equal M full domain nn nm
    { support := j.support, total := j.total, functional := j.functional,
      injective := j.injective, onto := j.onto }

theorem equinumerous_symm (M : Interpretation D R) (full : HasFullComprehension M)
    {N P Q : R 0} (h : Equinumerous M N P Q) : Equinumerous M N Q P := by
  obtain ⟨G, h⟩ := h
  exact inverse M full h

theorem equinumerous_preserves_size (M : Interpretation D R) (full : HasFullComprehension M)
    {N P Q : R 0} (eqv : Equinumerous M N P Q) {n : D}
    (size : FiniteSize M N Q n) : FiniteSize M N P n := by
  obtain ⟨G, pq⟩ := eqv
  obtain ⟨nn, H, qn⟩ := size
  exact ⟨nn, compose M full pq qn⟩

theorem same_size_equinumerous (M : Interpretation D R) (full : HasFullComprehension M)
    {N P Q : R 0} {n : D} (pn : FiniteSize M N P n) (qn : FiniteSize M N Q n) :
    Equinumerous M N P Q := by
  obtain ⟨_, G, pg⟩ := pn
  obtain ⟨_, H, qh⟩ := qn
  obtain ⟨I, ih⟩ := inverse M full qh
  exact compose M full pg ih

theorem not_finite_of_enumerable (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) {G : R 1}
    (enumeration : GraphBijection M (OnNumbers M N P) (member M N) G) :
    ¬ ∃ n, FiniteSize M N P n := by
  rintro ⟨n, nn, H, size⟩
  obtain ⟨I, ni⟩ := inverse M full enumeration
  obtain ⟨J, j⟩ := compose M full ni size
  exact no_natural_injection M full domain nn J
    { support := j.support, total := j.total,
      functional := j.functional, injective := j.injective }

end FregeanECA.Part2.HumeBijections
