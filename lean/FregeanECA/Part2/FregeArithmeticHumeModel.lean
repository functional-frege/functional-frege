import FregeanECA.Part2.FregeArithmeticInterpretation

/-! Hume's Principle for the interpreted Frege-Arithmetic structure.
The source quantifies over the actual relation sorts. A source bijection
need only be supported on number arguments, so its target graph is obtained
by the explicit comprehension restriction to the number domain squared. -/
namespace FregeanECA.Part2.FregeArithmeticHumeModel

open Positive Arithmetic HumeOrder HumeBijections FregeArithmeticInterpretation
universe u v
variable {D : Type u} {R : Nat → Type v}

theorem interpreted_member (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (P : R 0) (x : Number M N) :
    FregeArithmetic.member (interpretedModel M full domain) P x ↔ member M P x.val :=
  Iff.rfl

theorem interpreted_member2 (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (G : R 1) (x y : Number M N) :
    FregeArithmetic.member2 (interpretedModel M full domain) G x y ↔
      member2 M G x.val y.val := by
  have values : (fun i => (FregeArithmetic.pair x y i).val) = pair x.val y.val := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp only [FregeArithmetic.member2, interpretedModel, member2, values]

def restrictGraphFormula : Applicative.Formula :=
  .conjunction (unary 0 (.var 0))
    (.conjunction (unary 0 (.var 1)) (binary 0 (.var 0) (.var 1)))

theorem full_has_restricted_graph (M : Interpretation D R) (full : HasFullComprehension M)
    (N : R 0) (G : R 1) :
    ∃ H : R 1, ∀ x y, member2 M H x y ↔
      member M N x ∧ member M N y ∧ member2 M G x y := by
  let predicates := pushPredicate (pushPredicate (basePredicates M full) 0 N) 1 G
  obtain ⟨H, law⟩ := full.comprehend 1 restrictGraphFormula (fun _ => M.constantK) predicates
  refine ⟨H, ?_⟩
  intro x y
  have evaluated := law (pair x y)
  simp only [restrictGraphFormula, Applicative.Formula.truth, unary, binary_truth,
    Positive.Term.value, assignTuple, pushObject] at evaluated
  exact evaluated

theorem bijection_on_subtype (M : Interpretation D R) (full : HasFullComprehension M)
    {N P Q : R 0} (domain : PeanoDomain M N) {G : R 1}
    (bij : GraphBijection M (OnNumbers M N P) (OnNumbers M N Q) G) :
    FregeArithmetic.GraphBijection (interpretedModel M full domain)
      (FregeArithmetic.member (interpretedModel M full domain) P)
      (FregeArithmetic.member (interpretedModel M full domain) Q) G := by
  constructor
  · intro x y h
    have support := bij.support x.val y.val ((interpreted_member2 M full domain G x y).mp h)
    exact ⟨support.1.2, support.2.2⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := bij.total x.val ⟨x.property, hx⟩
    exact ⟨⟨y, (bij.support x.val y hxy).2.1⟩,
      (interpreted_member2 M full domain G x _).mpr hxy⟩
  · intro y hy
    obtain ⟨x, hxy⟩ := bij.onto y.val ⟨y.property, hy⟩
    exact ⟨⟨x, (bij.support x y.val hxy).1.1⟩,
      (interpreted_member2 M full domain G _ y).mpr hxy⟩
  · intro x y z hxy hxz
    apply Subtype.ext
    exact bij.functional x.val y.val z.val
      ((interpreted_member2 M full domain G x y).mp hxy)
      ((interpreted_member2 M full domain G x z).mp hxz)
  · intro x y z hxz hyz
    apply Subtype.ext
    exact bij.injective x.val y.val z.val
      ((interpreted_member2 M full domain G x z).mp hxz)
      ((interpreted_member2 M full domain G y z).mp hyz)

theorem bijection_from_subtype (M : Interpretation D R) (full : HasFullComprehension M)
    {N P Q : R 0} (domain : PeanoDomain M N) {G : R 1}
    (bij : FregeArithmetic.GraphBijection (interpretedModel M full domain)
      (FregeArithmetic.member (interpretedModel M full domain) P)
      (FregeArithmetic.member (interpretedModel M full domain) Q) G) :
    ∃ H : R 1, GraphBijection M (OnNumbers M N P) (OnNumbers M N Q) H := by
  obtain ⟨H, law⟩ := full_has_restricted_graph M full N G
  refine ⟨H, ?_⟩
  constructor
  · intro x y h
    obtain ⟨nx, ny, gxy⟩ := (law x y).mp h
    have support := bij.support ⟨x, nx⟩ ⟨y, ny⟩
      ((interpreted_member2 M full domain G _ _).mpr gxy)
    exact ⟨⟨nx, support.1⟩, ⟨ny, support.2⟩⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := bij.total ⟨x, hx.1⟩ hx.2
    exact ⟨y.val, (law x y.val).mpr ⟨hx.1, y.property,
      (interpreted_member2 M full domain G _ y).mp hxy⟩⟩
  · intro y hy
    obtain ⟨x, hxy⟩ := bij.onto ⟨y, hy.1⟩ hy.2
    exact ⟨x.val, (law x.val y).mpr ⟨x.property, hy.1,
      (interpreted_member2 M full domain G x _).mp hxy⟩⟩
  · intro x y z hxy hxz
    obtain ⟨nx, ny, gxy⟩ := (law x y).mp hxy
    obtain ⟨_, nz, gxz⟩ := (law x z).mp hxz
    exact congrArg Subtype.val (bij.functional ⟨x, nx⟩ ⟨y, ny⟩ ⟨z, nz⟩
      ((interpreted_member2 M full domain G _ _).mpr gxy)
      ((interpreted_member2 M full domain G _ _).mpr gxz))
  · intro x y z hxz hyz
    obtain ⟨nx, nz, gxz⟩ := (law x z).mp hxz
    obtain ⟨ny, _, gyz⟩ := (law y z).mp hyz
    exact congrArg Subtype.val (bij.injective ⟨x, nx⟩ ⟨y, ny⟩ ⟨z, nz⟩
      ((interpreted_member2 M full domain G _ _).mpr gxz)
      ((interpreted_member2 M full domain G _ _).mpr gyz))

theorem interpreted_equinumerous (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (P Q : R 0) :
    FregeArithmetic.Equinumerous (interpretedModel M full domain) P Q ↔
      Equinumerous M N P Q := by
  constructor
  · rintro ⟨G, bij⟩
    exact bijection_from_subtype M full domain bij
  · rintro ⟨G, bij⟩
    exact ⟨G, bijection_on_subtype M full domain bij⟩

/-- The separately defined source structure satisfies its generic HP axiom. -/
theorem interpreted_hume_principle (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) :
    FregeArithmetic.HumePrinciple (interpretedModel M full domain) := by
  intro P Q
  rw [interpreted_equinumerous M full domain P Q]
  have hp := HumeInternal.humes_principle M full domain
    (number_code M full domain P) (number_code M full domain Q)
  constructor
  · intro same
    exact hp.mp (congrArg Subtype.val same)
  · intro eqv
    exact Subtype.ext (hp.mpr eqv)

end FregeanECA.Part2.FregeArithmeticHumeModel
