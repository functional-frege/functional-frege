import FregeanECA.Part2.HumeOrder

/-! Internal initial segments and available injective graphs. Bounds are
elements of an arbitrary interpreted Peano domain, including nonstandard
elements. They are never replaced by external `Fin n` types. -/

namespace FregeanECA.Part2.HumeFinite
open Positive Arithmetic HumeOrder
universe u v
variable {D : Type u} {R : Nat → Type v}

def Lt (M : Interpretation D R) (x y : D) : Prop := Le M x y ∧ x ≠ y

def InSegment (M : Interpretation D R) (N : R 0) (n x : D) : Prop :=
  member M N x ∧ Lt M x n

theorem lt_irrefl (M : Interpretation D R) (x : D) : ¬ Lt M x x :=
  fun h => h.2 rfl

theorem lt_successor_self (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) {x : D} (nx : member M N x) :
    Lt M x (modelSuccessor M x) := by
  refine ⟨le_self_successor M x, ?_⟩
  intro same
  exact not_successor_le_self M full domain x nx (same ▸ le_refl M x)

theorem lt_successor_iff (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) {x n : D} (nn : member M N n) :
    Lt M x (modelSuccessor M n) ↔ Le M x n := by
  constructor
  · intro h
    rcases (le_successor_iff M full domain x n).mp h.1 with hle | heq
    · exact hle
    · exact False.elim (h.2 heq)
  · intro h
    refine ⟨le_successor M h, ?_⟩
    intro same
    exact not_successor_le_self M full domain n nn (same ▸ h)

theorem no_lt_zero (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (x : D) : ¬ Lt M x (modelZero M) :=
  fun h => h.2 ((le_zero_iff M full domain x).mp h.1)

theorem segment_successor (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) {n x : D} (nn : member M N n) :
    InSegment M N (modelSuccessor M n) x ↔ InSegment M N n x ∨ x = n := by
  classical
  constructor
  · rintro ⟨nx, hx⟩
    have h := (lt_successor_iff M full domain nn).mp hx
    by_cases same : x = n
    · exact Or.inr same
    · exact Or.inl ⟨nx, h, same⟩
  · rintro (⟨nx, hxn, _⟩ | rfl)
    · exact ⟨nx, (lt_successor_iff M full domain nn).mpr hxn⟩
    · exact ⟨nn, lt_successor_self M full domain nn⟩

/-- An available binary graph of an injection between internal initial
segments; support rules out any extraneous graph pairs. -/
structure Injection (M : Interpretation D R) (N : R 0) (G : R 1) (n m : D) : Prop where
  support : ∀ x y, member2 M G x y → InSegment M N n x ∧ InSegment M N m y
  total : ∀ x, InSegment M N n x → ∃ y, member2 M G x y
  functional : ∀ x y z, member2 M G x y → member2 M G x z → y = z
  injective : ∀ x y z, member2 M G x z → member2 M G y z → x = y

def notEqual (x y : Positive.Term) : Applicative.Formula :=
  .implies (.equal x y) .falsum

/-- Unary predicate zero names N; binary predicate one names the order. -/
def segmentFormula (n x : Positive.Term) : Applicative.Formula :=
  .conjunction (unary 0 x) (.conjunction (binary 1 x n) (notEqual x n))

theorem segment_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) {L : R 1} (orderLaw : RepresentsLe M L)
    (bound : r 1 1 = L) (n x : Positive.Term) :
    (segmentFormula n x).truth M o r ↔ InSegment M (r 0 0) (n.value M o) (x.value M o) := by
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  simp [segmentFormula, notEqual, Applicative.Formula.truth, binary_truth,
    unary, member, bound, orderLaw, InSegment, Lt]

def injectionFormula : Applicative.Formula :=
  .conjunction
    (.forallObject (.forallObject (.implies (binary 0 (.var 1) (.var 0))
      (.conjunction (segmentFormula (.var 2) (.var 1))
        (segmentFormula (.var 3) (.var 0))))))
    (.conjunction
      (.forallObject (.implies (segmentFormula (.var 1) (.var 0))
        (.existsObject (binary 0 (.var 1) (.var 0)))))
      (.conjunction
        (.forallObject (.forallObject (.forallObject
          (.implies (.conjunction (binary 0 (.var 2) (.var 1)) (binary 0 (.var 2) (.var 0)))
            (.equal (.var 1) (.var 0))))))
        (.forallObject (.forallObject (.forallObject
          (.implies (.conjunction (binary 0 (.var 2) (.var 0)) (binary 0 (.var 1) (.var 0)))
            (.equal (.var 2) (.var 1))))))))

theorem injection_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) {L : R 1} (orderLaw : RepresentsLe M L)
    (bound : r 1 1 = L) :
    injectionFormula.truth M o r ↔ Injection M (r 0 0) (r 1 0) (o 0) (o 1) := by
  simp only [injectionFormula, Applicative.Formula.truth, binary_truth,
    segment_formula_truth M _ r orderLaw bound, Positive.Term.value, pushObject, and_imp]
  exact ⟨fun ⟨hs, ht, hf, hi⟩ => ⟨hs, ht, hf, hi⟩,
    fun h => ⟨h.support, h.total, h.functional, h.injective⟩⟩

/-- Swap the removed domain point's image q with the last target point m,
then restrict to the predecessor segments n,m. -/
def SwapRestriction (M : Interpretation D R) (N : R 0) (G : R 1)
    (n m q x y : D) : Prop :=
  InSegment M N n x ∧ InSegment M N m y ∧
    ((member2 M G x y ∧ y ≠ m) ∨ (member2 M G x m ∧ y = q))

/-- Free objects: x,y,n,m,q. Graph is binary predicate zero, order one. -/
def swapRestrictionFormula : Applicative.Formula :=
  .conjunction (segmentFormula (.var 2) (.var 0))
    (.conjunction (segmentFormula (.var 3) (.var 1))
      (.disjunction
        (.conjunction (binary 0 (.var 0) (.var 1)) (notEqual (.var 1) (.var 3)))
        (.conjunction (binary 0 (.var 0) (.var 3)) (.equal (.var 1) (.var 4)))))

theorem swap_restriction_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) {L : R 1} (orderLaw : RepresentsLe M L)
    (bound : r 1 1 = L) :
    swapRestrictionFormula.truth M o r ↔
      SwapRestriction M (r 0 0) (r 1 0) (o 2) (o 3) (o 4) (o 0) (o 1) := by
  simp only [swapRestrictionFormula, Applicative.Formula.truth,
    segment_formula_truth M _ r orderLaw bound, binary_truth, notEqual,
    Positive.Term.value, SwapRestriction]

theorem full_has_swap_restriction (M : Interpretation D R) (full : HasFullComprehension M)
    (N : R 0) (G : R 1) (n m q : D) :
    ∃ H : R 1, ∀ x y, member2 M H x y ↔ SwapRestriction M N G n m q x y := by
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  let predicates := pushPredicate (pushPredicate
    (withNatural (basePredicates M full) N) 1 L) 1 G
  let parameters : ObjectAssignment D := pushObject (pushObject (fun _ => q) m) n
  obtain ⟨H, law⟩ := full.comprehend 1 swapRestrictionFormula parameters predicates
  refine ⟨H, ?_⟩
  intro x y
  exact (law (pair x y)).trans (swap_restriction_formula_truth M _ predicates orderLaw rfl)

theorem segment_of_successor_ne (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) {n x : D} (nn : member M N n)
    (hx : InSegment M N (modelSuccessor M n) x) (different : x ≠ n) :
    InSegment M N n x := by
  rcases (segment_successor M full domain nn).mp hx with h | same
  · exact h
  · exact False.elim (different same)

/-- Removing the last source point and swapping its image with the last
target point produces an available injection between predecessor segments. -/
theorem remove_last_injection (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) {G : R 1} {n m : D}
    (nn : member M N n) (nm : member M N m)
    (inj : Injection M N G (modelSuccessor M n) (modelSuccessor M m)) :
    ∃ H : R 1, Injection M N H n m := by
  classical
  obtain ⟨q, last⟩ := inj.total n ⟨nn, lt_successor_self M full domain nn⟩
  obtain ⟨H, law⟩ := full_has_swap_restriction M full N G n m q
  have qsmall (x : D) (hx : InSegment M N n x) (hxm : member2 M G x m) :
      InSegment M N m q := by
    apply segment_of_successor_ne M full domain nm (inj.support n q last).2
    intro same
    exact hx.2.2 (inj.injective x n m hxm (same ▸ last))
  refine ⟨H, ?_⟩
  constructor
  · intro x y h
    exact ⟨((law x y).mp h).1, ((law x y).mp h).2.1⟩
  · intro x hx
    obtain ⟨y, hxy⟩ := inj.total x ((segment_successor M full domain nn).mpr (Or.inl hx))
    by_cases same : y = m
    · subst y
      exact ⟨q, (law x q).mpr ⟨hx, qsmall x hx hxy, Or.inr ⟨hxy, rfl⟩⟩⟩
    · exact ⟨y, (law x y).mpr ⟨hx,
        segment_of_successor_ne M full domain nm (inj.support x y hxy).2 same,
        Or.inl ⟨hxy, same⟩⟩⟩
  · intro x y z hy hz
    rcases ((law x y).mp hy).2.2 with ⟨gxy, ym⟩ | ⟨gxm, yq⟩
    · rcases ((law x z).mp hz).2.2 with ⟨gxz, _⟩ | ⟨gxm, _⟩
      · exact inj.functional x y z gxy gxz
      · exact False.elim (ym (inj.functional x y m gxy gxm))
    · rcases ((law x z).mp hz).2.2 with ⟨gxz, zm⟩ | ⟨_, zq⟩
      · exact False.elim (zm (inj.functional x z m gxz gxm))
      · exact yq.trans zq.symm
  · intro x y z hx hy
    have xs := ((law x z).mp hx).1
    have ys := ((law y z).mp hy).1
    rcases ((law x z).mp hx).2.2 with ⟨gxz, _⟩ | ⟨gxm, zq⟩
    · rcases ((law y z).mp hy).2.2 with ⟨gyz, _⟩ | ⟨_, zq⟩
      · exact inj.injective x y z gxz gyz
      · exact False.elim (xs.2.2 (inj.injective x n q (zq ▸ gxz) last))
    · rcases ((law y z).mp hy).2.2 with ⟨gyz, _⟩ | ⟨gym, _⟩
      · exact False.elim (ys.2.2 (inj.injective y n q (zq ▸ gyz) last))
      · exact inj.injective x y m gxm gym

/-- The induction formula quantifies over the source bound and every available
graph. Its free object variable is the target bound. -/
def pigeonholeFormula : Applicative.Formula :=
  .forallObject (.implies (unary 0 (.var 0))
    (.forallPredicate 1 (.implies injectionFormula (binary 1 (.var 0) (.var 1)))))

theorem pigeonhole_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) {L : R 1} (orderLaw : RepresentsLe M L)
    (bound : r 1 0 = L) :
    pigeonholeFormula.truth M o r ↔
      ∀ n, member M (r 0 0) n → ∀ G : R 1,
        Injection M (r 0 0) G n (o 0) → Le M n (o 0) := by
  change ∀ x y, member2 M L x y ↔ Le M x y at orderLaw
  simp only [pigeonholeFormula, Applicative.Formula.truth, unary,
    Positive.Term.value, pushObject, member]
  apply forall_congr'
  intro n
  apply imp_congr Iff.rfl
  apply forall_congr'
  intro G
  have graphs : pushPredicate r 1 G 1 1 = L := bound
  rw [injection_formula_truth M _ _ orderLaw graphs, binary_truth]
  simpa [pushPredicate, pushObject, Positive.Term.value, bound] using
    imp_congr Iff.rfl (orderLaw n (o 0))

/-- Internal finite pigeonhole, including nonstandard bounds: an available
injection from the n-segment into the m-segment entails n ≤ m. -/
theorem injection_bound (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) :
    ∀ m, member M N m → ∀ n, member M N n → ∀ G : R 1,
      Injection M N G n m → Le M n m := by
  classical
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  let predicates := pushPredicate (withNatural (basePredicates M full) N) 1 L
  apply induction_of_formula M domain pigeonholeFormula (fun _ => M.constantK)
    predicates (fun m => ∀ n, member M N n → ∀ G : R 1, Injection M N G n m → Le M n m)
  · intro m
    exact pigeonhole_formula_truth M _ predicates orderLaw rfl
  · intro n nn G inj
    by_cases nz : n = modelZero M
    · subst n
      exact le_refl M _
    · have zeroBelow : InSegment M N n (modelZero M) :=
        ⟨domain.zero_member, zero_le M domain nn, Ne.symm nz⟩
      obtain ⟨y, hy⟩ := inj.total _ zeroBelow
      exact False.elim (no_lt_zero M full domain y (inj.support _ y hy).2.2)
  · intro m nm ih n nn G inj
    rcases zero_or_successor M full domain n nn with rfl | ⟨k, nk, rfl⟩
    · exact zero_le M domain (domain.successor_closed m nm)
    · obtain ⟨H, small⟩ := remove_last_injection M full domain nk nm inj
      exact successor_le_successor M full (ih k nk H small)

structure Bijection (M : Interpretation D R) (N : R 0) (G : R 1) (n m : D) : Prop
    extends Injection M N G n m where
  onto : ∀ y, InSegment M N m y → ∃ x, member2 M G x y

theorem full_has_inverse (M : Interpretation D R) (full : HasFullComprehension M)
    (G : R 1) : ∃ H : R 1, ∀ x y, member2 M H x y ↔ member2 M G y x := by
  let predicates := pushPredicate (basePredicates M full) 1 G
  obtain ⟨H, law⟩ := full.comprehend 1 (binary 0 (.var 1) (.var 0))
    (fun _ => M.constantK) predicates
  refine ⟨H, ?_⟩
  intro x y
  exact (law (pair x y)).trans (binary_truth M _ predicates 0 (.var 1) (.var 0))

theorem inverse_injection (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} {G : R 1} {n m : D} (bij : Bijection M N G n m) :
    ∃ H : R 1, Injection M N H m n := by
  obtain ⟨H, law⟩ := full_has_inverse M full G
  refine ⟨H, ?_⟩
  constructor
  · intro x y h
    exact (bij.support y x ((law x y).mp h)).symm
  · intro x hx
    obtain ⟨y, h⟩ := bij.onto x hx
    exact ⟨y, (law x y).mpr h⟩
  · intro x y z hxy hxz
    exact bij.injective y z x ((law x y).mp hxy) ((law x z).mp hxz)
  · intro x y z hxz hyz
    exact bij.functional z x y ((law x z).mp hxz) ((law y z).mp hyz)

/-- Available bijections between internal finite initial segments preserve
their bounds, even when those bounds are nonstandard model elements. -/
theorem bijection_bounds_equal (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) {G : R 1} {n m : D}
    (nn : member M N n) (nm : member M N m) (bij : Bijection M N G n m) : n = m := by
  obtain ⟨H, inverse⟩ := inverse_injection M full bij
  exact le_antisymm M full domain nn
    (injection_bound M full domain m nm n nn G bij.toInjection)
    (injection_bound M full domain n nn m nm H inverse)

/-- An available injection from the whole interpreted number domain into a
bounded initial segment. This record will be refuted, not assumed to exist. -/
structure NaturalInjection (M : Interpretation D R) (N : R 0) (G : R 1) (m : D) : Prop where
  support : ∀ x y, member2 M G x y → member M N x ∧ InSegment M N m y
  total : ∀ x, member M N x → ∃ y, member2 M G x y
  functional : ∀ x y z, member2 M G x y → member2 M G x z → y = z
  injective : ∀ x y z, member2 M G x z → member2 M G y z → x = y

def restrictFormula : Applicative.Formula :=
  .conjunction (segmentFormula (.var 2) (.var 0)) (binary 0 (.var 0) (.var 1))

theorem full_has_restriction (M : Interpretation D R) (full : HasFullComprehension M)
    (N : R 0) (G : R 1) (n : D) :
    ∃ H : R 1, ∀ x y, member2 M H x y ↔ InSegment M N n x ∧ member2 M G x y := by
  obtain ⟨L, orderLaw⟩ := full_has_order M full
  let predicates := pushPredicate (pushPredicate
    (withNatural (basePredicates M full) N) 1 L) 1 G
  obtain ⟨H, law⟩ := full.comprehend 1 restrictFormula (fun _ => n) predicates
  refine ⟨H, ?_⟩
  intro x y
  have evaluated := law (pair x y)
  rw [restrictFormula, Applicative.Formula.truth,
    segment_formula_truth M _ predicates orderLaw rfl, binary_truth] at evaluated
  exact evaluated

theorem restrict_natural_injection (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} {G : R 1} {m : D} (inj : NaturalInjection M N G m) (n : D) :
    ∃ H : R 1, Injection M N H n m := by
  obtain ⟨H, law⟩ := full_has_restriction M full N G n
  refine ⟨H, ?_⟩
  constructor
  · intro x y h
    obtain ⟨hx, gxy⟩ := (law x y).mp h
    exact ⟨hx, (inj.support x y gxy).2⟩
  · intro x hx
    obtain ⟨y, gxy⟩ := inj.total x hx.1
    exact ⟨y, (law x y).mpr ⟨hx, gxy⟩⟩
  · intro x y z hxy hxz
    exact inj.functional x y z ((law x y).mp hxy).2 ((law x z).mp hxz).2
  · intro x y z hxz hyz
    exact inj.injective x y z ((law x z).mp hxz).2 ((law y z).mp hyz).2

theorem no_natural_injection (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) {m : D} (nm : member M N m) (G : R 1) :
    ¬ NaturalInjection M N G m := by
  intro inj
  obtain ⟨H, restricted⟩ := restrict_natural_injection M full inj (modelSuccessor M m)
  exact not_successor_le_self M full domain m nm
    (injection_bound M full domain m nm _ (domain.successor_closed m nm) H restricted)

end FregeanECA.Part2.HumeFinite
