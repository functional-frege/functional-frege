import FregeanECA.Part2.FregeArithmeticRecursion

/-! Fixed source-language definitions of the auxiliary data used in the
arithmetic translation. External binders are N, G, z, k, in that order.
Thus k and z have object indices 0 and 1, N has unary index 0, and G has
ternary index 0. All other auxiliary predicates are locally quantified. -/
namespace FregeanECA.Part2.FregeArithmeticData
open Positive FregeArithmetic
universe u v
variable {D : Type u} {R : Nat → Type v}

theorem iff_formula_truth (M : FregeArithmetic.Interpretation D R)
    (p q : FregeArithmetic.Formula) (o : ObjectAssignment D) (r : PredicateAssignment R) :
    (iffFormula p q).truth M o r ↔ (p.truth M o r ↔ q.truth M o r) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

def predecessionAt (a b : Nat) : FregeArithmetic.Formula :=
  .existsPredicate 0 (.existsPredicate 0 (.existsObject
    (.conjunction (unary 1 (.var 0))
      (.conjunction
        (.forallObject (iffFormula (unary 0 (.var 0))
          (.conjunction (unary 1 (.var 0)) (notFormula (.equal (.var 0) (.var 1))))))
        (.conjunction (.equal (.number 0) (.var (a + 1)))
          (.equal (.number 1) (.var (b + 1))))))))

theorem predecession_at_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) (a b : Nat) :
    (predecessionAt a b).truth M o r ↔ Precedes M (o a) (o b) := by
  simp only [predecessionAt, FregeArithmetic.Formula.truth, iff_formula_truth,
    unary, notFormula, FregeArithmetic.Term.value, pushPredicate, pushObject,
    dite_true, Precedes, member]

def ancestralAt (a b : Nat) : FregeArithmetic.Formula :=
  .forallPredicate 0 (.implies
    (.conjunction (unary 0 (.var a))
      (.forallObject (.forallObject
        (.implies (.conjunction (unary 0 (.var 1)) (predecessionAt 1 0))
          (unary 0 (.var 0))))))
    (unary 0 (.var b)))

theorem ancestral_at_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) (a b : Nat) :
    (ancestralAt a b).truth M o r ↔ Ancestral M (o a) (o b) := by
  simp [ancestralAt, FregeArithmetic.Formula.truth, predecession_at_truth,
    unary, FregeArithmetic.Term.value, pushPredicate, pushObject, member,
    Ancestral, and_imp]

def applicationAt (f x y k z : Nat) : FregeArithmetic.Formula :=
  .disjunction (.conjunction (.equal (.var f) (.var k)) (predecessionAt x y))
    (.conjunction (notFormula (.equal (.var f) (.var k))) (.equal (.var y) (.var z)))

def ApplicationRelation (M : FregeArithmetic.Interpretation D R) (k z f x y : D) : Prop :=
  (f = k ∧ Precedes M x y) ∨ (f ≠ k ∧ y = z)

theorem application_at_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) (f x y k z : Nat) :
    (applicationAt f x y k z).truth M o r ↔
      ApplicationRelation M (o k) (o z) (o f) (o x) (o y) := by
  simp only [applicationAt, FregeArithmetic.Formula.truth, predecession_at_truth,
    notFormula, FregeArithmetic.Term.value, ApplicationRelation]

def zeroDefinition : FregeArithmetic.Formula :=
  .existsPredicate 0 (.conjunction
    (.forallObject (notFormula (unary 0 (.var 0))))
    (.equal (.var 1) (.number 0)))

def naturalDefinition : FregeArithmetic.Formula :=
  .forallObject (iffFormula (unary 0 (.var 0)) (ancestralAt 2 0))

def applicationDefinition : FregeArithmetic.Formula :=
  .forallObject (.forallObject (.forallObject
    (iffFormula (FregeArithmeticDefinable.graphAtom 0 2 1 0) (applicationAt 2 1 0 3 4))))

def dataFormula : FregeArithmetic.Formula :=
  .conjunction zeroDefinition
    (.conjunction naturalDefinition (.conjunction (predecessionAt 1 0) applicationDefinition))

structure CanonicalData (M : FregeArithmetic.Interpretation D R)
    (N : R 0) (G : R 2) (z k : D) : Prop where
  zero : ∃ E : R 0, (∀ x, ¬ member M E x) ∧ z = M.number E
  natural : ∀ x, member M N x ↔ Ancestral M z x
  tag : Precedes M z k
  application : ∀ f x y,
    M.satisfies 2 G (FregeArithmeticDefinable.three f x y) ↔
      ApplicationRelation M k z f x y

theorem zero_definition_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) :
    zeroDefinition.truth M o r ↔ ∃ E : R 0, (∀ x, ¬ member M E x) ∧ o 1 = M.number E := by
  simp [zeroDefinition, FregeArithmetic.Formula.truth, notFormula, unary,
    FregeArithmetic.Term.value, pushPredicate, pushObject, member]

theorem natural_definition_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) :
    naturalDefinition.truth M o r ↔ ∀ x, member M (r 0 0) x ↔ Ancestral M (o 1) x := by
  simp only [naturalDefinition, FregeArithmetic.Formula.truth, iff_formula_truth,
    ancestral_at_truth, unary, FregeArithmetic.Term.value, pushObject, member]

theorem application_definition_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) :
    applicationDefinition.truth M o r ↔ ∀ f x y,
      M.satisfies 2 (r 2 0) (FregeArithmeticDefinable.three f x y) ↔
        ApplicationRelation M (o 0) (o 1) f x y := by
  simp only [applicationDefinition, FregeArithmetic.Formula.truth, iff_formula_truth,
    FregeArithmeticDefinable.graph_atom_truth, application_at_truth, pushObject]

theorem data_formula_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) :
    dataFormula.truth M o r ↔ CanonicalData M (r 0 0) (r 2 0) (o 1) (o 0) := by
  simp only [dataFormula, FregeArithmetic.Formula.truth, zero_definition_truth,
    natural_definition_truth, predecession_at_truth, application_definition_truth]
  exact ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩,
    fun h => ⟨h.zero, h.natural, h.tag, h.application⟩⟩

theorem CanonicalData.zero_eq (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) {N : R 0} {G : R 2} {z k : D}
    (data : CanonicalData M N G z k) : z = FregeArithmetic.zero M full.comprehension := by
  obtain ⟨E, empty, same⟩ := data.zero
  exact same.trans ((number_zero_iff_empty M full E).mpr empty)

theorem CanonicalData.natural_iff (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) {N : R 0} {G : R 2} {z k : D}
    (data : CanonicalData M N G z k) (x : D) :
    member M N x ↔ Natural M full.comprehension x := by
  rw [data.natural x, data.zero_eq M full]
  rfl

theorem CanonicalData.tag_eq (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) {N : R 0} {G : R 2} {z k : D}
    (data : CanonicalData M N G z k) :
    k = (FregeArithmeticRecursion.successor M full (FregeArithmeticRecursion.zero M full)).val := by
  apply (FregeArithmeticRecursion.predecession_iff_successor_value M full
    (FregeArithmeticRecursion.zero M full) k).mp
  change Precedes M (FregeArithmetic.zero M full.comprehension) k
  simpa only [data.zero_eq M full] using data.tag

/-- The auxiliary data exist with the canonical Frege number representative.
The graph is supplied by the displayed source formula on the entire source
domain, and on Frege numbers it is exactly the recursion model's application. -/
theorem canonical_data_exists (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) :
    ∃ G : R 2,
      CanonicalData M (FregeArithmeticRecursion.naturalPredicate M full) G
        (FregeArithmeticRecursion.zero M full).val
        (FregeArithmeticRecursion.successor M full (FregeArithmeticRecursion.zero M full)).val ∧
      FregeArithmeticDefinable.GraphsApplication M
        (FregeArithmeticRecursion.naturalPredicate M full)
        (FregeArithmeticRecursion.model M full).apply G := by
  classical
  let z := FregeArithmeticRecursion.zero M full
  let k := FregeArithmeticRecursion.successor M full z
  let o := pushObject (fun _ => z.val) k.val
  let r := basePredicates M full.comprehension
  obtain ⟨G, represents⟩ := full.comprehension.comprehend 2 (applicationAt 0 1 2 3 4) o r
  have law (f x y : D) : M.satisfies 2 G (FregeArithmeticDefinable.three f x y) ↔
      ApplicationRelation M k.val z.val f x y := by
    exact (represents (FregeArithmeticDefinable.three f x y)).trans
      (application_at_truth M _ r 0 1 2 3 4)
  refine ⟨G, ?_, ?_⟩
  · exact ⟨⟨emptyPredicate M full.comprehension, empty_predicate M full.comprehension, rfl⟩,
      FregeArithmeticRecursion.natural_predicate_truth M full,
      FregeArithmeticRecursion.successor_precedes M full z, law⟩
  · intro f x y
    rw [law, ApplicationRelation, FregeArithmeticRecursion.predecession_iff_successor_value]
    by_cases same : f = k
    · simp [FregeArithmeticRecursion.model, FregeArithmeticAdapter.interpretation, same, k, z]
    · have vals : f.val ≠ k.val := fun eq => same (Subtype.ext eq)
      simp [FregeArithmeticRecursion.model, FregeArithmeticAdapter.interpretation, same, vals, k, z]

end FregeanECA.Part2.FregeArithmeticData
