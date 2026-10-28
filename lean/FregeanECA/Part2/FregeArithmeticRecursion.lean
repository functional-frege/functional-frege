import FregeanECA.Part2.FregeArithmeticAdapter
import FregeanECA.Part2.FregeArithmeticTheorem
import FregeanECA.Part2.FregeArithmeticDefinable

/-! The standard HP-derived number carrier supplies the generic recursion
interface. This file does not use the earlier ECA-derived Peano domain or
Z2 proof transfer. Full comprehension for its artificial application must be
transported separately through an actual source-formula translation. -/

namespace FregeanECA.Part2.FregeArithmeticRecursion
open Positive


universe u v
variable {D : Type u} {R : Nat → Type v}

noncomputable def naturalPredicate (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) : R 0 :=
  Classical.choose (FregeArithmetic.full_has_natural M full.comprehension)

theorem natural_predicate_truth (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) (x : D) :
    FregeArithmetic.member M (naturalPredicate M full) x ↔ FregeArithmetic.Natural M full.comprehension x :=
  Classical.choose_spec (FregeArithmetic.full_has_natural M full.comprehension) x

abbrev Carrier (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) :=
  {x : D // FregeArithmetic.member M (naturalPredicate M full) x}

noncomputable def zero (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) : Carrier M full :=
  ⟨FregeArithmetic.zero M full.comprehension, (natural_predicate_truth M full _).mpr
    (FregeArithmetic.hume_implies_frege_peano M full).zero_natural⟩

noncomputable def successor (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (x : Carrier M full) : Carrier M full := by
  let laws := FregeArithmetic.hume_implies_frege_peano M full
  have nx := (natural_predicate_truth M full x.val).mp x.property
  let y := Classical.choose (laws.successor_exists x.val nx)
  have next : FregeArithmetic.Precedes M x.val y := Classical.choose_spec (laws.successor_exists x.val nx)
  exact ⟨y, (natural_predicate_truth M full y).mpr (laws.successor_closed _ _ nx next)⟩

theorem successor_precedes (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (x : Carrier M full) : FregeArithmetic.Precedes M x.val (successor M full x).val :=
  Classical.choose_spec ((FregeArithmetic.hume_implies_frege_peano M full).successor_exists
    x.val ((natural_predicate_truth M full x.val).mp x.property))

theorem zero_not_successor (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (x : Carrier M full) : zero M full ≠ successor M full x := by
  intro same
  have next := successor_precedes M full x
  have equalValues := congrArg Subtype.val same
  rw [← equalValues] at next
  exact (FregeArithmetic.hume_implies_frege_peano M full).zero_has_no_predecessor x.val
    ((natural_predicate_truth M full x.val).mp x.property) next

theorem successor_injective (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) :
    Function.Injective (successor M full) := by
  intro x y same
  apply Subtype.ext
  have nextY := successor_precedes M full y
  rw [← same] at nextY
  exact (FregeArithmetic.hume_implies_frege_peano M full).predecessor_unique _ _ _
    ((natural_predicate_truth M full x.val).mp x.property)
    ((natural_predicate_truth M full y.val).mp y.property)
    (successor_precedes M full x) nextY

def satisfies (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (arity : Nat) (P : R arity) (xs : Fin (arity + 1) → Carrier M full) : Prop :=
  M.satisfies arity P (fun i => (xs i).val)

theorem available_induction (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M)
    (P : R 0) (base : satisfies M full 0 P (fun _ => zero M full))
    (step : ∀ x, satisfies M full 0 P (fun _ => x) →
      satisfies M full 0 P (fun _ => successor M full x)) :
    ∀ x, satisfies M full 0 P (fun _ => x) := by
  have laws := FregeArithmetic.hume_implies_frege_peano M full
  intro a
  apply laws.induction P base ?_ a.val
    ((natural_predicate_truth M full a.val).mp a.property)
  intro x y nx px next
  let a : Carrier M full := ⟨x, (natural_predicate_truth M full x).mpr nx⟩
  have sy : (successor M full a).val = y :=
    laws.successor_unique _ _ _ nx (successor_precedes M full a) next
  have out := step a px
  change FregeArithmetic.member M P (successor M full a).val at out
  simpa only [sy] using out

noncomputable def model (M : FregeArithmetic.Interpretation D R) (full : FregeArithmetic.FullConditions M) :
    Positive.Interpretation (Carrier M full) R :=
  FregeArithmeticAdapter.interpretation (satisfies M full) (zero M full)
    (successor M full (zero M full)) (successor M full)

/-- All remaining Peano and recursion premises are derived from generic HP.
The only separate obligation is full comprehension for the defined adapter. -/
theorem arithmetic_of_adapter_comprehension (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) (comprehension : HasFullComprehension (model M full)) :
    Nonempty (Arithmetic.FullArithmetic (model M full) (naturalPredicate M full)) :=
  FregeArithmeticAdapter.arithmetic_on_inductive_carrier (satisfies M full) (zero M full)
    (successor M full (zero M full)) (successor M full)
    (Ne.symm (zero_not_successor M full (zero M full))) comprehension
    (naturalPredicate M full) (fun x => x.property) (available_induction M full)
    (zero_not_successor M full) (successor_injective M full)

theorem predecession_iff_successor_value (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) (x : Carrier M full) (y : D) :
    FregeArithmetic.Precedes M x.val y ↔ y = (successor M full x).val := by
  constructor
  · intro next
    exact FregeArithmetic.predecession_functional M full next (successor_precedes M full x)
  · intro same
    rw [same]
    exact successor_precedes M full x

/-- The adapter's application is definable from the available predecession
graph and the two object parameters. Its argument and result variables occupy
slots 0, 1, 2; the tag and zero parameters occupy slots 3, 4. -/
def applicationFormula : FregeArithmetic.Formula :=
  .disjunction
    (.conjunction (.equal (.var 0) (.var 3)) (FregeArithmetic.binary 0 (.var 1) (.var 2)))
    (.conjunction (FregeArithmetic.notFormula (.equal (.var 0) (.var 3)))
      (.equal (.var 2) (.var 4)))

/-- Every comprehension instance for the auxiliary recursion language is
translated into an actual source-language instance. No comprehension for
arbitrary external predicates is assumed. -/
theorem model_has_full_comprehension (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) : HasFullComprehension (model M full) := by
  classical
  let k := successor M full (zero M full)
  let z := zero M full
  obtain ⟨G, graph⟩ := FregeArithmetic.full_has_predecession M full.comprehension
  let o := pushObject (fun _ => z.val) k.val
  let r := pushPredicate (FregeArithmetic.basePredicates M full.comprehension) 1 G
  apply FregeArithmeticDefinable.full_comprehension_of_formula M (naturalPredicate M full)
    (model M full).apply k z full.comprehension applicationFormula o r
  intro x y output
  have truth : applicationFormula.truth M
      (assignTuple 3 (FregeArithmeticDefinable.three x.val y.val output) o) r ↔
      (x.val = k.val ∧ FregeArithmetic.Precedes M y.val output) ∨
      (x.val ≠ k.val ∧ output = z.val) := by
    simp only [applicationFormula, FregeArithmetic.Formula.truth,
      FregeArithmetic.binary_truth, FregeArithmetic.notFormula,
      FregeArithmetic.Term.value, assignTuple, pushObject,
      FregeArithmeticDefinable.three, Fin.cases_zero, Fin.cases_succ,
      o, r, pushPredicate, dite_true, graph]
  rw [truth, predecession_iff_successor_value]
  by_cases same : x = k
  · simp [model, FregeArithmeticAdapter.interpretation, same, k]
  · have vals : x.val ≠ k.val := fun eq => same (Subtype.ext eq)
    simp [model, FregeArithmeticAdapter.interpretation, same, vals, k, z]

/-- Full second-order arithmetic on the standard Frege number domain,
constructed from HP and full source comprehension alone. -/
theorem hume_supplies_arithmetic (M : FregeArithmetic.Interpretation D R)
    (full : FregeArithmetic.FullConditions M) :
    Nonempty (Arithmetic.FullArithmetic (model M full) (naturalPredicate M full)) :=
  arithmetic_of_adapter_comprehension M full (model_has_full_comprehension M full)

end FregeanECA.Part2.FregeArithmeticRecursion

