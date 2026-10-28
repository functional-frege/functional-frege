import FregeanECA.Part2.HumeCounting
import FregeanECA.Part2.Theorems

/-! Internal cardinal abstraction on the interpreted arithmetic domain.
Finite size is expressed by an AVAILABLE bijection to an internal initial
segment. This module uses the actual object/relation formula grammar.
-/

namespace FregeanECA.Part2.HumeInternal
open Positive Arithmetic HumeOrder HumeFinite HumeBijections
universe u v
variable {D : Type u} {R : Nat → Type v}

def Code (M : Interpretation D R) (N P : R 0) (a : D) : Prop :=
  (∃ n, FiniteSize M N P n ∧ a = modelSuccessor M n) ∨
    (a = modelZero M ∧ ¬ ∃ n, FiniteSize M N P n)

theorem code_total_unique (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (P : R 0) : ∃! a, Code M N P a := by
  classical
  by_cases finite : ∃ n, FiniteSize M N P n
  · obtain ⟨n, hn⟩ := finite
    refine ⟨modelSuccessor M n, Or.inl ⟨n, hn, rfl⟩, ?_⟩
    intro a ha
    rcases ha with ⟨m, hm, same⟩ | ⟨_, impossible⟩
    · exact same.trans (congrArg (modelSuccessor M) (finite_size_unique M full domain hm hn))
    · exact False.elim (impossible ⟨n, hn⟩)
  · refine ⟨modelZero M, Or.inr ⟨rfl, finite⟩, ?_⟩
    intro a ha
    rcases ha with ⟨n, hn, _⟩ | ⟨same, _⟩
    · exact False.elim (finite ⟨n, hn⟩)
    · exact same

theorem code_natural (M : Interpretation D R) {N P : R 0}
    (domain : PeanoDomain M N) {a : D} (h : Code M N P a) : member M N a := by
  rcases h with ⟨n, hn, rfl⟩ | ⟨rfl, _⟩
  · exact domain.successor_closed n hn.1
  · exact domain.zero_member

theorem equinumerous_same_code (M : Interpretation D R) (full : HasFullComprehension M)
    {N P Q : R 0} (domain : PeanoDomain M N) (eqv : Equinumerous M N P Q)
    {a b : D} (ha : Code M N P a) (hb : Code M N Q b) : a = b := by
  rcases ha with ⟨n, pn, rfl⟩ | ⟨rfl, pinf⟩
  · rcases hb with ⟨m, qm, rfl⟩ | ⟨_, qinf⟩
    · exact congrArg (modelSuccessor M)
        (finite_size_unique M full domain pn (equinumerous_preserves_size M full eqv qm))
    · exact False.elim (qinf ⟨n,
        equinumerous_preserves_size M full (equinumerous_symm M full eqv) pn⟩)
  · rcases hb with ⟨m, qm, _⟩ | ⟨rfl, _⟩
    · exact False.elim (pinf ⟨m, equinumerous_preserves_size M full eqv qm⟩)
    · rfl

/-- The order formula with arbitrary term arguments; its only predicate
quantifier is fresh and binds the inductive predicate internally. -/
def leAt (x y : Positive.Term) : Applicative.Formula :=
  .forallPredicate 0 (.implies
    (.conjunction (unary 0 x)
      (.forallObject (.implies (unary 0 (.var 0))
        (unary 0 (successorTerm (.var 0)))))) (unary 0 y))

theorem le_at_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (x y : Positive.Term) :
    (leAt x y).truth M o r ↔ Le M (x.value M o) (y.value M o) := by
  simp only [leAt, Applicative.Formula.truth, unary, successorTerm,
    Positive.Term.value, pushPredicate, pushObject, Le, member, modelSuccessor,
    dite_true, and_imp]

def onNumbersAt (natural predicate : Nat) (x : Positive.Term) : Applicative.Formula :=
  .conjunction (unary natural x) (unary predicate x)

def segmentAt (natural : Nat) (n x : Positive.Term) : Applicative.Formula :=
  .conjunction (unary natural x) (.conjunction (leAt x n) (notEqual x n))

theorem on_numbers_at_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (natural predicate : Nat) (x : Positive.Term) :
    (onNumbersAt natural predicate x).truth M o r ↔
      OnNumbers M (r 0 natural) (r 0 predicate) (x.value M o) := Iff.rfl

theorem segment_at_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (natural : Nat) (n x : Positive.Term) :
    (segmentAt natural n x).truth M o r ↔
      InSegment M (r 0 natural) (n.value M o) (x.value M o) := by
  simp only [segmentAt, Applicative.Formula.truth, unary, le_at_truth,
    notEqual, member, InSegment, Lt]

def functionalGraphFormula : Applicative.Formula :=
  .forallObject (.forallObject (.forallObject
    (.implies (.conjunction (binary 0 (.var 2) (.var 1)) (binary 0 (.var 2) (.var 0)))
      (.equal (.var 1) (.var 0)))))

def injectiveGraphFormula : Applicative.Formula :=
  .forallObject (.forallObject (.forallObject
    (.implies (.conjunction (binary 0 (.var 2) (.var 0)) (binary 0 (.var 1) (.var 0)))
      (.equal (.var 2) (.var 1)))))

theorem functional_graph_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) : functionalGraphFormula.truth M o r ↔
      ∀ x y z, member2 M (r 1 0) x y → member2 M (r 1 0) x z → y = z := by
  simp only [functionalGraphFormula, Applicative.Formula.truth, binary_truth,
    Positive.Term.value, pushObject, and_imp]

theorem injective_graph_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) : injectiveGraphFormula.truth M o r ↔
      ∀ x y z, member2 M (r 1 0) x z → member2 M (r 1 0) y z → x = y := by
  simp only [injectiveGraphFormula, Applicative.Formula.truth, binary_truth,
    Positive.Term.value, pushObject, and_imp]

/-- The sole free object is the finite bound n. The graph is binary predicate zero. -/
def finiteBijectionFormula (natural predicate : Nat) : Applicative.Formula :=
  .conjunction
    (.forallObject (.forallObject (.implies (binary 0 (.var 1) (.var 0))
      (.conjunction (onNumbersAt natural predicate (.var 1))
        (segmentAt natural (.var 2) (.var 0))))))
    (.conjunction
      (.forallObject (.implies (onNumbersAt natural predicate (.var 0))
        (.existsObject (binary 0 (.var 1) (.var 0)))))
      (.conjunction
        (.forallObject (.implies (segmentAt natural (.var 1) (.var 0))
          (.existsObject (binary 0 (.var 0) (.var 1)))))
        (.conjunction functionalGraphFormula injectiveGraphFormula)))

theorem finite_bijection_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (natural predicate : Nat) :
    (finiteBijectionFormula natural predicate).truth M o r ↔
      GraphBijection M (OnNumbers M (r 0 natural) (r 0 predicate))
        (InSegment M (r 0 natural) (o 0)) (r 1 0) := by
  simp only [finiteBijectionFormula, Applicative.Formula.truth, binary_truth,
    on_numbers_at_truth, segment_at_truth, functional_graph_formula_truth,
    injective_graph_formula_truth, Positive.Term.value, pushObject, and_imp]
  exact ⟨fun ⟨hs, ht, ho, hf, hi⟩ => ⟨hs, ht, ho, hf, hi⟩,
    fun h => ⟨h.support, h.total, h.onto, h.functional, h.injective⟩⟩

def finiteSizeFormula (natural predicate : Nat) : Applicative.Formula :=
  .conjunction (unary natural (.var 0))
    (.existsPredicate 1 (finiteBijectionFormula natural predicate))

theorem finite_size_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (natural predicate : Nat) :
    (finiteSizeFormula natural predicate).truth M o r ↔
      FiniteSize M (r 0 natural) (r 0 predicate) (o 0) := by
  simp only [finiteSizeFormula, Applicative.Formula.truth, unary,
    finite_bijection_formula_truth, Positive.Term.value, FiniteSize, member]
  simp [pushPredicate]

def shiftTerm : Positive.Term → Positive.Term
  | .var i => .var (i + 1)
  | .constantK => .constantK
  | .constantS => .constantS
  | .app s t => .app (shiftTerm s) (shiftTerm t)

theorem shift_term_value (M : Interpretation D R) (o : ObjectAssignment D) (a : D)
    (t : Positive.Term) : (shiftTerm t).value M (pushObject o a) = t.value M o := by
  induction t with
  | var i => rfl
  | constantK => rfl
  | constantS => rfl
  | app s t hs ht => change M.apply _ _ = M.apply _ _; rw [hs, ht]

def codeFormula (natural predicate : Nat) (a : Positive.Term) : Applicative.Formula :=
  .disjunction
    (.existsObject (.conjunction (finiteSizeFormula natural predicate)
      (.equal (shiftTerm a) (successorTerm (.var 0)))))
    (.conjunction (.equal a zeroTerm)
      (.implies (.existsObject (finiteSizeFormula natural predicate)) .falsum))

theorem code_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (natural predicate : Nat) (a : Positive.Term) :
    (codeFormula natural predicate a).truth M o r ↔
      Code M (r 0 natural) (r 0 predicate) (a.value M o) := by
  simp only [codeFormula, Applicative.Formula.truth, finite_size_formula_truth,
    shift_term_value, successorTerm, zeroTerm, Positive.Term.value,
    pushObject, modelSuccessor, modelZero, Code]

theorem not_finite_enumerable (M : Interpretation D R) (full : HasFullComprehension M)
    {N P : R 0} (domain : PeanoDomain M N) (infinite : ¬ ∃ n, FiniteSize M N P n) :
    ∃ G : R 1, GraphBijection M (OnNumbers M N P) (member M N) G := by
  rcases HumeCounting.predicate_cardinality_cases M full domain P with finite | enumeration
  · exact False.elim (infinite finite)
  · exact enumeration

/-- Hume's Principle on the interpreted arithmetic domain in EVERY full
Henkin model. Neither graph availability nor cardinal classification is a
premise: both were proved from the actual comprehension scheme. -/
theorem humes_principle (M : Interpretation D R) (full : HasFullComprehension M)
    {N P Q : R 0} (domain : PeanoDomain M N) {a b : D}
    (ha : Code M N P a) (hb : Code M N Q b) :
    a = b ↔ Equinumerous M N P Q := by
  constructor
  · intro same
    rcases ha with ⟨n, pn, rfl⟩ | ⟨rfl, pinf⟩
    · rcases hb with ⟨m, qm, rfl⟩ | ⟨rfl, _⟩
      · have nm := domain.successor_injective n m same
        subst m
        exact same_size_equinumerous M full pn qm
      · exact False.elim (domain.zero_not_successor n same.symm)
    · rcases hb with ⟨m, _, rfl⟩ | ⟨rfl, qinf⟩
      · exact False.elim (domain.zero_not_successor m same)
      · obtain ⟨G, pg⟩ := not_finite_enumerable M full domain pinf
        obtain ⟨H, qh⟩ := not_finite_enumerable M full domain qinf
        obtain ⟨I, ih⟩ := inverse M full qh
        exact compose M full pg ih
  · intro eqv
    exact equinumerous_same_code M full domain eqv ha hb

def equinumerousBijectionFormula (natural left right : Nat) : Applicative.Formula :=
  .conjunction
    (.forallObject (.forallObject (.implies (binary 0 (.var 1) (.var 0))
      (.conjunction (onNumbersAt natural left (.var 1))
        (onNumbersAt natural right (.var 0))))))
    (.conjunction
      (.forallObject (.implies (onNumbersAt natural left (.var 0))
        (.existsObject (binary 0 (.var 1) (.var 0)))))
      (.conjunction
        (.forallObject (.implies (onNumbersAt natural right (.var 0))
          (.existsObject (binary 0 (.var 0) (.var 1)))))
        (.conjunction functionalGraphFormula injectiveGraphFormula)))

theorem equinumerous_bijection_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (natural left right : Nat) :
    (equinumerousBijectionFormula natural left right).truth M o r ↔
      GraphBijection M (OnNumbers M (r 0 natural) (r 0 left))
        (OnNumbers M (r 0 natural) (r 0 right)) (r 1 0) := by
  simp only [equinumerousBijectionFormula, Applicative.Formula.truth, binary_truth,
    on_numbers_at_truth, functional_graph_formula_truth, injective_graph_formula_truth,
    Positive.Term.value, pushObject]
  exact ⟨fun ⟨hs, ht, ho, hf, hi⟩ => ⟨hs, ht, ho, hf, hi⟩,
    fun h => ⟨h.support, h.total, h.onto, h.functional, h.injective⟩⟩

def equinumerousFormula (natural left right : Nat) : Applicative.Formula :=
  .existsPredicate 1 (equinumerousBijectionFormula natural left right)

theorem equinumerous_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (natural left right : Nat) :
    (equinumerousFormula natural left right).truth M o r ↔
      Equinumerous M (r 0 natural) (r 0 left) (r 0 right) := by
  simp [equinumerousFormula, Applicative.Formula.truth,
    equinumerous_bijection_formula_truth, pushPredicate, Equinumerous]

def iffFormula (p q : Applicative.Formula) : Applicative.Formula :=
  .conjunction (.implies p q) (.implies q p)

theorem iff_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (p q : Applicative.Formula) :
    (iffFormula p q).truth M o r ↔ (p.truth M o r ↔ q.truth M o r) := by
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

/-- N is unary predicate zero. All P,Q and candidate abstract values are
quantified in the actual target language. -/
def humePrincipleFormula : Applicative.Formula :=
  .forallPredicate 0 (.forallPredicate 0 (.forallObject (.forallObject
    (.implies (.conjunction (codeFormula 2 1 (.var 1)) (codeFormula 2 0 (.var 0)))
      (iffFormula (.equal (.var 1) (.var 0)) (equinumerousFormula 2 1 0))))))

theorem hume_principle_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) : humePrincipleFormula.truth M o r ↔
      ∀ P Q : R 0, ∀ a b : D, Code M (r 0 0) P a → Code M (r 0 0) Q b →
        (a = b ↔ Equinumerous M (r 0 0) P Q) := by
  simp only [humePrincipleFormula, Applicative.Formula.truth, code_formula_truth,
    iff_formula_truth, equinumerous_formula_truth, Positive.Term.value, pushObject, and_imp]
  simp [pushPredicate]

def uniqueCodeFormula : Applicative.Formula :=
  .forallPredicate 0 (.existsObject (.conjunction (codeFormula 1 0 (.var 0))
    (.forallObject (.implies (codeFormula 1 0 (.var 0)) (.equal (.var 0) (.var 1))))))

theorem unique_code_formula_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) : uniqueCodeFormula.truth M o r ↔
      ∀ P : R 0, ∃! a, Code M (r 0 0) P a := by
  simp only [uniqueCodeFormula, Applicative.Formula.truth, code_formula_truth,
    Positive.Term.value, pushObject, ExistsUnique]
  simp [pushPredicate]

/-- Both the unique existence of the abstraction's value and HP itself are
true as literal formulas in any full model with the derived Peano domain. -/
theorem internal_hume_formulas (M : Interpretation D R) (full : HasFullComprehension M)
    {N : R 0} (domain : PeanoDomain M N) (o : ObjectAssignment D)
    (r : PredicateAssignment R) (namesNatural : r 0 0 = N) :
    uniqueCodeFormula.truth M o r ∧ humePrincipleFormula.truth M o r := by
  constructor
  · apply (unique_code_formula_truth M o r).mpr
    rw [namesNatural]
    exact code_total_unique M full domain
  · apply (hume_principle_formula_truth M o r).mpr
    rw [namesNatural]
    intro P Q a b ha hb
    exact humes_principle M full domain ha hb

/-- The canonical least-inductive-domain definition, in the target syntax. -/
def naturalDefinition : Applicative.Formula :=
  .forallObject (iffFormula (unary 0 (.var 0)) leastInductiveFormula)

theorem natural_definition_truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) : naturalDefinition.truth M o r ↔
      RepresentsLeast M (r 0 0) := by
  simp only [naturalDefinition, Applicative.Formula.truth, iff_formula_truth,
    least_inductive_formula_truth, unary, Positive.Term.value, pushObject,
    RepresentsLeast, member]

/-- Closed target-language assertion: the canonical number domain exists,
every available predicate has a unique abstract value, and those values obey HP. -/
def internalHumeSentence : Applicative.Formula :=
  .existsPredicate 0 (.conjunction naturalDefinition
    (.conjunction uniqueCodeFormula humePrincipleFormula))

theorem internal_hume_sentence_valid (M : Interpretation D R) (full : FullTSConditions M)
    (o : ObjectAssignment D) (r : PredicateAssignment R) :
    internalHumeSentence.truth M o r := by
  obtain ⟨N, domain⟩ := full_ts_has_peano_domain M full
  change ∃ N : R 0, _
  refine ⟨N, ?_, ?_⟩
  · exact (natural_definition_truth M o (pushPredicate r 0 N)).mpr domain.represents_least
  · exact internal_hume_formulas M full.full_comprehension domain o (pushPredicate r 0 N) rfl

open FFL FFL.FirstOrder
open scoped FFL.FirstOrder

/-- An actual Foundation sequent-calculus theorem of Part II, with no model
or arithmetic-validity premise. The proof does not use Z2 proof transfer. -/
theorem internal_hume_provable :
    fullAlgebraTheory ⊢ Guarded.sentence internalHumeSentence.functional := by
  apply Theory.Proof.complete_on_eq_models.{0, 0}
  intro M _ _ _ hM
  have := Encoded.sorts_of_model hM
  let native := Guarded.extracted M
  have full : FullTSConditions native.applicative :=
    (algebra_axioms_iff_conditions native).mp
      ((Encoded.model_iff_valid (Guarded.extractedRealization M) AlgebraAxiom).mp hM)
  apply (Guarded.sentence_truth (Guarded.extractedRealization M)
    inferInstance (fun _ => inferInstance) internalHumeSentence.functional).mpr
  intro objects functions predicates
  exact (shared_formula_preserves_truth native internalHumeSentence objects functions predicates).mpr
    (internal_hume_sentence_valid native.applicative full objects predicates)

theorem internal_hume_provable_fregean :
    fullFunctionalTheory ⊢ Guarded.sentence internalHumeSentence.functional :=
  (full_functional_algebra_provability internalHumeSentence).mpr internal_hume_provable

/-- An expanded graph language: the new atom says that a predicate's abstract
value is the given object term. Arbitrary classical combinations and nested
object/predicate quantifiers are included. Number-function terms can be
eliminated using their unique graph witnesses; no such source calculus is
silently identified with this syntax. -/
inductive ExpandedFormula where
  | ordinary (formula : Applicative.Formula)
  | abstraction (natural predicate : Nat) (output : Positive.Term)
  | implies (left right : ExpandedFormula)
  | conjunction (left right : ExpandedFormula)
  | disjunction (left right : ExpandedFormula)
  | existsObject (body : ExpandedFormula)
  | forallObject (body : ExpandedFormula)
  | existsPredicate (arity : Nat) (body : ExpandedFormula)
  | forallPredicate (arity : Nat) (body : ExpandedFormula)

def ExpandedFormula.eliminate : ExpandedFormula → Applicative.Formula
  | .ordinary p => p
  | .abstraction n p a => codeFormula n p a
  | .implies p q => .implies p.eliminate q.eliminate
  | .conjunction p q => .conjunction p.eliminate q.eliminate
  | .disjunction p q => .disjunction p.eliminate q.eliminate
  | .existsObject p => .existsObject p.eliminate
  | .forallObject p => .forallObject p.eliminate
  | .existsPredicate n p => .existsPredicate n p.eliminate
  | .forallPredicate n p => .forallPredicate n p.eliminate

def ExpandedFormula.truth (M : Interpretation D R) (o : ObjectAssignment D)
    (r : PredicateAssignment R) : ExpandedFormula → Prop
  | .ordinary p => p.truth M o r
  | .abstraction n p a => Code M (r 0 n) (r 0 p) (a.value M o)
  | .implies p q => p.truth M o r → q.truth M o r
  | .conjunction p q => p.truth M o r ∧ q.truth M o r
  | .disjunction p q => p.truth M o r ∨ q.truth M o r
  | .existsObject p => ∃ x, p.truth M (pushObject o x) r
  | .forallObject p => ∀ x, p.truth M (pushObject o x) r
  | .existsPredicate n p => ∃ P : R n, p.truth M o (pushPredicate r n P)
  | .forallPredicate n p => ∀ P : R n, p.truth M o (pushPredicate r n P)

theorem ExpandedFormula.eliminate_truth (M : Interpretation D R) (p : ExpandedFormula) :
    ∀ o r, p.eliminate.truth M o r ↔ p.truth M o r := by
  induction p with
  | ordinary p => intros; exact Iff.rfl
  | abstraction n p a => intros; exact code_formula_truth M _ _ n p a
  | implies p q ihp ihq => intros; exact imp_congr (ihp _ _) (ihq _ _)
  | conjunction p q ihp ihq => intros; exact and_congr (ihp _ _) (ihq _ _)
  | disjunction p q ihp ihq => intros; exact or_congr (ihp _ _) (ihq _ _)
  | existsObject p ih => intros; exact exists_congr (fun _ => ih _ _)
  | forallObject p ih => intros; exact forall_congr' (fun _ => ih _ _)
  | existsPredicate n p ih => intros; exact exists_congr (fun _ => ih _ _)
  | forallPredicate n p ih => intros; exact forall_congr' (fun _ => ih _ _)

/-- Full comprehension is preserved after adding the defined abstraction
graph, including bodies with nested abstraction atoms and predicate binders.
This proves every expanded-language semantic comprehension instance. A
translation of arbitrary proofs from a separately specified HP calculus is
a distinct further interface, not asserted by this theorem. -/
theorem expanded_comprehension (M : Interpretation D R) (full : HasFullComprehension M)
    (arity : Nat) (p : ExpandedFormula) (o : ObjectAssignment D)
    (r : PredicateAssignment R) :
    ∃ P : R arity, ∀ xs, M.satisfies arity P xs ↔
      p.truth M (assignTuple (arity + 1) xs o) r := by
  obtain ⟨P, law⟩ := full.comprehend arity p.eliminate o r
  exact ⟨P, fun xs => (law xs).trans (p.eliminate_truth M _ _)⟩

end FregeanECA.Part2.HumeInternal
