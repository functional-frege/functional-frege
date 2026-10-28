import FregeanECA.Syntax
import FregeanECA.Model
import FregeanECA.Comprehension

namespace FregeanECA.Functional
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- The assignment correspondence explicitly states where both source sorts
are located in the single target object-variable stack. -/
structure Bindings (M : Interpretation D F R) (om fm : Nat → Nat)
    (objects : Nat → D) (functions : Nat → F) (target : Nat → D) : Prop where
  object : ∀ i, target (om i) = objects i
  function : ∀ i, target (fm i) = M.delta (functions i)

theorem Bindings.objectBinder {M : Interpretation D F R} {om fm : Nat → Nat}
    {objects : Nat → D} {functions : Nat → F} {target : Nat → D}
    (h : Bindings M om fm objects functions target) (x : D) :
    Bindings M (bindMap om) (shiftMap fm) (Positive.pushObject objects x)
      functions (Positive.pushObject target x) where
  object := by intro i; cases i with | zero => rfl | succ i => exact h.object i
  function := h.function

theorem Bindings.functionBinder {M : Interpretation D F R} {om fm : Nat → Nat}
    {objects : Nat → D} {functions : Nat → F} {target : Nat → D}
    (h : Bindings M om fm objects functions target) (f : F) :
    Bindings M (shiftMap om) (bindMap fm) objects (Positive.pushObject functions f)
      (Positive.pushObject target (M.delta f)) where
  object := h.object
  function := by intro i; cases i with | zero => rfl | succ i => exact h.function i

theorem term_translation_preserves_value (M : Interpretation D F R)
    (evaluation : ∀ f x, M.eval f x = M.applicative.apply (M.delta f) x)
    (term : Term) (om fm : Nat → Nat) (objects : Nat → D) (functions : Nat → F)
    (target : Nat → D) (bindings : Bindings M om fm objects functions target) :
    term.value M objects functions = (term.translate om fm).value M.applicative target := by
  induction term with
  | var i => exact (bindings.object i).symm
  | constantK => rfl
  | constantS => rfl
  | app f x hf hx => simp only [Term.value, Term.translate, Positive.Term.value, hf, hx]
  | eval f x hx =>
      simp only [Term.value, Term.translate, Positive.Term.value, bindings.function, evaluation, hx]
  | delta f => exact (bindings.function f).symm

/-- Removing the function sort preserves every positive formula. Coverage is
sufficient: injectivity of representation is not used. -/
theorem positive_translation_preserves_truth (M : Interpretation D F R)
    (evaluation : ∀ f x, M.eval f x = M.applicative.apply (M.delta f) x)
    (coverage : ∀ a, ∃ f, M.delta f = a) (formula : PositiveFormula) :
    ∀ (om fm : Nat → Nat) (objects : Nat → D) (functions : Nat → F)
      (target : Nat → D) (predicates : Positive.PredicateAssignment R),
      Bindings M om fm objects functions target →
      (formula.truth M objects functions predicates ↔
        (formula.translate om fm).truth M.applicative target predicates) := by
  induction formula with
  | equal left right =>
      intro om fm objects functions target predicates bindings
      simp only [PositiveFormula.truth, PositiveFormula.translate, Positive.Formula.truth,
        term_translation_preserves_value M evaluation _ om fm objects functions target bindings]
  | relation arity index arguments =>
      intro om fm objects functions target predicates bindings
      simp only [PositiveFormula.truth, PositiveFormula.translate, Positive.Formula.truth,
        term_translation_preserves_value M evaluation _ om fm objects functions target bindings]
  | conjunction left right hl hr =>
      intro om fm objects functions target predicates bindings
      exact and_congr (hl _ _ _ _ _ _ bindings) (hr _ _ _ _ _ _ bindings)
  | disjunction left right hl hr =>
      intro om fm objects functions target predicates bindings
      exact or_congr (hl _ _ _ _ _ _ bindings) (hr _ _ _ _ _ _ bindings)
  | existsObject body ih =>
      intro om fm objects functions target predicates bindings
      exact exists_congr (fun x => ih _ _ _ _ _ _ (bindings.objectBinder x))
  | forallObject body ih =>
      intro om fm objects functions target predicates bindings
      exact forall_congr' (fun x => ih _ _ _ _ _ _ (bindings.objectBinder x))
  | existsFunction body ih =>
      intro om fm objects functions target predicates bindings
      constructor
      · rintro ⟨f, holds⟩
        exact ⟨M.delta f, (ih _ _ _ _ _ _ (bindings.functionBinder f)).mp holds⟩
      · rintro ⟨a, holds⟩
        obtain ⟨f, rfl⟩ := coverage a
        exact ⟨f, (ih _ _ _ _ _ _ (bindings.functionBinder f)).mpr holds⟩
  | forallFunction body ih =>
      intro om fm objects functions target predicates bindings
      constructor
      · intro holds a
        obtain ⟨f, rfl⟩ := coverage a
        exact (ih _ _ _ _ _ _ (bindings.functionBinder f)).mp (holds f)
      · intro holds f
        exact (ih _ _ _ _ _ _ (bindings.functionBinder f)).mpr (holds (M.delta f))
  | existsPredicate arity body ih =>
      intro om fm objects functions target predicates bindings
      exact exists_congr (fun P => ih _ _ _ _ _ _ bindings)
  | forallPredicate arity body ih =>
      intro om fm objects functions target predicates bindings
      exact forall_congr' (fun P => ih _ _ _ _ _ _ bindings)

/-- With injectivity (equivalently FE in an A3 representation), the same
translation preserves arbitrary classical formulas, including F/R identity. -/
theorem translation_preserves_truth (M : Interpretation D F R)
    (evaluation : ∀ f x, M.eval f x = M.applicative.apply (M.delta f) x)
    (coverage : ∀ a, ∃ f, M.delta f = a)
    (injective : ∀ f g, M.delta f = M.delta g → f = g) (formula : Formula) :
    ∀ (om fm : Nat → Nat) (objects : Nat → D) (functions : Nat → F)
      (target : Nat → D) (predicates : Positive.PredicateAssignment R),
      Bindings M om fm objects functions target →
      (formula.truth M objects functions predicates ↔
        (formula.translate om fm).truth M.applicative target predicates) := by
  induction formula with
  | equal left right =>
      intro om fm objects functions target predicates bindings
      simp only [Formula.truth, Formula.translate, Applicative.Formula.truth,
        term_translation_preserves_value M evaluation _ om fm objects functions target bindings]
  | relation arity index arguments =>
      intro om fm objects functions target predicates bindings
      simp only [Formula.truth, Formula.translate, Applicative.Formula.truth,
        term_translation_preserves_value M evaluation _ om fm objects functions target bindings]
  | relationEqual arity left right => intros; exact Iff.rfl
  | functionEqual left right =>
      intro om fm objects functions target predicates bindings
      change functions left = functions right ↔ target (fm left) = target (fm right)
      rw [bindings.function, bindings.function]
      exact ⟨congrArg M.delta, injective _ _⟩
  | falsum => intros; exact Iff.rfl
  | implies left right hl hr =>
      intro om fm objects functions target predicates bindings
      exact imp_congr (hl _ _ _ _ _ _ bindings) (hr _ _ _ _ _ _ bindings)
  | conjunction left right hl hr =>
      intro om fm objects functions target predicates bindings
      exact and_congr (hl _ _ _ _ _ _ bindings) (hr _ _ _ _ _ _ bindings)
  | disjunction left right hl hr =>
      intro om fm objects functions target predicates bindings
      exact or_congr (hl _ _ _ _ _ _ bindings) (hr _ _ _ _ _ _ bindings)
  | existsObject body ih =>
      intro om fm objects functions target predicates bindings
      exact exists_congr (fun x => ih _ _ _ _ _ _ (bindings.objectBinder x))
  | forallObject body ih =>
      intro om fm objects functions target predicates bindings
      exact forall_congr' (fun x => ih _ _ _ _ _ _ (bindings.objectBinder x))
  | existsFunction body ih =>
      intro om fm objects functions target predicates bindings
      constructor
      · rintro ⟨f, holds⟩
        exact ⟨M.delta f, (ih _ _ _ _ _ _ (bindings.functionBinder f)).mp holds⟩
      · rintro ⟨a, holds⟩
        obtain ⟨f, rfl⟩ := coverage a
        exact ⟨f, (ih _ _ _ _ _ _ (bindings.functionBinder f)).mpr holds⟩
  | forallFunction body ih =>
      intro om fm objects functions target predicates bindings
      constructor
      · intro holds a
        obtain ⟨f, rfl⟩ := coverage a
        exact (ih _ _ _ _ _ _ (bindings.functionBinder f)).mp (holds f)
      · intro holds f
        exact (ih _ _ _ _ _ _ (bindings.functionBinder f)).mpr (holds (M.delta f))
  | existsPredicate arity body ih =>
      intro om fm objects functions target predicates bindings
      exact exists_congr (fun P => ih _ _ _ _ _ _ bindings)
  | forallPredicate arity body ih =>
      intro om fm objects functions target predicates bindings
      exact forall_congr' (fun P => ih _ _ _ _ _ _ bindings)

end FregeanECA.Functional


namespace FregeanECA
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

theorem shared_term_preserves_value (M : Functional.Interpretation D F R)
    (objects : Nat → D) (functions : Nat → F) (term : Positive.Term) :
    term.functional.value M objects functions = term.value M.applicative objects := by
  induction term with
  | var i => rfl
  | constantK => rfl
  | constantS => rfl
  | app f x hf hx => simp only [Positive.Term.functional, Functional.Term.value, Positive.Term.value, hf, hx]

theorem shared_positive_preserves_truth (M : Functional.Interpretation D F R)
    (formula : Positive.Formula) : ∀ (objects : Nat → D) (functions : Nat → F)
      (predicates : Positive.PredicateAssignment R),
      formula.functional.truth M objects functions predicates ↔
        formula.truth M.applicative objects predicates := by
  induction formula with
  | equal left right => intros; simp [Positive.Formula.functional, Functional.PositiveFormula.truth, Positive.Formula.truth, shared_term_preserves_value]
  | relation arity index arguments => intros; simp [Positive.Formula.functional, Functional.PositiveFormula.truth, Positive.Formula.truth, shared_term_preserves_value]
  | conjunction left right hl hr => intros; exact and_congr (hl _ _ _) (hr _ _ _)
  | disjunction left right hl hr => intros; exact or_congr (hl _ _ _) (hr _ _ _)
  | existsObject body ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallObject body ih => intros; exact forall_congr' (fun _ => ih _ _ _)
  | existsPredicate arity body ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallPredicate arity body ih => intros; exact forall_congr' (fun _ => ih _ _ _)

/-- The shared language is preserved without FE and without any restriction on
the cardinalities or identity of relation representatives. -/
theorem shared_formula_preserves_truth (M : Functional.Interpretation D F R)
    (formula : Applicative.Formula) : ∀ (objects : Nat → D) (functions : Nat → F)
      (predicates : Positive.PredicateAssignment R),
      formula.functional.truth M objects functions predicates ↔
        formula.truth M.applicative objects predicates := by
  induction formula with
  | equal left right => intros; simp [Applicative.Formula.functional, Functional.Formula.truth, Applicative.Formula.truth, shared_term_preserves_value]
  | relation arity index arguments => intros; simp [Applicative.Formula.functional, Functional.Formula.truth, Applicative.Formula.truth, shared_term_preserves_value]
  | relationEqual arity left right => intros; exact Iff.rfl
  | falsum => intros; exact Iff.rfl
  | implies left right hl hr => intros; exact imp_congr (hl _ _ _) (hr _ _ _)
  | conjunction left right hl hr => intros; exact and_congr (hl _ _ _) (hr _ _ _)
  | disjunction left right hl hr => intros; exact or_congr (hl _ _ _) (hr _ _ _)
  | existsObject body ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallObject body ih => intros; exact forall_congr' (fun _ => ih _ _ _)
  | existsPredicate arity body ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallPredicate arity body ih => intros; exact forall_congr' (fun _ => ih _ _ _)

/-- The interpretation of the function sort as a copy of the object domain. -/
def copyExpansion (M : Positive.Interpretation D R) : Functional.Interpretation D D R where
  applicative := M
  eval := M.apply
  delta := id

theorem copy_expansion_preserves_full_truth (M : Positive.Interpretation D R)
    (formula : Functional.Formula) (om fm : Nat → Nat)
    (objects functions target : Nat → D) (predicates : Positive.PredicateAssignment R)
    (bindings : Functional.Bindings (copyExpansion M) om fm objects functions target) :
    formula.truth (copyExpansion M) objects functions predicates ↔
      (formula.translate om fm).truth M target predicates :=
  Functional.translation_preserves_truth (copyExpansion M) (fun _ _ => rfl)
    (fun a => ⟨a, rfl⟩) (fun _ _ h => h) formula om fm objects functions target predicates bindings

end FregeanECA

namespace FregeanECA.Functional
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

structure HasPositiveComprehension (M : Interpretation D F R) : Prop where
  relations_nonempty : ∀ arity, Nonempty (R arity)
  comprehend : ∀ arity (formula : PositiveFormula) (parameters : Nat → D)
    (functions : Nat → F) (predicates : Positive.PredicateAssignment R),
    ∃ relation : R arity, ∀ arguments,
      M.applicative.satisfies arity relation arguments ↔
        formula.truth M (Positive.assignTuple (arity + 1) arguments parameters) functions predicates

def mergedParameters (M : Interpretation D F R) (objects : Nat → D) (functions : Nat → F)
    (i : Nat) : D := if i % 2 = 0 then objects (i / 2) else M.delta (functions (i / 2))

theorem mergedParameters_even (M : Interpretation D F R) (objects : Nat → D)
    (functions : Nat → F) (i : Nat) : mergedParameters M objects functions (2*i) = objects i := by
  have hm : (2*i) % 2 = 0 := by omega
  have hd : (2*i) / 2 = i := by omega
  simp [mergedParameters, hd]

theorem mergedParameters_odd (M : Interpretation D F R) (objects : Nat → D)
    (functions : Nat → F) (i : Nat) :
    mergedParameters M objects functions (2*i+1) = M.delta (functions i) := by
  have hm : (2*i+1) % 2 ≠ 0 := by omega
  have hd : (2*i+1) / 2 = i := by omega
  simp [mergedParameters, hd]

def objectMap (length index : Nat) : Nat :=
  if index < length then index else length + 2*(index-length)
def functionMap (length index : Nat) : Nat := length + (2*index+1)

theorem merged_bindings (M : Interpretation D F R) (length : Nat)
    (arguments : Fin length → D) (objects : Nat → D) (functions : Nat → F) :
    Bindings M (objectMap length) (functionMap length)
      (Positive.assignTuple length arguments objects) functions
      (Positive.assignTuple length arguments (mergedParameters M objects functions)) where
  object := by
    intro i
    by_cases h : i < length
    · simp only [objectMap, if_pos h]
      rw [Positive.assignTuple_at length arguments _ ⟨i,h⟩,
        Positive.assignTuple_at length arguments _ ⟨i,h⟩]
    · have hi : length + (i-length) = i := by omega
      simp only [objectMap, if_neg h, Positive.assignTuple_after]
      rw [mergedParameters_even]
      have hx : Positive.assignTuple length arguments objects i = objects (i-length) := by
        simpa only [hi] using (Positive.assignTuple_after length arguments objects (i-length))
      exact hx.symm
  function := by
    intro i
    simp only [functionMap, Positive.assignTuple_after, mergedParameters_odd]

/-- A1 in the full functional-positive language follows from actual
applicative positive comprehension, without full relation domains or FE. -/
theorem applicative_comprehension_supplies_functional_comprehension
    (M : Interpretation D F R)
    (evaluation : ∀ f x, M.eval f x = M.applicative.apply (M.delta f) x)
    (coverage : ∀ a, ∃ f, M.delta f = a)
    (pc : Positive.HasPositiveComprehension M.applicative) : HasPositiveComprehension M where
  relations_nonempty := pc.relations_nonempty
  comprehend := by
    intro arity formula parameters functions predicates
    obtain ⟨relation, relationLaw⟩ := pc.comprehend arity
      (formula.translate (objectMap (arity+1)) (functionMap (arity+1)))
      (mergedParameters M parameters functions) predicates
    refine ⟨relation, ?_⟩
    intro arguments
    exact (relationLaw arguments).trans
      (positive_translation_preserves_truth M evaluation coverage formula _ _ _ _ _ _
        (merged_bindings M (arity+1) arguments parameters functions)).symm

theorem functional_comprehension_supplies_applicative_comprehension
    (M : Interpretation D F R) (function_nonempty : Nonempty F)
    (pc : HasPositiveComprehension M) : Positive.HasPositiveComprehension M.applicative where
  relations_nonempty := pc.relations_nonempty
  comprehend := by
    intro arity formula parameters predicates
    obtain ⟨f⟩ := function_nonempty
    obtain ⟨relation, relationLaw⟩ := pc.comprehend arity formula.functional parameters (fun _ => f) predicates
    refine ⟨relation, ?_⟩
    intro arguments
    exact (relationLaw arguments).trans (FregeanECA.shared_positive_preserves_truth M formula _ _ _)

end FregeanECA.Functional

namespace FregeanECA
universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-- A1--A5 in the language with defined application. `evaluation` is the
defining application equation; K/S equations are not assumed here. -/
structure RawTFConditions (M : Functional.Interpretation D F R) : Prop where
  comprehension : Functional.HasPositiveComprehension M
  functional_comprehension : ∀ arity (term : Positive.Term) (parameters : Nat → D),
    ∃ f : F, ∀ arguments : Fin (arity+1) → D,
      M.evalVector f arguments =
        term.value M.applicative (Positive.assignTuple (arity+1) arguments parameters)
  lawV : ∀ f g, M.delta f = M.delta g ↔ ∀ x, M.eval f x = M.eval g x
  coverage : ∀ a, ∃ f, M.delta f = a
  nontrivial : ∃ a b : D, a ≠ b
  evaluation : ∀ f x, M.eval f x = M.applicative.apply (M.delta f) x

/-- The unique K and S are explicitly selected in the definitional extension.
Their existence from A2 is proved below, rather than included in RawTFConditions. -/
structure TFConditions (M : Functional.Interpretation D F R) : Prop extends RawTFConditions M where
  combinatory : Positive.CombinatoryLaws M.applicative

structure TSConditions (M : Positive.Interpretation D R) : Prop where
  combinatory : Positive.CombinatoryLaws M
  extensional : ∀ a b, (∀ x, M.apply a x = M.apply b x) → a = b
  nontrivial : ∃ a b : D, a ≠ b
  closure : Positive.PositiveClosure M

def RawTFConditions.representation {M : Functional.Interpretation D F R}
    (h : RawTFConditions M) : Representation D F where
  eval := M.eval
  delta := M.delta
  lawV := h.lawV
  coverage := h.coverage

theorem RawTFConditions.application_extensional {M : Functional.Interpretation D F R}
    (h : RawTFConditions M) (a b : D)
    (same : ∀ x, M.applicative.apply a x = M.applicative.apply b x) : a = b := by
  obtain ⟨f, rfl⟩ := h.coverage a
  obtain ⟨g, rfl⟩ := h.coverage b
  apply (h.lawV f g).mpr
  intro x
  rw [h.evaluation, h.evaluation]
  exact same x

theorem RawTFConditions.combinators_exist {M : Functional.Interpretation D F R}
    (h : RawTFConditions M) :
    (∃ k : D, ∀ x y, M.applicative.apply (M.applicative.apply k x) y = x) ∧
    (∃ s : D, ∀ x y z,
      M.applicative.apply (M.applicative.apply (M.applicative.apply s x) y) z =
        M.applicative.apply (M.applicative.apply x z) (M.applicative.apply y z)) := by
  obtain ⟨f, hf⟩ := h.functional_comprehension 1 (.var 0) (fun _ => M.applicative.constantK)
  obtain ⟨g, hg⟩ := h.functional_comprehension 2
    (.app (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2)))
    (fun _ => M.applicative.constantK)
  constructor
  · refine ⟨M.delta f, ?_⟩
    intro x y
    simpa [Positive.applyArguments, Positive.Term.value, Positive.assignTuple, Positive.pushObject]
      using hf (fun i => if i = 0 then x else y)
  · refine ⟨M.delta g, ?_⟩
    intro x y z
    simpa [Positive.applyArguments, Positive.Term.value, Positive.assignTuple, Positive.pushObject]
      using hg (fun i => if i = 0 then x else if i = 1 then y else z)

theorem tf_reduct_satisfies_ts {M : Functional.Interpretation D F R}
    (h : TFConditions M) : TSConditions M.applicative where
  combinatory := h.combinatory
  extensional := h.toRawTFConditions.application_extensional
  nontrivial := h.nontrivial
  closure := by
    have inhabited : Nonempty F := by
      obtain ⟨f, _⟩ := h.coverage M.applicative.constantK
      exact ⟨f⟩
    exact Positive.positive_comprehension_implies_closure M.applicative
      (Functional.functional_comprehension_supplies_applicative_comprehension M inhabited h.comprehension)

theorem ts_expansion_satisfies_tf {M : Positive.Interpretation D R}
    (h : TSConditions M) : TFConditions (copyExpansion M) where
  comprehension := Functional.applicative_comprehension_supplies_functional_comprehension
    (copyExpansion M) (fun _ _ => rfl) (fun a => ⟨a, rfl⟩)
    (Positive.positive_closure_implies_comprehension M h.combinatory h.nontrivial h.closure)
  functional_comprehension := by
    intro arity term parameters
    exact Positive.terms_have_codes M h.combinatory (arity+1) parameters term
  lawV := by
    intro f g
    exact ⟨fun same x => congrArg (fun a => M.apply a x) same, h.extensional f g⟩
  coverage := fun a => ⟨a, rfl⟩
  nontrivial := h.nontrivial
  evaluation := fun _ _ => rfl
  combinatory := h.combinatory

def changeConstants (M : Functional.Interpretation D F R) (k s : D) :
    Functional.Interpretation D F R :=
  { M with applicative := { M.applicative with constantK := k, constantS := s } }

theorem change_constants_preserves_applications (M : Functional.Interpretation D F R)
    (k s : D) (length : Nat) (code : D) (arguments : Fin length → D) :
    Positive.applyArguments (changeConstants M k s).applicative code arguments =
      Positive.applyArguments M.applicative code arguments := by
  induction length generalizing code with
  | zero => rfl
  | succ length ih => exact ih _ (fun i => arguments i.succ)

/-- None of B1--B5 mentions the designated K/S constants. -/
theorem change_constants_preserves_closure (M : Functional.Interpretation D F R)
    (k s : D) (h : Positive.PositiveClosure M.applicative) :
    Positive.PositiveClosure (changeConstants M k s).applicative where
  equality := h.equality
  preimage := by
    intro source target relation programs
    obtain ⟨result, resultLaw⟩ := h.preimage source target relation programs
    refine ⟨result, ?_⟩
    intro arguments
    change M.applicative.satisfies target result arguments ↔
      M.applicative.satisfies source relation (fun position =>
        Positive.applyArguments (changeConstants M k s).applicative (programs position) arguments)
    simp only [change_constants_preserves_applications]
    exact resultLaw arguments
  intersection := h.intersection
  union := h.union
  existsProjection := h.existsProjection
  forallProjection := h.forallProjection

/-- Every raw A1--A5 model has the definitional K/S expansion. This proves all
schemas in the expansion; it does not merely choose two witnesses and assume
that comprehension survives changing the constants. -/
theorem raw_tf_has_chosen_combinator_expansion {M : Functional.Interpretation D F R}
    (h : RawTFConditions M) : ∃ k s, TFConditions (changeConstants M k s) := by
  obtain ⟨⟨k, hk⟩, ⟨s, hs⟩⟩ := h.combinators_exist
  let N := changeConstants M k s
  have laws : Positive.CombinatoryLaws N.applicative := ⟨hk, hs⟩
  have fnNonempty : Nonempty F := by
    obtain ⟨f, _⟩ := h.coverage k
    exact ⟨f⟩
  have oldPC := Functional.functional_comprehension_supplies_applicative_comprehension
    M fnNonempty h.comprehension
  have oldClosure := Positive.positive_comprehension_implies_closure M.applicative oldPC
  have newClosure : Positive.PositiveClosure N.applicative :=
    change_constants_preserves_closure M k s oldClosure
  have newPC := Positive.positive_closure_implies_comprehension N.applicative laws h.nontrivial newClosure
  refine ⟨k, s, ?_⟩
  exact {
    comprehension := Functional.applicative_comprehension_supplies_functional_comprehension
      N h.evaluation h.coverage newPC
    functional_comprehension := by
      intro arity term parameters
      obtain ⟨a, ha⟩ := Positive.terms_have_codes N.applicative laws (arity+1) parameters term
      obtain ⟨f, hf⟩ := h.coverage a
      refine ⟨f, ?_⟩
      intro arguments
      change Positive.applyArguments N.applicative (M.delta f) arguments = _
      rw [hf]
      exact ha arguments
    lawV := h.lawV
    coverage := h.coverage
    nontrivial := h.nontrivial
    evaluation := h.evaluation
    combinatory := laws }

theorem combinator_choices_are_unique {M : Functional.Interpretation D F R}
    (h : RawTFConditions M) {k k' s s' : D}
    (hk : ∀ x y, M.applicative.apply (M.applicative.apply k x) y = x)
    (hk' : ∀ x y, M.applicative.apply (M.applicative.apply k' x) y = x)
    (hs : ∀ x y z, M.applicative.apply (M.applicative.apply (M.applicative.apply s x) y) z =
      M.applicative.apply (M.applicative.apply x z) (M.applicative.apply y z))
    (hs' : ∀ x y z, M.applicative.apply (M.applicative.apply (M.applicative.apply s' x) y) z =
      M.applicative.apply (M.applicative.apply x z) (M.applicative.apply y z)) : k = k' ∧ s = s' := by
  constructor
  · apply h.application_extensional
    intro x
    apply h.application_extensional
    intro y
    rw [hk, hk']
  · apply h.application_extensional
    intro x
    apply h.application_extensional
    intro y
    apply h.application_extensional
    intro z
    rw [hs, hs']

/-- FE makes the representation an isomorphism of the function sort with the
object sort; evaluation is recovered by application under this isomorphism. -/
theorem function_sort_isomorphism {M : Functional.Interpretation D F R}
    (h : RawTFConditions M)
    (fe : ∀ f g, (∀ x, M.eval f x = M.eval g x) → f = g) :
    ∃ inverse : D → F,
      (∀ f, inverse (M.delta f) = f) ∧
      (∀ a, M.delta (inverse a) = a) ∧
      (∀ a x, M.eval (inverse a) x = M.applicative.apply a x) := by
  classical
  let inverse := fun a => Classical.choose (h.coverage a)
  have right : ∀ a, M.delta (inverse a) = a := fun a => Classical.choose_spec (h.coverage a)
  refine ⟨inverse, ?_, right, ?_⟩
  · intro f
    exact fe _ _ ((h.lawV _ _).mp (right (M.delta f)))
  · intro a x
    rw [h.evaluation, right]

/-- These are ordinary semantic consequences, not a definition of derivability. -/
def TFValid (formula : Applicative.Formula) : Prop :=
  ∀ (D F : Type) (R : Nat → Type) (M : Functional.Interpretation D F R),
    TFConditions M → ∀ objects functions predicates,
      formula.functional.truth M objects functions predicates

def TSValid (formula : Applicative.Formula) : Prop :=
  ∀ (D : Type) (R : Nat → Type) (M : Positive.Interpretation D R),
    TSConditions M → ∀ objects predicates, formula.truth M objects predicates

theorem shared_semantic_consequences_iff (formula : Applicative.Formula) :
    TFValid formula ↔ TSValid formula := by
  constructor
  · intro valid D R M h objects predicates
    have holds := valid D D R (copyExpansion M) (ts_expansion_satisfies_tf h)
      objects (fun _ => M.constantK) predicates
    exact (shared_formula_preserves_truth (copyExpansion M) formula _ _ _).mp holds
  · intro valid D F R M h objects functions predicates
    exact (shared_formula_preserves_truth M formula _ _ _).mpr
      (valid D R M.applicative (tf_reduct_satisfies_ts h) objects predicates)

end FregeanECA
