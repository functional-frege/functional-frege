import FregeanECA.V3.Cleaner
import FregeanECA.V3.PaperResults
import FregeanECA.V3.Nontriviality

/-!
The theory exactly as printed in the paper (`def:tf`): the six axioms

  A1  Relational comprehension   ∃P ∀x̄ (P(x̄) ↔ φ(x̄)),  |x̄| ≥ 1, φ not containing P
  A2  Functional comprehension   ∃f ∀x̄ (f(x̄) = θ(x̄)),  |x̄| ≥ 1, θ an application
                                  term all of whose variables are among the inputs x̄
  A3  Functional Basic Law V     ∀f,g (δf = δg ↔ ∀x f(x) = g(x))
  A4  Functional extensionality  ∀f,g ((∀x f(x) = g(x)) → f = g)
  A5  Coverage                   ∀y ∃f (δf = y)
  A6  Nontriviality              T ≠ F

written out as formulas of the development's formula language, together with
the defining clauses for the application symbol and the constants K and S
(`V3.Cleaner.DefinitionAxiom`). In A2 the left side f(x₁, …, xₙ) is the paper's
convention: f evaluated at x₁ (the primitive evaluation `Term.eval`, an
object), and that object applied to x₂, …, xₙ in turn by the application
operation `Term.app`; for n = 1 it is just f(x₁). T and F are the abstracts of
the two projections, K and K·I in combinator notation.

`V3.Cleaner.theory` is the encoded presentation used by the older modules: its
A2 applies the abstract δf to all inputs and admits parameters and the empty
input list, its A3 is injective abstraction and its A5 is ∃x,y (x ≠ y). This
module proves that the printed axioms have exactly the models
(`axioms_iff_cleaner`) and exactly the theorems (`provability_iff`) of the
encoded presentation. The two left sides of A2 differ by the defining clause
of application, (δf)(x) = f(x), at the first step (`A2_iff_cleaner`); the
parametric encoded instances follow from the printed axioms by
`parametric_comprehension` (`prop:parametric`). The one-object structure shows
that A6 is independent of A1–A5 (`A6_not_provable`).
-/
namespace FregeanECA.V4.Printed

open FFL FFL.FirstOrder Functional Axioms Guarded Encoded Part2
open scoped FFL.FirstOrder
open FregeanECA.V3.Cleaner (ApplicationTerm)

universe u v w
variable {D : Type u} {F : Type v} {R : Nat → Type w}

/-! ### The six axioms -/

/-- A1 as printed: ∃P ∀x̄ (P(x̄) ↔ φ(x̄)) for the n + 1 inputs x₀, …, xₙ (the
relation sort indexed by n has n + 1 argument places, so every instance has at
least one input; input xᵢ is the object variable i under the binders). The
relation variable P introduced by the axiom is the fresh index 0 of its arity,
and the proviso that φ does not mention P is realised by shifting the other
relation variables of that arity in φ past the new binder; so every formula φ
of the language is admissible, with parameters and with quantifiers over
objects, functions and relations. -/
def A1 (n : Nat) (φ : Formula) : Formula :=
  .existsPredicate n (allObjects (n + 1)
    (iffF (.relation n 0 (fun i => .var i.val))
      (renameFullPredicates (fun arity index => if arity = n then index + 1 else index) φ)))

/-- The term of the functional language denoted by an application term:
object variables and application only. -/
def termOf : ApplicationTerm → Term
  | .var i => .var i
  | .app σ θ => .app (termOf σ) (termOf θ)

/-- The side condition of A2: every variable of θ is one of the first `m`
object variables, the bound inputs. -/
def Closed (m : Nat) : ApplicationTerm → Prop
  | .var i => i < m
  | .app σ θ => Closed m σ ∧ Closed m θ

instance Closed.decidable (m : Nat) : (θ : ApplicationTerm) → Decidable (Closed m θ)
  | .var i => inferInstanceAs (Decidable (i < m))
  | .app σ θ =>
      haveI := Closed.decidable m σ
      haveI := Closed.decidable m θ
      inferInstanceAs (Decidable (Closed m σ ∧ Closed m θ))

/-- f(x₀, …, xₙ) for the function variable f = 0 and the n + 1 inputs
x₀, …, xₙ: f evaluated at the first input (`Term.eval`, an object), and the
resulting object applied to the remaining inputs in turn (`Term.app`). -/
def functionAtInputs : Nat → Term
  | 0 => .eval 0 (.var 0)
  | k + 1 => .app (functionAtInputs k) (.var (k + 1))

/-- A2 as printed: ∃f ∀x̄ (f(x̄) = θ(x̄)) for the n + 1 inputs x₀, …, xₙ, with
input xᵢ the object variable i under the binders. `CoreAxiom` admits the
instance exactly when `Closed (n + 1) θ`: every variable of θ is an input. -/
def A2 (n : Nat) (θ : ApplicationTerm) : Formula :=
  .existsFunction (allObjects (n + 1) (.equal (functionAtInputs n) (termOf θ)))

/-- A3 as printed: functional Basic Law V, ∀f,g (δf = δg ↔ ∀x f(x) = g(x)). -/
def A3 : Formula := allFunctions 2
  (iffF (.equal (.delta 0) (.delta 1))
    (.forallObject (.equal (.eval 0 (.var 0)) (.eval 1 (.var 0)))))

/-- A4 as printed: functional extensionality, ∀f,g ((∀x f(x) = g(x)) → f = g). -/
def A4 : Formula := allFunctions 2
  (.implies (.forallObject (.equal (.eval 0 (.var 0)) (.eval 1 (.var 0))))
    (.functionEqual 0 1))

/-- A5 as printed: coverage, ∀y ∃f (δf = y). -/
def A5 : Formula := .forallObject (.existsFunction (.equal (.delta 0) (.var 0)))

/-- Church's truth values in the encoded term language: T = K and
F = K·I with I = S·K·K, the abstracts of the two projections. -/
def churchTrue : Term := .constantK
def churchFalse : Term :=
  .app .constantK (.app (.app .constantS .constantK) .constantK)

/-- A6 as printed: nontriviality, T ≠ F. -/
def A6 : Formula := notF (.equal churchTrue churchFalse)

/-- The six printed axioms. A1 and A2 are schemas; A2 is restricted to terms
all of whose variables are among the bound inputs. -/
inductive CoreAxiom : Formula → Prop where
  | a1 (n : Nat) (φ : Formula) : CoreAxiom (A1 n φ)
  | a2 (n : Nat) (θ : ApplicationTerm) (closed : Closed (n + 1) θ) : CoreAxiom (A2 n θ)
  | a3 : CoreAxiom A3
  | a4 : CoreAxiom A4
  | a5 : CoreAxiom A5
  | a6 : CoreAxiom A6

/-- The printed axioms together with the defining clauses for application and
for K and S. -/
def Axiom (p : Formula) : Prop := CoreAxiom p ∨ V3.Cleaner.DefinitionAxiom p

/-- The printed theory. -/
abbrev theory := Encoded.theory Axiom

/-! ### The printed formulas and the development's named formulas -/

theorem A1_eq (n : Nat) (φ : Formula) : A1 n φ = fullRelationalComprehension n φ := rfl
theorem A3_eq : A3 = lawV := rfl
theorem A4_eq : A4 = functionExtensionality := rfl
theorem A5_eq : A5 = coverage := rfl

theorem termOf_eq (θ : ApplicationTerm) : termOf θ = θ.positive.functional := by
  induction θ with
  | var i => rfl
  | app σ τ ih₁ ih₂ =>
      simp only [termOf, V3.Cleaner.ApplicationTerm.positive, Positive.Term.functional, ih₁, ih₂]

theorem termOf_value (M : Interpretation D F R) (θ : ApplicationTerm)
    (o : Nat → D) (f : Nat → F) :
    (termOf θ).value M o f = θ.positive.value M.applicative o := by
  rw [termOf_eq, applicativeTerm_value]

/-! ### Truth conditions -/

theorem A1_truth (M : Interpretation D F R) (n : Nat) (φ : Formula)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (A1 n φ).truth M o f r ↔
      ∃ P : R n, ∀ xs, M.applicative.satisfies n P xs ↔
        φ.truth M (Positive.assignTuple (n + 1) xs o) f r :=
  fullRelationalComprehension_truth M n φ o f r

theorem functionAtInputs_value (M : Interpretation D F R) (n : Nat)
    (o : Nat → D) (f : Nat → F) :
    (functionAtInputs n).value M o f =
      Positive.applyArguments M.applicative (M.eval (f 0) (o 0))
        (fun i : Fin n => o (i.val + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Positive.applyArguments_append]
      change M.applicative.apply ((functionAtInputs n).value M o f) (o (n + 1)) = _
      rw [ih]
      rfl

/-- The printed A2 instance says: some f, evaluated at the first input and the
result applied to the remaining inputs, returns θ at every input tuple. -/
theorem A2_truth (M : Interpretation D F R) (n : Nat) (θ : ApplicationTerm)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    (A2 n θ).truth M o f r ↔
      ∃ g : F, ∀ xs : Fin (n + 1) → D,
        Positive.applyArguments M.applicative (M.eval g (xs 0)) (fun i => xs i.succ) =
          θ.positive.value M.applicative (Positive.assignTuple (n + 1) xs o) := by
  change (∃ g, _) ↔ _
  apply exists_congr
  intro g
  rw [allObjects_truth]
  apply forall_congr'
  intro xs
  change (functionAtInputs n).value M _ _ = (termOf θ).value M _ _ ↔ _
  rw [functionAtInputs_value, termOf_value]
  have h0 : Positive.assignTuple (n + 1) xs o 0 = xs 0 := Positive.assignTuple_at (n + 1) xs o 0
  have hs : (fun i : Fin n => Positive.assignTuple (n + 1) xs o (i.val + 1)) =
      fun i => xs i.succ := by
    funext i
    exact Positive.assignTuple_at (n + 1) xs o i.succ
  rw [h0, hs]
  exact Iff.rfl

theorem A3_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    A3.truth M o f r ↔ ∀ a b : F, M.delta a = M.delta b ↔ ∀ x, M.eval a x = M.eval b x :=
  lawV_truth M o f r

theorem A4_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    A4.truth M o f r ↔ ∀ a b : F, (∀ x, M.eval a x = M.eval b x) → a = b :=
  functionExtensionality_truth M o f r

theorem A5_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    A5.truth M o f r ↔ ∀ y : D, ∃ g : F, M.delta g = y := Iff.rfl

/-- The identity combinator I = S·K·K in a model. -/
def identityObject (M : Interpretation D F R) : D :=
  M.applicative.apply (M.applicative.apply M.applicative.constantS M.applicative.constantK)
    M.applicative.constantK

theorem A6_truth (M : Interpretation D F R) (o : Nat → D) (f : Nat → F)
    (r : Positive.PredicateAssignment R) :
    A6.truth M o f r ↔
      M.applicative.constantK ≠ M.applicative.apply M.applicative.constantK (identityObject M) :=
  Iff.rfl

/-! ### A3: functional Basic Law V versus injective abstraction -/

/-- Given A4, functional Basic Law V makes abstraction injective. -/
theorem injective_of_lawV (M : Interpretation D F R)
    (lv : Valid M A3) (ext : Valid M A4) : Valid M V3.Cleaner.A3 := by
  intro o f r
  have hv := (A3_truth M o f r).mp (lv o f r)
  have he := (A4_truth M o f r).mp (ext o f r)
  apply (V3.Cleaner.A3_truth M o f r).mpr
  intro a b
  exact ⟨fun hab => he a b ((hv a b).mp hab), congrArg M.delta⟩

/-- Given A4, injective abstraction yields functional Basic Law V. -/
theorem lawV_of_injective (M : Interpretation D F R)
    (inj : Valid M V3.Cleaner.A3) (ext : Valid M A4) : Valid M A3 := by
  intro o f r
  have hi := (V3.Cleaner.A3_truth M o f r).mp (inj o f r)
  have he := (A4_truth M o f r).mp (ext o f r)
  apply (A3_truth M o f r).mpr
  intro a b
  constructor
  · intro eqd
    have eqf := (hi a b).mp eqd
    subst eqf
    exact fun _ => rfl
  · intro pointwise
    exact congrArg M.delta (he a b pointwise)

/-! ### A6: distinct truth values versus nontriviality -/

/-- T ≠ F exhibits two distinct objects. -/
theorem nontriviality_of_A6 (M : Interpretation D F R) (h : Valid M A6) :
    Valid M nontriviality := by
  intro o f r
  exact (nontriviality_truth M o f r).mpr ⟨_, _, (A6_truth M o f r).mp (h o f r)⟩

/-- Given the K and S laws, two distinct objects force T ≠ F: if K = K·I then
every x equals K·x·y = (K·I)·x·y = I·y = y. -/
theorem A6_of_nontriviality (M : Interpretation D F R)
    (hn : Valid M nontriviality) (hk : Valid M kLaw) (hs : Valid M sLaw) :
    Valid M A6 := by
  intro o f r
  apply (A6_truth M o f r).mpr
  intro heq
  obtain ⟨a, b, hab⟩ := (nontriviality_truth M o f r).mp (hn o f r)
  have k := (kLaw_truth M o f r).mp (hk o f r)
  have s := (sLaw_truth M o f r).mp (hs o f r)
  apply hab
  have step : M.applicative.apply (M.applicative.apply M.applicative.constantK a) b =
      M.applicative.apply (M.applicative.apply
        (M.applicative.apply M.applicative.constantK (identityObject M)) a) b := by
    rw [← heq]
  calc a = M.applicative.apply (M.applicative.apply M.applicative.constantK a) b := (k a b).symm
    _ = M.applicative.apply (M.applicative.apply
          (M.applicative.apply M.applicative.constantK (identityObject M)) a) b := step
    _ = M.applicative.apply (identityObject M) b := by rw [k]
    _ = M.applicative.apply (M.applicative.apply M.applicative.constantK b)
          (M.applicative.apply M.applicative.constantK b) := s _ _ _
    _ = b := k _ _

/-! ### A2: f evaluated at the first input versus δf applied to all inputs -/

/-- Under the defining clause of application, (δf)(x) = f(x), the printed
instance for θ with the n + 1 inputs x₀, …, xₙ and the encoded instance
`V3.Cleaner.A2 (n + 1) θ`, whose left side applies δf to all inputs, say the
same thing: the two left sides agree after the first step. -/
theorem A2_iff_cleaner (M : Interpretation D F R) (n : Nat) (θ : ApplicationTerm)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R)
    (ev : evaluation.truth M o f r) :
    (A2 n θ).truth M o f r ↔ (V3.Cleaner.A2 (n + 1) θ).truth M o f r := by
  rw [A2_truth, V3.Cleaner.A2_truth]
  have ev' := (evaluation_truth M o f r).mp ev
  apply exists_congr
  intro g
  apply forall_congr'
  intro xs
  rw [show Positive.applyArguments M.applicative (M.delta g) xs =
      Positive.applyArguments M.applicative (M.eval g (xs 0)) (fun i => xs i.succ) from
    M.evalVector_eq_curried ev' g xs]

theorem A2_valid_iff_cleaner (M : Interpretation D F R) (n : Nat) (θ : ApplicationTerm)
    (ev : Valid M evaluation) :
    Valid M (A2 n θ) ↔ Valid M (V3.Cleaner.A2 (n + 1) θ) :=
  ⟨fun h o f r => (A2_iff_cleaner M n θ o f r (ev o f r)).mp (h o f r),
    fun h o f r => (A2_iff_cleaner M n θ o f r (ev o f r)).mpr (h o f r)⟩

/-! ### Functional comprehension with parameters (`prop:parametric`) -/

/-- The first projection: the instance θ = x₀ with inputs x₀, x₁. With the
defining clause of application its abstract is a K object. -/
theorem k_exists (M : Interpretation D F R)
    (h : ∀ p, CoreAxiom p → Valid M p) (ev : Valid M evaluation)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    ∃ k : D, ∀ x y, M.applicative.apply (M.applicative.apply k x) y = x := by
  obtain ⟨g, hg⟩ := (V3.Cleaner.A2_truth M 2 (.var 0) o f r).mp
    ((A2_iff_cleaner M 1 (.var 0) o f r (ev o f r)).mp
      (h _ (.a2 1 (.var 0) (by decide)) o f r))
  refine ⟨M.delta g, fun x y => ?_⟩
  exact hg (Fin.cases (motive := fun _ => D) x (fun _ => y))

/-- The instance θ = (x₀ x₂)(x₁ x₂) with inputs x₀, x₁, x₂. With the defining
clause of application its abstract is an S object. -/
theorem s_exists (M : Interpretation D F R)
    (h : ∀ p, CoreAxiom p → Valid M p) (ev : Valid M evaluation)
    (o : Nat → D) (f : Nat → F) (r : Positive.PredicateAssignment R) :
    ∃ s : D, ∀ x y z,
      M.applicative.apply (M.applicative.apply (M.applicative.apply s x) y) z =
        M.applicative.apply (M.applicative.apply x z) (M.applicative.apply y z) := by
  obtain ⟨g, hg⟩ := (V3.Cleaner.A2_truth M 3
      (.app (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2))) o f r).mp
    ((A2_iff_cleaner M 2 (.app (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2))) o f r
      (ev o f r)).mp
      (h _ (.a2 2 (.app (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2))) (by decide)) o f r))
  refine ⟨M.delta g, fun x y z => ?_⟩
  exact hg (Fin.cases (motive := fun _ => D) x
    (Fin.cases (motive := fun _ => D) y (fun _ => z)))

theorem applyArguments_same_apply (model model' : Positive.Interpretation D R)
    (same : model'.apply = model.apply) (n : Nat) (z : D) (xs : Fin n → D) :
    Positive.applyArguments model' z xs = Positive.applyArguments model z xs := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      change Positive.applyArguments model' (model'.apply z (xs 0)) (fun i => xs i.succ) =
        Positive.applyArguments model (model.apply z (xs 0)) (fun i => xs i.succ)
      rw [same]
      exact ih _ _

/-- An application term has no constants, so its value depends on the
application operation alone. -/
theorem positive_value_same_apply (model model' : Positive.Interpretation D R)
    (same : model'.apply = model.apply) (θ : ApplicationTerm) (env : Nat → D) :
    θ.positive.value model' env = θ.positive.value model env := by
  induction θ with
  | var i => rfl
  | app σ τ ih₁ ih₂ =>
      change model'.apply _ _ = model.apply _ _
      rw [same, ih₁, ih₂]

/-- `prop:parametric` in a model, from the printed core axioms and the
defining clause of application alone: every encoded A2 instance
`V3.Cleaner.A2 n θ` holds, parameters and the empty input list included. The
printed instances for x₀ and for (x₀ x₂)(x₁ x₂) give K and S objects; with
them the bracket lemma `Positive.terms_have_codes` represents θ, its
parameters fixed by the assignment, by an object z with z·x̄ = θ(x̄); coverage
gives h with δh = z, and h witnesses the instance. For n = 0 the term is an
object and coverage alone supplies the witness. -/
theorem parametric_comprehension_of_core (M : Interpretation D F R)
    (h : ∀ p, CoreAxiom p → Valid M p) (ev : Valid M evaluation)
    (n : Nat) (θ : ApplicationTerm) : Valid M (V3.Cleaner.A2 n θ) := by
  intro o f r
  obtain ⟨k, hk⟩ := k_exists M h ev o f r
  obtain ⟨s, hs⟩ := s_exists M h ev o f r
  let model : Positive.Interpretation D R :=
    { M.applicative with constantK := k, constantS := s }
  have laws : Positive.CombinatoryLaws model := ⟨hk, hs⟩
  obtain ⟨z, hz⟩ := Positive.terms_have_codes model laws n o θ.positive
  obtain ⟨g, hg⟩ := (A5_truth M o f r).mp (h _ .a5 o f r) z
  apply (V3.Cleaner.A2_truth M n θ o f r).mpr
  refine ⟨g, fun xs => ?_⟩
  rw [hg, ← applyArguments_same_apply M.applicative model rfl n z xs, hz,
    positive_value_same_apply M.applicative model rfl θ]

/-- `prop:parametric`: in every model of the printed axioms, functional
comprehension holds for every application term with parameters and any
number of inputs, zero included; that is, every instance of the encoded A2 of
`V3.Cleaner` is valid. -/
theorem parametric_comprehension (M : Interpretation D F R)
    (h : ∀ p, Axiom p → Valid M p) (n : Nat) (θ : ApplicationTerm) :
    Valid M (V3.Cleaner.A2 n θ) :=
  parametric_comprehension_of_core M (fun p hp => h p (Or.inl hp))
    (h _ (Or.inr .evaluation)) n θ

/-! ### Same models, same theorems -/

/-- The printed core axioms, with the defining clause of application, imply
the encoded core axioms. -/
theorem core_to_cleaner (M : Interpretation D F R)
    (h : ∀ p, CoreAxiom p → Valid M p) (ev : Valid M evaluation) :
    ∀ p, V3.Cleaner.CoreAxiom p → Valid M p := by
  intro p hp
  cases hp with
  | a1 n body => exact h _ (.a1 n body)
  | a2 n t => exact parametric_comprehension_of_core M h ev n t
  | a3 => exact injective_of_lawV M (h _ .a3) (h _ .a4)
  | a4 => exact h _ .a4
  | a5 => exact nontriviality_of_A6 M (h _ .a6)

/-- Coverage is the zero-input encoded instance for a variable, its free
parameter universally closed. -/
theorem A5_of_cleaner_zero (M : Interpretation D F R)
    (zero : Valid M (V3.Cleaner.A2 0 (.var 0))) : Valid M A5 := by
  intro o f r
  apply (A5_truth M o f r).mpr
  intro y
  obtain ⟨g, hg⟩ := (V3.Cleaner.A2_truth M 0 (.var 0) (fun _ => y) f r).mp
    (zero (fun _ => y) f r)
  exact ⟨g, hg Fin.elim0⟩

/-- The printed axiom set and the encoded one have the same models. -/
theorem axioms_iff_cleaner (M : Interpretation D F R) :
    (∀ p, Axiom p → Valid M p) ↔ (∀ p, V3.Cleaner.Axiom p → Valid M p) := by
  constructor
  · intro h p hp
    rcases hp with hp | hp
    · exact core_to_cleaner M (fun q hq => h q (Or.inl hq)) (h _ (Or.inr .evaluation)) p hp
    · exact h _ (Or.inr hp)
  · intro h p hp
    rcases hp with hp | hp
    · cases hp with
      | a1 n body => exact h _ (Or.inl (.a1 n body))
      | a2 n θ _ =>
          exact (A2_valid_iff_cleaner M n θ (h _ (Or.inr .evaluation))).mpr
            (h _ (Or.inl (.a2 (n + 1) θ)))
      | a3 => exact lawV_of_injective M (h _ (Or.inl .a3)) (h _ (Or.inl .a4))
      | a4 => exact h _ (Or.inl .a4)
      | a5 => exact A5_of_cleaner_zero M (h _ (Or.inl (.a2 0 (.var 0))))
      | a6 =>
          exact A6_of_nontriviality M (h _ (Or.inl .a5)) (h _ (Or.inr .k)) (h _ (Or.inr .s))
    · exact h _ (Or.inr hp)

/-- Every sentence of the encoded language is derivable from the printed
theory exactly when it is derivable from `V3.Cleaner.theory`. -/
theorem provability_iff (σ : Sentence language) :
    (theory ⊢ σ) ↔ (V3.Cleaner.theory ⊢ σ) := by
  apply LogicBridge.provable_iff_of_eq_model_lifts
  · intro M _ _ _ h
    have := sorts_of_model h
    have native := (model_iff_valid (extractedRealization M) V3.Cleaner.Axiom).mp h
    exact ⟨M↓[language], (model_iff_valid (extractedRealization M) Axiom).mpr
      ((axioms_iff_cleaner (extracted M)).mpr native), Iff.rfl⟩
  · intro M _ _ _ h
    have := sorts_of_model h
    have native := (model_iff_valid (extractedRealization M) Axiom).mp h
    exact ⟨M↓[language], (model_iff_valid (extractedRealization M) V3.Cleaner.Axiom).mpr
      ((axioms_iff_cleaner (extracted M)).mp native), Iff.rfl⟩

theorem consistency_iff :
    Entailment.Consistent theory ↔ Entailment.Consistent V3.Cleaner.theory := by
  rw [Entailment.consistent_iff_unprovable_bot, Entailment.consistent_iff_unprovable_bot]
  exact not_congr (provability_iff (⊥ : Sentence language))

/-- The printed A3 is derivable (it is an axiom); recorded for the
bi-interpretability certificate, where A3 is one of the isomorphism sentences. -/
theorem lawV_provable : theory ⊢ sentence A3 :=
  (provability_iff _).mpr
    (V3.PaperResults.provable_of_valid _ (fun M h =>
      lawV_of_injective M (h _ (Or.inl .a3)) (h _ (Or.inl .a4))))

/-- `prop:parametric` as derivability: every encoded A2 instance, parameters
and the empty input list included, is a theorem of the printed theory. -/
theorem parametric_comprehension_provable (n : Nat) (θ : ApplicationTerm) :
    theory ⊢ sentence (V3.Cleaner.A2 n θ) :=
  (provability_iff _).mpr
    (V3.PaperResults.provable_of_valid _ (fun _ h => h _ (Or.inl (.a2 n θ))))

/-! ### Independence of A6 from the printed A1–A5 -/

/-- The printed axioms other than A6. -/
inductive FirstFive : Formula → Prop where
  | a1 (n : Nat) (φ : Formula) : FirstFive (A1 n φ)
  | a2 (n : Nat) (θ : ApplicationTerm) (closed : Closed (n + 1) θ) : FirstFive (A2 n θ)
  | a3 : FirstFive A3
  | a4 : FirstFive A4
  | a5 : FirstFive A5

def FirstFiveAxiom (p : Formula) : Prop := FirstFive p ∨ V3.Cleaner.DefinitionAxiom p
abbrev firstFiveTheory := Encoded.theory FirstFiveAxiom

theorem singleton_satisfies_first_five :
    ∀ p, FirstFiveAxiom p → Valid V3.Nontriviality.model p := by
  intro p hp
  rcases hp with hp | hp
  · cases hp with
    | a1 n body =>
        exact V3.Nontriviality.singleton_satisfies_first_four _ (Or.inl (.a1 n body))
    | a2 n θ _ =>
        intro o f r
        apply (A2_truth V3.Nontriviality.model n θ o f r).mpr
        exact ⟨(), fun _ => Subsingleton.elim _ _⟩
    | a3 =>
        intro o f r
        apply (A3_truth V3.Nontriviality.model o f r).mpr
        exact fun _ _ => ⟨fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
    | a4 =>
        exact V3.Nontriviality.singleton_satisfies_first_four _ (Or.inl .a4)
    | a5 =>
        intro o f r
        apply (A5_truth V3.Nontriviality.model o f r).mpr
        exact fun _ => ⟨(), Subsingleton.elim _ _⟩
  · exact V3.Nontriviality.singleton_satisfies_first_four _ (Or.inr hp)

/-- In the one-object structure T = F. -/
theorem singleton_refutes_A6 : ¬ Valid V3.Nontriviality.model A6 := by
  intro h
  exact (A6_truth V3.Nontriviality.model (fun _ => ()) (fun _ => ()) (fun _ _ _ => False)).mp
    (h _ _ _) (Subsingleton.elim _ _)

/-- `prop:nontriviality`: the one-object structure satisfies the printed
A1–A5 and the defining clauses, and refutes the printed A6. -/
theorem countermodel :
    (∀ p, FirstFiveAxiom p → Valid V3.Nontriviality.model p) ∧
      ¬ Valid V3.Nontriviality.model A6 :=
  ⟨singleton_satisfies_first_five, singleton_refutes_A6⟩

/-- `prop:nontriviality`: the printed A6 is not derivable from the printed
A1–A5 together with the defining clauses. -/
theorem A6_not_provable : ¬ (firstFiveTheory ⊢ sentence A6) := by
  intro proof
  have satisfies :=
    taggedModel_valid V3.Nontriviality.model FirstFiveAxiom singleton_satisfies_first_five
  have truth := Theory.Proof.sound proof satisfies
  exact singleton_refutes_A6 ((taggedModel_truth V3.Nontriviality.model A6).mp truth)

end FregeanECA.V4.Printed

#print axioms FregeanECA.V4.Printed.parametric_comprehension
#print axioms FregeanECA.V4.Printed.provability_iff
#print axioms FregeanECA.V4.Printed.consistency_iff
#print axioms FregeanECA.V4.Printed.A6_not_provable
