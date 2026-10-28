import FregeanECA.Part2.ArithmeticGraphs
import FregeanECA.Part2.FregeArithmeticSyntax

/-! Conditional reuse interface for the generic arithmetic recursion proofs.
No ECA law is assumed. The comprehension translation and successor hypotheses
are explicit obligations; this module does not claim to discharge them from HP.
In particular, PeanoDomain requires successor separation and injectivity on
the ENTIRE object carrier. Defaulting successor to zero outside its number
domain therefore does not meet this interface. -/

namespace FregeanECA.Part2.FregeArithmeticAdapter
open Positive Arithmetic
universe u v
variable {D : Type u} {R : Nat → Type v}

noncomputable def interpretation
    (satisfies : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (zero tag : D) (successor : D → D) : Positive.Interpretation D R := by
  classical
  exact { apply := fun f x => if f = tag then successor x else zero
          constantK := tag
          constantS := zero
          satisfies := satisfies }

@[simp] theorem adapter_zero
    (source : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (zero tag : D) (successor : D → D) (distinct : tag ≠ zero) :
    modelZero (interpretation source zero tag successor) = zero := by
  simp [modelZero, interpretation, Ne.symm distinct]

@[simp] theorem adapter_successor
    (source : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (zero tag : D) (successor : D → D) (x : D) :
    modelSuccessor (interpretation source zero tag successor) x = successor x := by
  simp [modelSuccessor, interpretation]

/-- Comprehension transports through a truth-preserving translation of the
actual full formula grammar, for every object and predicate assignment.
Merely knowing that a successor graph exists does not supply this premise. -/
theorem comprehension_of_translation (source : FregeArithmetic.Interpretation D R)
    (sourceFull : FregeArithmetic.HasFullComprehension source)
    (zero tag : D) (successor : D → D)
    (translate : Applicative.Formula → FregeArithmetic.Formula)
    (translation_truth : ∀ p o r,
      (translate p).truth source o r ↔
        p.truth (interpretation source.satisfies zero tag successor) o r) :
    HasFullComprehension (interpretation source.satisfies zero tag successor) := by
  refine ⟨sourceFull.relations_nonempty, ?_⟩
  intro arity p objects predicates
  obtain ⟨P, represents⟩ := sourceFull.comprehend arity (translate p) objects predicates
  exact ⟨P, fun xs => (represents xs).trans (translation_truth p _ _)⟩

/-- The exact obstruction to the proposed default-zero extension. -/
theorem default_zero_obstruction
    (source : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (zero tag : D) (successor : D → D) (distinct : tag ≠ zero)
    (hitsZero : ∃ x, successor x = zero) (N : R 0) :
    ¬ PeanoDomain (interpretation source zero tag successor) N := by
  intro domain
  obtain ⟨x, hx⟩ := hitsZero
  apply domain.zero_not_successor x
  simpa only [adapter_zero source zero tag successor distinct, adapter_successor] using hx.symm

/-- A lawful global successor and a represented least domain suffice.
Formula induction follows from the explicitly supplied comprehension. -/
theorem peano_domain
    (source : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (zero tag : D) (successor : D → D) (distinct : tag ≠ zero)
    (full : HasFullComprehension (interpretation source zero tag successor))
    (N : R 0) (least : RepresentsLeast (interpretation source zero tag successor) N)
    (separated : ∀ x, zero ≠ successor x)
    (injective : Function.Injective successor) :
    PeanoDomain (interpretation source zero tag successor) N := by
  let M := interpretation source zero tag successor
  have closed := represented_least_is_inductive M least
  have intersections := positive_closure_supplies_unary_intersections M
    (full_comprehension_implies_classical_closure M full).positive
  refine { represents_least := least
           zero_member := closed.1
           successor_closed := closed.2
           zero_not_successor := ?_
           successor_injective := ?_
           formula_induction := ?_ }
  · intro x
    simpa only [adapter_zero source zero tag successor distinct, adapter_successor]
      using separated x
  · intro x y same
    apply injective
    simpa only [adapter_successor] using same
  · intro p objects predicates base step
    exact represented_formula_induction M intersections least p objects predicates
      (full_comprehension_represents_unary_formula M full p objects predicates) base step

/-- The existing addition/multiplication construction is genuinely independent
of ECA: once the explicit adapter obligations hold, it applies unchanged. -/
theorem arithmetic
    (source : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (zero tag : D) (successor : D → D) (distinct : tag ≠ zero)
    (full : HasFullComprehension (interpretation source zero tag successor))
    (N : R 0) (least : RepresentsLeast (interpretation source zero tag successor) N)
    (separated : ∀ x, zero ≠ successor x)
    (injective : Function.Injective successor) :
    Nonempty (FullArithmetic (interpretation source zero tag successor) N) :=
  full_comprehension_supplies_arithmetic _ full
    (peano_domain source zero tag successor distinct full N least separated injective)

/-- On the number subtype, the natural-domain representative is universal.
Ordinary induction for all available predicates makes it the least domain. -/
theorem least_of_available_induction
    (source : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (zero tag : D) (successor : D → D) (distinct : tag ≠ zero)
    (N : R 0) (universal : ∀ x, source 0 N (fun _ => x))
    (induction : ∀ P : R 0, source 0 P (fun _ => zero) →
      (∀ x, source 0 P (fun _ => x) → source 0 P (fun _ => successor x)) →
      ∀ x, source 0 P (fun _ => x)) :
    RepresentsLeast (interpretation source zero tag successor) N := by
  intro x
  constructor
  · intro _ P closed
    apply induction P _ _ x
    · simpa [member, modelZero, interpretation, Ne.symm distinct] using closed.1
    · intro y hy
      simpa [member, modelSuccessor, interpretation] using closed.2 y hy
  · intro _
    exact universal x

/-- Reuse of the original graph recursion from the precise data supplied by
a derived Frege-number subtype. Comprehension remains an explicit premise. -/
theorem arithmetic_on_inductive_carrier
    (source : (arity : Nat) → R arity → (Fin (arity + 1) → D) → Prop)
    (zero tag : D) (successor : D → D) (distinct : tag ≠ zero)
    (full : HasFullComprehension (interpretation source zero tag successor))
    (N : R 0) (universal : ∀ x, source 0 N (fun _ => x))
    (induction : ∀ P : R 0, source 0 P (fun _ => zero) →
      (∀ x, source 0 P (fun _ => x) → source 0 P (fun _ => successor x)) →
      ∀ x, source 0 P (fun _ => x))
    (separated : ∀ x, zero ≠ successor x)
    (injective : Function.Injective successor) :
    Nonempty (FullArithmetic (interpretation source zero tag successor) N) :=
  arithmetic source zero tag successor distinct full N
    (least_of_available_induction source zero tag successor distinct N universal induction)
    separated injective

end FregeanECA.Part2.FregeArithmeticAdapter
