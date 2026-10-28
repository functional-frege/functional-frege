import FregeanECA.Part2.FregeArithmeticSyntax
import FregeanECA.Part2.HumeInternal

/-! Interpretation of the generic Frege-Arithmetic language by the internal
cardinal graph. The source object domain is the derived number domain.
Its relation sorts remain the actual available target relation sorts.
-/

namespace FregeanECA.Part2.FregeArithmeticInterpretation
open Positive Arithmetic HumeInternal
universe u v
variable {D : Type u} {R : Nat → Type v}

abbrev Number (M : Positive.Interpretation D R) (N : R 0) :=
  {x : D // member M N x}

noncomputable def number (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    (P : R 0) : Number M N :=
  ⟨Classical.choose (code_total_unique M full domain P),
    code_natural M domain (Classical.choose_spec (code_total_unique M full domain P)).1⟩

theorem number_code (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    (P : R 0) : Code M N P (number M full domain P).val :=
  (Classical.choose_spec (code_total_unique M full domain P)).1

theorem code_iff_number (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    (P : R 0) (a : D) : Code M N P a ↔ a = (number M full domain P).val := by
  constructor
  · exact (Classical.choose_spec (code_total_unique M full domain P)).2 a
  · intro same
    rw [same]
    exact number_code M full domain P

noncomputable def interpretedModel (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N) :
    FregeArithmetic.Interpretation (Number M N) R where
  satisfies n P xs := M.satisfies n P (fun i => (xs i).val)
  number := number M full domain

/-- Skip the reserved unary predicate slot that names the number domain. -/
def skip : Nat → Nat → Nat
  | 0, i => i + 1
  | k + 1, 0 => 0
  | k + 1, i + 1 => skip k i + 1

def predicateIndex (natural : Nat) : Nat → Nat → Nat
  | 0, i => skip natural i
  | _ + 1, i => i

def nextNatural (natural arity : Nat) : Nat :=
  match arity with
  | 0 => natural + 1
  | _ + 1 => natural

structure Context (natural : Nat) (N : R 0)
    (source target : PredicateAssignment R) : Prop where
  names : target 0 natural = N
  lookup : ∀ arity i, target arity (predicateIndex natural arity i) = source arity i

theorem initial_context (N : R 0) (r : PredicateAssignment R) :
    Context 0 N r (pushPredicate r 0 N) := by
  constructor
  · simp [pushPredicate]
  · intro arity i
    cases arity <;> simp [predicateIndex, skip, pushPredicate]

theorem context_push {natural : Nat} {N : R 0} {s t : PredicateAssignment R}
    (ctx : Context natural N s t) (arity : Nat) (P : R arity) :
    Context (nextNatural natural arity) N
      (pushPredicate s arity P) (pushPredicate t arity P) := by
  constructor
  · cases arity <;> simpa [nextNatural, pushPredicate] using ctx.names
  · intro other i
    cases arity with
    | zero =>
      cases other with
      | zero =>
        cases i with
        | zero => simp [nextNatural, predicateIndex, skip, pushPredicate]
        | succ i =>
          simpa [nextNatural, predicateIndex, skip, pushPredicate] using ctx.lookup 0 i
      | succ other =>
        simpa [nextNatural, predicateIndex, pushPredicate] using ctx.lookup (other + 1) i
    | succ arity =>
      cases other with
      | zero =>
        simpa [nextNatural, predicateIndex, pushPredicate] using ctx.lookup 0 i
      | succ other =>
        by_cases same : other = arity
        · subst other
          cases i with
          | zero => simp [nextNatural, predicateIndex, pushPredicate]
          | succ i =>
            simpa [nextNatural, predicateIndex, pushPredicate] using ctx.lookup (arity + 1) i
        · simpa [nextNatural, predicateIndex, pushPredicate, same] using ctx.lookup (other + 1) i

end FregeanECA.Part2.FregeArithmeticInterpretation
