import FregeanECA.Part2.FregeArithmeticInterpretation
import FregeanECA.Part2.FormulaTuples
import FregeanECA.Part2.FregeArithmeticHumeModel

/-! A compositional translation of the complete source Frege-Arithmetic
grammar, including number terms and arbitrarily nested relation quantifiers.
Fresh object witnesses eliminate number terms using the proved Code graph.
-/

namespace FregeanECA.Part2.FregeArithmeticInterpretation
open Positive Arithmetic HumeInternal FormulaTuples
universe u v
variable {D : Type u} {R : Nat → Type v}

def termGraph (natural offset : Nat) : FregeArithmetic.Term → Positive.Term → Applicative.Formula
  | .var i, output => .equal output (.var (i + offset))
  | .number i, output => codeFormula natural (predicateIndex natural 0 i) output

theorem term_graph_truth (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    (o : ObjectAssignment (Number M N)) {s t : PredicateAssignment R}
    {natural : Nat} (ctx : Context natural N s t)
    (k : Nat) (xs : Fin k → D) (term : FregeArithmetic.Term) (output : Positive.Term) :
    (termGraph natural k term output).truth M (assignTuple k xs (fun i => (o i).val)) t ↔
      output.value M (assignTuple k xs (fun i => (o i).val)) =
        (term.value (interpretedModel M full domain) o s).val := by
  cases term with
  | var i =>
    simp [termGraph, Applicative.Formula.truth, FregeArithmetic.Term.value,
      Positive.Term.value, Nat.add_comm i k]
  | number i =>
    rw [termGraph, code_formula_truth, ctx.names, ctx.lookup 0 i]
    exact code_iff_number M full domain (s 0 i) _

def bindTerms (natural k : Nat) (terms : Fin k → FregeArithmetic.Term)
    (body : Applicative.Formula) : Applicative.Formula :=
  existsTuple k (.conjunction
    (conjunctionTuple k (fun i => termGraph natural k (terms i) (.var i))) body)

theorem bind_terms_truth (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    (o : ObjectAssignment (Number M N)) {s t : PredicateAssignment R}
    {natural : Nat} (ctx : Context natural N s t)
    (k : Nat) (terms : Fin k → FregeArithmetic.Term) (body : Applicative.Formula) :
    (bindTerms natural k terms body).truth M (fun i => (o i).val) t ↔
      body.truth M (assignTuple k
        (fun i => ((terms i).value (interpretedModel M full domain) o s).val)
        (fun i => (o i).val)) t := by
  rw [bindTerms, existsTuple_truth]
  simp only [Applicative.Formula.truth, conjunctionTuple_truth,
    term_graph_truth M full domain o ctx, Positive.Term.value, assignTuple_at]
  constructor
  · rintro ⟨xs, law, h⟩
    have same := funext law
    simpa only [same] using h
  · intro h
    exact ⟨_, fun _ => rfl, h⟩

def translate (natural : Nat) : FregeArithmetic.Formula → Applicative.Formula
  | .equal a b => bindTerms natural 2 (HumeOrder.pair a b) (.equal (.var 0) (.var 1))
  | .relation n i args => bindTerms natural (n + 1) args
      (.relation n (predicateIndex natural n i) (fun j => .var j))
  | .relationEqual n i j =>
      .relationEqual n (predicateIndex natural n i) (predicateIndex natural n j)
  | .falsum => .falsum
  | .implies p q => .implies (translate natural p) (translate natural q)
  | .conjunction p q => .conjunction (translate natural p) (translate natural q)
  | .disjunction p q => .disjunction (translate natural p) (translate natural q)
  | .existsObject p => .existsObject
      (.conjunction (unary natural (.var 0)) (translate natural p))
  | .forallObject p => .forallObject
      (.implies (unary natural (.var 0)) (translate natural p))
  | .existsPredicate n p => .existsPredicate n (translate (nextNatural natural n) p)
  | .forallPredicate n p => .forallPredicate n (translate (nextNatural natural n) p)

theorem push_values (M : Positive.Interpretation D R) {N : R 0}
    (o : ObjectAssignment (Number M N)) (x : Number M N) :
    (fun i => (pushObject o x i).val) = pushObject (fun i => (o i).val) x.val := by
  funext i
  cases i <;> rfl

theorem translation_truth (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N)
    (p : FregeArithmetic.Formula) :
    ∀ (natural : Nat) (o : ObjectAssignment (Number M N)) (s t : PredicateAssignment R),
      Context natural N s t →
      ((translate natural p).truth M (fun i => (o i).val) t ↔
        p.truth (interpretedModel M full domain) o s) := by
  induction p with
  | equal a b =>
    intro natural o s t ctx
    rw [translate, bind_terms_truth M full domain o ctx]
    simp only [Applicative.Formula.truth, Positive.Term.value, assignTuple,
      pushObject, HumeOrder.pair, Fin.cases_zero, Fin.cases_succ,
      FregeArithmetic.Formula.truth]
    exact Subtype.val_inj
  | relation n i args =>
    intro natural o s t ctx
    rw [translate, bind_terms_truth M full domain o ctx]
    simp only [Applicative.Formula.truth, Positive.Term.value, assignTuple_at,
      ctx.lookup]
    rfl
  | relationEqual n i j =>
    intro natural o s t ctx
    simp only [translate, Applicative.Formula.truth, FregeArithmetic.Formula.truth,
      ctx.lookup]
  | falsum => intros; exact Iff.rfl
  | implies p q ihp ihq =>
    intro natural o s t ctx
    exact imp_congr (ihp natural o s t ctx) (ihq natural o s t ctx)
  | conjunction p q ihp ihq =>
    intro natural o s t ctx
    exact and_congr (ihp natural o s t ctx) (ihq natural o s t ctx)
  | disjunction p q ihp ihq =>
    intro natural o s t ctx
    exact or_congr (ihp natural o s t ctx) (ihq natural o s t ctx)
  | existsObject p ih =>
    intro natural o s t ctx
    change (∃ x : D, member M (t 0 natural) x ∧
      (translate natural p).truth M (pushObject (fun i => (o i).val) x) t) ↔
      ∃ x : Number M N, p.truth (interpretedModel M full domain) (pushObject o x) s
    rw [ctx.names]
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨⟨x, hx⟩, (ih natural (pushObject o ⟨x, hx⟩) s t ctx).mp ?_⟩
      simpa only [push_values] using h
    · rintro ⟨x, h⟩
      refine ⟨x.val, x.property, ?_⟩
      simpa only [push_values] using (ih natural (pushObject o x) s t ctx).mpr h
  | forallObject p ih =>
    intro natural o s t ctx
    change (∀ x : D, member M (t 0 natural) x →
      (translate natural p).truth M (pushObject (fun i => (o i).val) x) t) ↔
      ∀ x : Number M N, p.truth (interpretedModel M full domain) (pushObject o x) s
    rw [ctx.names]
    constructor
    · intro h x
      apply (ih natural (pushObject o x) s t ctx).mp
      simpa only [push_values] using h x.val x.property
    · intro h x hx
      simpa only [push_values] using
        (ih natural (pushObject o ⟨x, hx⟩) s t ctx).mpr (h ⟨x, hx⟩)
  | existsPredicate n p ih =>
    intro natural o s t ctx
    exact exists_congr (fun P => ih (nextNatural natural n) o
      (pushPredicate s n P) (pushPredicate t n P) (context_push ctx n P))
  | forallPredicate n p ih =>
    intro natural o s t ctx
    exact forall_congr' (fun P => ih (nextNatural natural n) o
      (pushPredicate s n P) (pushPredicate t n P) (context_push ctx n P))

theorem assignTuple_values (M : Positive.Interpretation D R) {N : R 0}
    (k : Nat) (xs : Fin k → Number M N) (o : ObjectAssignment (Number M N)) :
    (fun i => (assignTuple k xs o i).val) =
      assignTuple k (fun i => (xs i).val) (fun i => (o i).val) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [assignTuple, push_values, ih]

/-- Every comprehension instance of the actual source HP language, including
number terms and arbitrary nested quantifiers, is supplied by Part II. -/
theorem interpreted_full_comprehension (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N) :
    FregeArithmetic.HasFullComprehension (interpretedModel M full domain) := by
  refine ⟨full.relations_nonempty, ?_⟩
  intro n p o r
  obtain ⟨P, law⟩ := full.comprehend n (translate 0 p)
    (fun i => (o i).val) (pushPredicate r 0 N)
  refine ⟨P, ?_⟩
  intro xs
  have truth := translation_truth M full domain p 0 (assignTuple (n + 1) xs o)
    r (pushPredicate r 0 N) (initial_context N r)
  rw [assignTuple_values] at truth
  exact (law (fun i => (xs i).val)).trans truth

/-- Both HP and full comprehension hold in the source-language structure.
This is a complete semantic interpretation, not just the HP biconditional. -/
theorem interpreted_full_conditions (M : Positive.Interpretation D R)
    (full : HasFullComprehension M) {N : R 0} (domain : PeanoDomain M N) :
    FregeArithmetic.FullConditions (interpretedModel M full domain) :=
  ⟨interpreted_full_comprehension M full domain,
    FregeArithmeticHumeModel.interpreted_hume_principle M full domain⟩

end FregeanECA.Part2.FregeArithmeticInterpretation

#print axioms FregeanECA.Part2.FregeArithmeticInterpretation.translation_truth
#print axioms FregeanECA.Part2.FregeArithmeticInterpretation.interpreted_full_conditions
