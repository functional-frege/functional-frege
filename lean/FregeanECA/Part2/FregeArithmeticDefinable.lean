import FregeanECA.Part2.FregeArithmeticSyntax
import FregeanECA.Part2.Closure

/-! Full comprehension transfers to a definable applicative reduct on a
definable object domain. The application graph is an actual available relation,
and the final wrapper obtains it from an explicit source formula. -/
namespace FregeanECA.Part2.FregeArithmeticDefinable
open Positive
universe u v
variable {D : Type u} {R : Nat → Type v}

abbrev Carrier (M : FregeArithmetic.Interpretation D R) (N : R 0) :=
  {x : D // FregeArithmetic.member M N x}

def reduct (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (app : Carrier M N → Carrier M N → Carrier M N) (k s : Carrier M N) :
    Positive.Interpretation (Carrier M N) R where
  apply := app
  constantK := k
  constantS := s
  satisfies n P xs := M.satisfies n P (fun i => (xs i).val)

def three {A : Type u} (x y z : A) : Fin 3 → A :=
  Fin.cases x (Fin.cases y (fun _ => z))

def GraphsApplication (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (app : Carrier M N → Carrier M N → Carrier M N) (G : R 2) : Prop :=
  ∀ x y : Carrier M N, ∀ z : D,
    M.satisfies 2 G (three x.val y.val z) ↔ z = (app x y).val

structure Slots where
  objects : Nat → Nat
  constantK : Nat
  constantS : Nat
  natural : Nat
  graph : Nat
  predicates : Nat → Nat → Nat

def Slots.shift (slots : Slots) (offset : Nat) : Slots :=
  { slots with objects := fun i => slots.objects i + offset
               constantK := slots.constantK + offset
               constantS := slots.constantS + offset }

def Slots.bindObject (slots : Slots) : Slots :=
  { slots with
    objects := fun i => match i with
      | 0 => 0
      | i + 1 => slots.objects i + 1
    constantK := slots.constantK + 1
    constantS := slots.constantS + 1 }

def Slots.bindPredicate (slots : Slots) (arity : Nat) : Slots :=
  { slots with natural := if arity = 0 then slots.natural + 1 else slots.natural
               graph := if arity = 2 then slots.graph + 1 else slots.graph
               predicates := fun other i => if other = arity then
                 match i with | 0 => 0 | i + 1 => slots.predicates other i + 1
                 else slots.predicates other i }

structure Context (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (k s : Carrier M N) (G : R 2) (slots : Slots)
    (o : ObjectAssignment (Carrier M N)) (t : ObjectAssignment D)
    (r q : PredicateAssignment R) : Prop where
  objects : ∀ i, t (slots.objects i) = (o i).val
  constantK : t slots.constantK = k.val
  constantS : t slots.constantS = s.val
  natural : q 0 slots.natural = N
  graph : q 2 slots.graph = G
  predicates : ∀ a i, q a (slots.predicates a i) = r a i

theorem context_shift {M : FregeArithmetic.Interpretation D R} {N : R 0}
    {k s : Carrier M N} {G : R 2} {slots : Slots}
    {o : ObjectAssignment (Carrier M N)} {t : ObjectAssignment D}
    {r q : PredicateAssignment R} (ctx : Context M N k s G slots o t r q)
    (n : Nat) (xs : Fin n → D) :
    Context M N k s G (slots.shift n) o (assignTuple n xs t) r q := by
  constructor
  · intro i
    simpa [Slots.shift, Nat.add_comm (slots.objects i) n] using ctx.objects i
  · simpa [Slots.shift, Nat.add_comm slots.constantK n] using ctx.constantK
  · simpa [Slots.shift, Nat.add_comm slots.constantS n] using ctx.constantS
  · exact ctx.natural
  · exact ctx.graph
  · exact ctx.predicates

theorem context_bindObject {M : FregeArithmetic.Interpretation D R} {N : R 0}
    {k s : Carrier M N} {G : R 2} {slots : Slots}
    {o : ObjectAssignment (Carrier M N)} {t : ObjectAssignment D}
    {r q : PredicateAssignment R} (ctx : Context M N k s G slots o t r q)
    (x : Carrier M N) :
    Context M N k s G slots.bindObject (pushObject o x) (pushObject t x.val) r q := by
  constructor
  · intro i
    cases i with
    | zero => rfl
    | succ i => exact ctx.objects i
  · exact ctx.constantK
  · exact ctx.constantS
  · exact ctx.natural
  · exact ctx.graph
  · exact ctx.predicates

theorem context_bindPredicate {M : FregeArithmetic.Interpretation D R} {N : R 0}
    {k s : Carrier M N} {G : R 2} {slots : Slots}
    {o : ObjectAssignment (Carrier M N)} {t : ObjectAssignment D}
    {r q : PredicateAssignment R} (ctx : Context M N k s G slots o t r q)
    (a : Nat) (P : R a) :
    Context M N k s G (slots.bindPredicate a) o t
      (pushPredicate r a P) (pushPredicate q a P) := by
  constructor
  · exact ctx.objects
  · exact ctx.constantK
  · exact ctx.constantS
  · by_cases h : a = 0
    · subst a; simpa [Slots.bindPredicate, pushPredicate] using ctx.natural
    · simpa [Slots.bindPredicate, pushPredicate, h, Ne.symm h] using ctx.natural
  · by_cases h : a = 2
    · subst a; simpa [Slots.bindPredicate, pushPredicate] using ctx.graph
    · simpa [Slots.bindPredicate, pushPredicate, h, Ne.symm h] using ctx.graph
  · intro b i
    by_cases h : b = a
    · subst b
      cases i with
      | zero => simp [Slots.bindPredicate, pushPredicate]
      | succ i => simpa [Slots.bindPredicate, pushPredicate] using ctx.predicates a i
    · simpa [Slots.bindPredicate, pushPredicate, h] using ctx.predicates b i

def graphAtom (graph x y z : Nat) : FregeArithmetic.Formula :=
  .relation 2 graph (three (.var x) (.var y) (.var z))

theorem graph_atom_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) (g x y z : Nat) :
    (graphAtom g x y z).truth M o r ↔ M.satisfies 2 (r 2 g) (three (o x) (o y) (o z)) := by
  have vals : (fun i => (three (FregeArithmetic.Term.var x) (.var y) (.var z) i).value M o r) =
      three (o x) (o y) (o z) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
  simp only [graphAtom, FregeArithmetic.Formula.truth, vals]

def termGraph (slots : Slots) : Positive.Term → Nat → FregeArithmetic.Formula
  | .var i, output => .equal (.var output) (.var (slots.objects i))
  | .constantK, output => .equal (.var output) (.var slots.constantK)
  | .constantS, output => .equal (.var output) (.var slots.constantS)
  | .app f x, output => .existsObject (.existsObject
      (.conjunction (termGraph (slots.shift 2) f 1)
        (.conjunction (termGraph (slots.shift 2) x 0)
          (graphAtom slots.graph 1 0 (output + 2)))))

theorem term_graph_truth (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (app : Carrier M N → Carrier M N → Carrier M N) (k s : Carrier M N)
    (G : R 2) (graph : GraphsApplication M N app G) (term : Positive.Term) :
    ∀ slots o t r q, Context M N k s G slots o t r q → ∀ output,
      (termGraph slots term output).truth M t q ↔
        t output = (term.value (reduct M N app k s) o).val := by
  induction term with
  | var i =>
    intro slots o t r q ctx output
    simpa [termGraph, FregeArithmetic.Formula.truth, FregeArithmetic.Term.value,
      Positive.Term.value] using congrArg (fun x => t output = x) (ctx.objects i)
  | constantK =>
    intro slots o t r q ctx output
    simp only [termGraph, FregeArithmetic.Formula.truth, FregeArithmetic.Term.value,
      Positive.Term.value, reduct, ctx.constantK]
  | constantS =>
    intro slots o t r q ctx output
    simp only [termGraph, FregeArithmetic.Formula.truth, FregeArithmetic.Term.value,
      Positive.Term.value, reduct, ctx.constantS]
  | app f x ihf ihx =>
    intro slots o t r q ctx output
    constructor
    · rintro ⟨fv, xv, hf, hx, hg⟩
      have ctx' := context_shift ctx 2 (FregeArithmetic.pair xv fv)
      have ef := (ihf _ o _ r q ctx' 1).mp hf
      have ex := (ihx _ o _ r q ctx' 0).mp hx
      have gh := (graph_atom_truth M _ q slots.graph 1 0 (output + 2)).mp hg
      change fv = _ at ef
      change xv = _ at ex
      change M.satisfies 2 (q 2 slots.graph) (three fv xv (t output)) at gh
      rw [ctx.graph, ef, ex] at gh
      exact (graph _ _ _).mp gh
    · intro h
      let fv := f.value (reduct M N app k s) o
      let xv := x.value (reduct M N app k s) o
      have ctx' := context_shift ctx 2 (FregeArithmetic.pair xv.val fv.val)
      refine ⟨fv.val, xv.val, (ihf _ o _ r q ctx' 1).mpr rfl,
        (ihx _ o _ r q ctx' 0).mpr rfl, ?_⟩
      apply (graph_atom_truth M _ q slots.graph 1 0 (output + 2)).mpr
      change M.satisfies 2 (q 2 slots.graph) (three fv.val xv.val (t output))
      rw [ctx.graph]
      exact (graph fv xv (t output)).mpr h

def existsTuple : Nat → FregeArithmetic.Formula → FregeArithmetic.Formula
  | 0, p => p
  | n + 1, p => existsTuple n (.existsObject p)

theorem existsTuple_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) (n : Nat) (p : FregeArithmetic.Formula) :
    (existsTuple n p).truth M o r ↔ ∃ xs : Fin n → D,
      p.truth M (assignTuple n xs o) r := by
  induction n generalizing p with
  | zero => exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩
  | succ n ih =>
    rw [existsTuple, ih]
    exact ⟨fun ⟨xs, x, h⟩ => ⟨Fin.cases (motive := fun _ => D) x xs, h⟩,
      fun ⟨xs, h⟩ => ⟨fun i => xs i.succ, xs 0, h⟩⟩

def conjunctionTuple : (n : Nat) → (Fin n → FregeArithmetic.Formula) → FregeArithmetic.Formula
  | 0, _ => .implies .falsum .falsum
  | n + 1, fs => .conjunction (fs 0) (conjunctionTuple n (fun i => fs i.succ))

theorem conjunctionTuple_truth (M : FregeArithmetic.Interpretation D R)
    (o : ObjectAssignment D) (r : PredicateAssignment R) (n : Nat)
    (fs : Fin n → FregeArithmetic.Formula) :
    (conjunctionTuple n fs).truth M o r ↔ ∀ i, (fs i).truth M o r := by
  induction n with
  | zero => simp [conjunctionTuple, FregeArithmetic.Formula.truth]
  | succ n ih =>
    simp only [conjunctionTuple, FregeArithmetic.Formula.truth, ih]
    exact ⟨fun h i => Fin.cases h.1 h.2 i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

def bindTerms (slots : Slots) (n : Nat) (terms : Fin n → Positive.Term)
    (body : FregeArithmetic.Formula) : FregeArithmetic.Formula :=
  existsTuple n (.conjunction
    (conjunctionTuple n (fun i => termGraph (slots.shift n) (terms i) i)) body)

theorem bind_terms_truth (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (app : Carrier M N → Carrier M N → Carrier M N) (k s : Carrier M N)
    (G : R 2) (graph : GraphsApplication M N app G)
    (slots : Slots) (o : ObjectAssignment (Carrier M N)) (t : ObjectAssignment D)
    (r q : PredicateAssignment R) (ctx : Context M N k s G slots o t r q)
    (n : Nat) (terms : Fin n → Positive.Term) (body : FregeArithmetic.Formula) :
    (bindTerms slots n terms body).truth M t q ↔
      body.truth M (assignTuple n
        (fun i => ((terms i).value (reduct M N app k s) o).val) t) q := by
  rw [bindTerms, existsTuple_truth]
  simp only [FregeArithmetic.Formula.truth, conjunctionTuple_truth]
  constructor
  · rintro ⟨xs, hs, h⟩
    have same : xs = fun i => ((terms i).value (reduct M N app k s) o).val := by
      funext i
      simpa only [assignTuple_at] using (term_graph_truth M N app k s G graph (terms i) _ _ _ _ _
        (context_shift ctx n xs) i).mp (hs i)
    simpa only [same] using h
  · intro h
    refine ⟨_, ?_, h⟩
    intro i
    apply (term_graph_truth M N app k s G graph (terms i) _ _ _ _ _
      (context_shift ctx n _) i).mpr
    exact assignTuple_at n _ t i

def translate (slots : Slots) : Applicative.Formula → FregeArithmetic.Formula
  | .equal a b => bindTerms slots 2 (FregeArithmetic.pair a b)
      (.equal (.var 0) (.var 1))
  | .relation n i args => bindTerms slots (n + 1) args
      (.relation n (slots.predicates n i) (fun j => .var j))
  | .relationEqual n i j => .relationEqual n (slots.predicates n i) (slots.predicates n j)
  | .falsum => .falsum
  | .implies p q => .implies (translate slots p) (translate slots q)
  | .conjunction p q => .conjunction (translate slots p) (translate slots q)
  | .disjunction p q => .disjunction (translate slots p) (translate slots q)
  | .existsObject p => .existsObject (.conjunction
      (FregeArithmetic.unary slots.natural (.var 0)) (translate slots.bindObject p))
  | .forallObject p => .forallObject (.implies
      (FregeArithmetic.unary slots.natural (.var 0)) (translate slots.bindObject p))
  | .existsPredicate n p => .existsPredicate n (translate (slots.bindPredicate n) p)
  | .forallPredicate n p => .forallPredicate n (translate (slots.bindPredicate n) p)

theorem translation_truth (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (app : Carrier M N → Carrier M N → Carrier M N) (k s : Carrier M N)
    (G : R 2) (graph : GraphsApplication M N app G) (p : Applicative.Formula) :
    ∀ slots o t r q, Context M N k s G slots o t r q →
      ((translate slots p).truth M t q ↔ p.truth (reduct M N app k s) o r) := by
  induction p with
  | equal a b =>
    intro slots o t r q ctx
    rw [translate, bind_terms_truth M N app k s G graph slots o t r q ctx]
    simp only [FregeArithmetic.Formula.truth, FregeArithmetic.Term.value, assignTuple,
      pushObject, FregeArithmetic.pair, Fin.cases_zero, Fin.cases_succ,
      Applicative.Formula.truth]
    exact ⟨Subtype.ext, congrArg Subtype.val⟩
  | relation n i args =>
    intro slots o t r q ctx
    rw [translate, bind_terms_truth M N app k s G graph slots o t r q ctx]
    simp only [FregeArithmetic.Formula.truth, FregeArithmetic.Term.value,
      assignTuple_at, ctx.predicates]
    rfl
  | relationEqual n i j =>
    intro slots o t r q ctx
    simp only [translate, FregeArithmetic.Formula.truth, Applicative.Formula.truth,
      ctx.predicates]
  | falsum => intros; exact Iff.rfl
  | implies p q ihp ihq =>
    intro slots o t r q ctx
    exact imp_congr (ihp slots o t r q ctx) (ihq slots o t r q ctx)
  | conjunction p q ihp ihq =>
    intro slots o t r q ctx
    exact and_congr (ihp slots o t r q ctx) (ihq slots o t r q ctx)
  | disjunction p q ihp ihq =>
    intro slots o t r q ctx
    exact or_congr (ihp slots o t r q ctx) (ihq slots o t r q ctx)
  | existsObject p ih =>
    intro slots o t r q ctx
    change (∃ x : D, FregeArithmetic.member M (q 0 slots.natural) x ∧
      (translate slots.bindObject p).truth M (pushObject t x) q) ↔
      ∃ x : Carrier M N, p.truth (reduct M N app k s) (pushObject o x) r
    rw [ctx.natural]
    exact ⟨fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩,
      (ih _ _ _ _ _ (context_bindObject ctx ⟨x, hx⟩)).mp h⟩,
      fun ⟨x, h⟩ => ⟨x.val, x.property,
        (ih _ _ _ _ _ (context_bindObject ctx x)).mpr h⟩⟩
  | forallObject p ih =>
    intro slots o t r q ctx
    change (∀ x : D, FregeArithmetic.member M (q 0 slots.natural) x →
      (translate slots.bindObject p).truth M (pushObject t x) q) ↔
      ∀ x : Carrier M N, p.truth (reduct M N app k s) (pushObject o x) r
    rw [ctx.natural]
    exact ⟨fun h x => (ih _ _ _ _ _ (context_bindObject ctx x)).mp (h x.val x.property),
      fun h x hx => (ih _ _ _ _ _ (context_bindObject ctx ⟨x, hx⟩)).mpr (h ⟨x, hx⟩)⟩
  | existsPredicate n p ih =>
    intro slots o t r q ctx
    exact exists_congr (fun P => ih _ _ _ _ _ (context_bindPredicate ctx n P))
  | forallPredicate n p ih =>
    intro slots o t r q ctx
    exact forall_congr' (fun P => ih _ _ _ _ _ (context_bindPredicate ctx n P))

def initialSlots : Slots where
  objects i := i + 2
  constantK := 0
  constantS := 1
  natural := 0
  graph := 0
  predicates a i := if a = 0 ∨ a = 2 then i + 1 else i

theorem initial_context (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (k s : Carrier M N) (G : R 2) (o : ObjectAssignment (Carrier M N))
    (r : PredicateAssignment R) :
    Context M N k s G initialSlots o
      (pushObject (pushObject (fun i => (o i).val) s.val) k.val)
      r (pushPredicate (pushPredicate r 0 N) 2 G) := by
  constructor
  · intro i; rfl
  · rfl
  · rfl
  · simp [initialSlots, pushPredicate]
  · simp [initialSlots, pushPredicate]
  · intro a i
    by_cases h0 : a = 0
    · subst a; simp [initialSlots, pushPredicate]
    · by_cases h2 : a = 2
      · subst a; simp [initialSlots, pushPredicate]
      · simp [initialSlots, pushPredicate, h0, h2]

def Slots.bindTuple : Nat → Slots → Slots
  | 0, slots => slots
  | n + 1, slots => (slots.bindTuple n).bindObject

theorem context_bindTuple {M : FregeArithmetic.Interpretation D R} {N : R 0}
    {k s : Carrier M N} {G : R 2} {slots : Slots}
    {o : ObjectAssignment (Carrier M N)} {t : ObjectAssignment D}
    {r q : PredicateAssignment R} (ctx : Context M N k s G slots o t r q)
    (n : Nat) (xs : Fin n → Carrier M N) :
    Context M N k s G (slots.bindTuple n) (assignTuple n xs o)
      (assignTuple n (fun i => (xs i).val) t) r q := by
  induction n with
  | zero => exact ctx
  | succ n ih => exact context_bindObject (ih (fun i => xs i.succ)) (xs 0)

/-- All full applicative comprehension instances are supplied by source
comprehension, once the application operation has this actual graph. -/
theorem full_comprehension_of_graph (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (app : Carrier M N → Carrier M N → Carrier M N) (k s : Carrier M N)
    (full : FregeArithmetic.HasFullComprehension M)
    (G : R 2) (graph : GraphsApplication M N app G) :
    HasFullComprehension (reduct M N app k s) := by
  refine ⟨full.relations_nonempty, ?_⟩
  intro n p o r
  let t := pushObject (pushObject (fun i => (o i).val) s.val) k.val
  let q := pushPredicate (pushPredicate r 0 N) 2 G
  obtain ⟨P, law⟩ := full.comprehend n (translate (initialSlots.bindTuple (n + 1)) p) t q
  refine ⟨P, ?_⟩
  intro xs
  exact (law (fun i => (xs i).val)).trans
    (translation_truth M N app k s G graph p _ _ _ _ _
      (context_bindTuple (initial_context M N k s G o r) (n + 1) xs))

/-- The application graph need not be separately postulated: a source formula
with parameters and its truth lemma suffice, by the actual source schema. -/
theorem full_comprehension_of_formula (M : FregeArithmetic.Interpretation D R) (N : R 0)
    (app : Carrier M N → Carrier M N → Carrier M N) (k s : Carrier M N)
    (full : FregeArithmetic.HasFullComprehension M) (p : FregeArithmetic.Formula)
    (o : ObjectAssignment D) (r : PredicateAssignment R)
    (law : ∀ x y : Carrier M N, ∀ z : D,
      p.truth M (assignTuple 3 (three x.val y.val z) o) r ↔ z = (app x y).val) :
    HasFullComprehension (reduct M N app k s) := by
  obtain ⟨G, represents⟩ := full.comprehend 2 p o r
  apply full_comprehension_of_graph M N app k s full G
  intro x y z
  exact (represents (three x.val y.val z)).trans (law x y z)

end FregeanECA.Part2.FregeArithmeticDefinable
