import FregeanECA.Part2.ArithmeticGraphs

/-! Actual second-order arithmetic syntax and its Henkin interpretation.
Numbers are the represented least inductive domain, not an assumed copy of
standard Nat. Sets identify available predicates precisely when their
restrictions to that number domain agree. -/

namespace FregeanECA.Part2.SecondOrderArithmetic
open Positive Arithmetic
universe u v
variable {D : Type u} {R : Nat → Type v}

abbrev Number (M : Interpretation D R) (N : R 0) := {x : D // member M N x}

/-- Extensional sets on the interpreted numbers, represented by available
unary predicates. Duplicate target representatives are intentionally allowed. -/
def SetDomain (M : Interpretation D R) (N : R 0) :=
  {s : Number M N → Prop // ∃ P : R 0, ∀ x, s x ↔ member M P x.val}

def representedSet (M : Interpretation D R) (N : R 0) (P : R 0) : SetDomain M N :=
  ⟨fun x => member M P x.val, P, fun _ => Iff.rfl⟩

theorem representedSet_surjective (M : Interpretation D R) (N : R 0) :
    Function.Surjective (representedSet M N) := by
  rintro ⟨s, P, law⟩
  refine ⟨P, ?_⟩
  apply Subtype.ext
  funext x
  exact propext (law x).symm

theorem set_identity_iff_coextension (M : Interpretation D R) (N : R 0)
    (X Y : SetDomain M N) : X = Y ↔ ∀ x, X.val x ↔ Y.val x := by
  constructor
  · intro same; subst Y; exact fun _ => Iff.rfl
  · intro same
    apply Subtype.ext
    exact funext (fun x => propext (same x))

/-- The semantic operations needed to evaluate genuine arithmetic terms.
Their construction from total unique graphs is separate from syntax. -/
structure Operations (M : Interpretation D R) (N : R 0) where
  domain : PeanoDomain M N
  add : Number M N → Number M N → Number M N
  multiply : Number M N → Number M N → Number M N

def Operations.zero {M : Interpretation D R} {N : R 0}
    (A : Operations M N) : Number M N := ⟨modelZero M, A.domain.zero_member⟩

def Operations.successor {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (x : Number M N) : Number M N :=
  ⟨modelSuccessor M x.val, A.domain.successor_closed x.val x.property⟩

inductive Term where
  | var (index : Nat)
  | zero
  | successor (argument : Term)
  | add (left right : Term)
  | multiply (left right : Term)

def Term.value {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (numbers : Nat → Number M N) : Term → Number M N
  | .var i => numbers i
  | .zero => A.zero
  | .successor t => A.successor (t.value A numbers)
  | .add s t => A.add (s.value A numbers) (t.value A numbers)
  | .multiply s t => A.multiply (s.value A numbers) (t.value A numbers)

inductive Formula where
  | equal (left right : Term)
  | member (term : Term) (setIndex : Nat)
  | setEqual (left right : Nat)
  | falsum
  | implies (left right : Formula)
  | conjunction (left right : Formula)
  | disjunction (left right : Formula)
  | existsNumber (body : Formula)
  | forallNumber (body : Formula)
  | existsSet (body : Formula)
  | forallSet (body : Formula)

def Formula.truth {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (numbers : Nat → Number M N)
    (sets : Nat → SetDomain M N) : Formula → Prop
  | .equal s t => s.value A numbers = t.value A numbers
  | .member t i => (sets i).val (t.value A numbers)
  | .setEqual i j => sets i = sets j
  | .falsum => False
  | .implies p q => p.truth A numbers sets → q.truth A numbers sets
  | .conjunction p q => p.truth A numbers sets ∧ q.truth A numbers sets
  | .disjunction p q => p.truth A numbers sets ∨ q.truth A numbers sets
  | .existsNumber p => ∃ n, p.truth A (pushObject numbers n) sets
  | .forallNumber p => ∀ n, p.truth A (pushObject numbers n) sets
  | .existsSet p => ∃ X, p.truth A numbers (pushObject sets X)
  | .forallSet p => ∀ X, p.truth A numbers (pushObject sets X)

def Formula.renameSets (map : Nat → Nat) : Formula → Formula
  | .equal s t => .equal s t
  | .member t i => .member t (map i)
  | .setEqual i j => .setEqual (map i) (map j)
  | .falsum => .falsum
  | .implies p q => .implies (p.renameSets map) (q.renameSets map)
  | .conjunction p q => .conjunction (p.renameSets map) (q.renameSets map)
  | .disjunction p q => .disjunction (p.renameSets map) (q.renameSets map)
  | .existsNumber p => .existsNumber (p.renameSets map)
  | .forallNumber p => .forallNumber (p.renameSets map)
  | .existsSet p => .existsSet (p.renameSets (Functional.bindMap map))
  | .forallSet p => .forallSet (p.renameSets (Functional.bindMap map))

def iffF (p q : Formula) : Formula := .conjunction (.implies p q) (.implies q p)

def comprehension (body : Formula) : Formula :=
  .existsSet (.forallNumber (iffF (.member (.var 0) 0) (body.renameSets Nat.succ)))

/-- The usual second-order induction axiom. Together with the full scheme it
entails induction for every source formula, with number and set parameters. -/
def inductionAxiom : Formula := .forallSet (.implies
  (.conjunction (.member .zero 0)
    (.forallNumber (.implies (.member (.var 0) 0) (.member (.successor (.var 0)) 0))))
  (.forallNumber (.member (.var 0) 0)))

def extensionalityAxiom : Formula := .forallSet (.forallSet (.implies
  (.forallNumber (iffF (.member (.var 0) 0) (.member (.var 0) 1)))
  (.setEqual 0 1)))

/-- Z2 in an equivalent first-coordinate recursion presentation. The induction
axiom is second-order induction; comprehension admits every classical formula. -/
inductive Axiom : Formula → Prop where
  | zeroNotSuccessor : Axiom (.forallNumber
      (.implies (.equal .zero (.successor (.var 0))) .falsum))
  | successorInjective : Axiom (.forallNumber (.forallNumber
      (.implies (.equal (.successor (.var 0)) (.successor (.var 1)))
        (.equal (.var 0) (.var 1)))))
  | additionZero : Axiom (.forallNumber (.equal (.add .zero (.var 0)) (.var 0)))
  | additionSuccessor : Axiom (.forallNumber (.forallNumber
      (.equal (.add (.successor (.var 0)) (.var 1))
        (.successor (.add (.var 0) (.var 1))))))
  | multiplicationZero : Axiom (.forallNumber (.equal (.multiply .zero (.var 0)) .zero))
  | multiplicationSuccessor : Axiom (.forallNumber (.forallNumber
      (.equal (.multiply (.successor (.var 0)) (.var 1))
        (.add (.multiply (.var 0) (.var 1)) (.var 1)))))
  | induction : Axiom inductionAxiom
  | extensionality : Axiom extensionalityAxiom
  | comprehend (body : Formula) : Axiom (comprehension body)

def Valid {M : Interpretation D R} {N : R 0} (A : Operations M N) (p : Formula) : Prop :=
  ∀ numbers sets, p.truth A numbers sets

def renameTerm (map : Nat → Nat) : Positive.Term → Positive.Term
  | .var i => .var (map i)
  | .constantK => .constantK
  | .constantS => .constantS
  | .app s t => .app (renameTerm map s) (renameTerm map t)

theorem renameTerm_value (M : Interpretation D R) (map : Nat → Nat)
    (term : Positive.Term) (objects : ObjectAssignment D) :
    (renameTerm map term).value M objects = term.value M (fun i => objects (map i)) := by
  induction term with
  | var _ => rfl
  | constantK => rfl
  | constantS => rfl
  | app _ _ hs ht => change M.apply _ _ = M.apply _ _; rw [hs, ht]

def triple {X : Type u} (x y z : X) : Fin 3 → X :=
  Fin.cases x (Fin.cases y (fun _ => z))

theorem triple_eq_arithmetic {X : Type u} (x y z : X) :
    triple x y z = Arithmetic.triple x y z := rfl

/-- A term's value is expressed by arithmetic graphs. Auxiliary bound object
variables are local witnesses, not new computational function symbols. -/
def Term.graph (addition multiplication : Nat) (variables : Nat → Positive.Term)
    (output : Positive.Term) : Term → Applicative.Formula
  | .var i => .equal output (variables i)
  | .zero => .equal output zeroTerm
  | .successor t => .existsObject (.conjunction
      (t.graph addition multiplication (fun i => renameTerm Nat.succ (variables i)) (.var 0))
      (.equal (renameTerm Nat.succ output) (successorTerm (.var 0))))
  | .add s t => .existsObject (.existsObject (.conjunction
      (s.graph addition multiplication (fun i => renameTerm (fun n => n+2) (variables i)) (.var 1))
      (.conjunction
        (t.graph addition multiplication (fun i => renameTerm (fun n => n+2) (variables i)) (.var 0))
        (.relation 2 addition (triple (.var 1) (.var 0) (renameTerm (fun n => n+2) output))))))
  | .multiply s t => .existsObject (.existsObject (.conjunction
      (s.graph addition multiplication (fun i => renameTerm (fun n => n+2) (variables i)) (.var 1))
      (.conjunction
        (t.graph addition multiplication (fun i => renameTerm (fun n => n+2) (variables i)) (.var 0))
        (.relation 2 multiplication (triple (.var 1) (.var 0) (renameTerm (fun n => n+2) output))))))

structure GraphBindings {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (addition multiplication : Nat)
    (predicates : PredicateAssignment R) : Prop where
  add : ∀ (x y : Number M N) (z : D),
    M.satisfies 2 (predicates 2 addition) (triple x.val y.val z) ↔ z = (A.add x y).val
  multiply : ∀ (x y : Number M N) (z : D),
    M.satisfies 2 (predicates 2 multiplication) (triple x.val y.val z) ↔
      z = (A.multiply x y).val

theorem value_triple (M : Interpretation D R) (objects : ObjectAssignment D)
    (x y z : Positive.Term) :
    (fun i => (triple x y z i).value M objects) =
      triple (x.value M objects) (y.value M objects) (z.value M objects) := by
  funext i
  refine Fin.cases rfl (fun i => ?_) i
  exact Fin.cases rfl (fun _ => rfl) i

/-- Graph elimination preserves the value of every nested arithmetic term. -/
theorem Term.graph_truth {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (addition multiplication : Nat)
    (predicates : PredicateAssignment R) (graphs : GraphBindings A addition multiplication predicates)
    (term : Term) (numbers : Nat → Number M N) :
    ∀ (variables : Nat → Positive.Term) (output : Positive.Term) (objects : ObjectAssignment D),
      (∀ i, (variables i).value M objects = (numbers i).val) →
      ((term.graph addition multiplication variables output).truth M objects predicates ↔
        output.value M objects = (term.value A numbers).val) := by
  induction term with
  | var i =>
      intro variables output objects assigned
      simp only [Term.graph, Applicative.Formula.truth, Term.value, assigned]
  | zero => intros; exact Iff.rfl
  | successor term ih =>
      intro variables output objects assigned
      have inner (x : D) := ih (fun i => renameTerm Nat.succ (variables i)) (.var 0)
        (pushObject objects x) (by intro i; simpa only [renameTerm_value, pushObject] using assigned i)
      simp only [Term.graph, Applicative.Formula.truth, inner, renameTerm_value,
        Positive.Term.value, successorTerm, pushObject, Term.value, Operations.successor]
      constructor
      · rintro ⟨x, rfl, h⟩; exact h
      · intro h; exact ⟨_, rfl, h⟩
  | add s t hs ht =>
      intro variables output objects assigned
      have left (x y : D) := hs (fun i => renameTerm (fun n => n+2) (variables i)) (.var 1)
        (pushObject (pushObject objects x) y)
        (by intro i; simpa only [renameTerm_value, pushObject] using assigned i)
      have right (x y : D) := ht (fun i => renameTerm (fun n => n+2) (variables i)) (.var 0)
        (pushObject (pushObject objects x) y)
        (by intro i; simpa only [renameTerm_value, pushObject] using assigned i)
      simp only [Term.graph, Applicative.Formula.truth, left, right, value_triple,
        renameTerm_value, Positive.Term.value, pushObject, Term.value]
      constructor
      · rintro ⟨x, y, rfl, rfl, h⟩
        exact (graphs.add _ _ _).mp h
      · intro h
        exact ⟨_, _, rfl, rfl, (graphs.add _ _ _).mpr h⟩
  | multiply s t hs ht =>
      intro variables output objects assigned
      have left (x y : D) := hs (fun i => renameTerm (fun n => n+2) (variables i)) (.var 1)
        (pushObject (pushObject objects x) y)
        (by intro i; simpa only [renameTerm_value, pushObject] using assigned i)
      have right (x y : D) := ht (fun i => renameTerm (fun n => n+2) (variables i)) (.var 0)
        (pushObject (pushObject objects x) y)
        (by intro i; simpa only [renameTerm_value, pushObject] using assigned i)
      simp only [Term.graph, Applicative.Formula.truth, left, right, value_triple,
        renameTerm_value, Positive.Term.value, pushObject, Term.value]
      constructor
      · rintro ⟨x, y, rfl, rfl, h⟩
        exact (graphs.multiply _ _ _).mp h
      · intro h
        exact ⟨_, _, rfl, rfl, (graphs.multiply _ _ _).mpr h⟩

def Formula.translate (natural addition multiplication : Nat)
    (numbers sets : Nat → Nat) : Formula → Applicative.Formula
  | .equal s t => .existsObject (.conjunction
      (s.graph addition multiplication (fun i => .var (numbers i + 1)) (.var 0))
      (t.graph addition multiplication (fun i => .var (numbers i + 1)) (.var 0)))
  | .member t i => .existsObject (.conjunction
      (t.graph addition multiplication (fun i => .var (numbers i + 1)) (.var 0))
      (unary (sets i) (.var 0)))
  | .setEqual i j => .forallObject (.implies (unary natural (.var 0))
      (.conjunction (.implies (unary (sets i) (.var 0)) (unary (sets j) (.var 0)))
        (.implies (unary (sets j) (.var 0)) (unary (sets i) (.var 0)))))
  | .falsum => .falsum
  | .implies p q => .implies (p.translate natural addition multiplication numbers sets)
      (q.translate natural addition multiplication numbers sets)
  | .conjunction p q => .conjunction (p.translate natural addition multiplication numbers sets)
      (q.translate natural addition multiplication numbers sets)
  | .disjunction p q => .disjunction (p.translate natural addition multiplication numbers sets)
      (q.translate natural addition multiplication numbers sets)
  | .existsNumber p => .existsObject (.conjunction (unary natural (.var 0))
      (p.translate natural addition multiplication (Functional.bindMap numbers) sets))
  | .forallNumber p => .forallObject (.implies (unary natural (.var 0))
      (p.translate natural addition multiplication (Functional.bindMap numbers) sets))
  | .existsSet p => .existsPredicate 0
      (p.translate (natural+1) addition multiplication numbers (Functional.bindMap sets))
  | .forallSet p => .forallPredicate 0
      (p.translate (natural+1) addition multiplication numbers (Functional.bindMap sets))

structure Bindings {M : Interpretation D R} {N : R 0} (A : Operations M N)
    (natural addition multiplication : Nat) (nm sm : Nat → Nat)
    (numbers : Nat → Number M N) (sets : Nat → SetDomain M N)
    (objects : ObjectAssignment D) (predicates : PredicateAssignment R) : Prop where
  natural : predicates 0 natural = N
  numbers : ∀ i, objects (nm i) = (numbers i).val
  sets : ∀ i, representedSet M N (predicates 0 (sm i)) = sets i
  graphs : GraphBindings A addition multiplication predicates

theorem Bindings.member {M : Interpretation D R} {N : R 0} {A : Operations M N}
    {natural addition multiplication : Nat} {nm sm : Nat → Nat}
    {numbers : Nat → Number M N} {sets : Nat → SetDomain M N}
    {objects : ObjectAssignment D} {predicates : PredicateAssignment R}
    (bindings : Bindings A natural addition multiplication nm sm numbers sets objects predicates)
    (i : Nat) (x : Number M N) :
    member M (predicates 0 (sm i)) x.val ↔ (sets i).val x := by
  change (representedSet M N (predicates 0 (sm i))).val x ↔ _
  rw [bindings.sets i]

theorem Bindings.numberBinder {M : Interpretation D R} {N : R 0} {A : Operations M N}
    {natural addition multiplication : Nat} {nm sm : Nat → Nat}
    {numbers : Nat → Number M N} {sets : Nat → SetDomain M N}
    {objects : ObjectAssignment D} {predicates : PredicateAssignment R}
    (bindings : Bindings A natural addition multiplication nm sm numbers sets objects predicates)
    (x : Number M N) :
    Bindings A natural addition multiplication (Functional.bindMap nm) sm
      (pushObject numbers x) sets (pushObject objects x.val) predicates where
  natural := bindings.natural
  numbers := by intro i; cases i with | zero => rfl | succ i => exact bindings.numbers i
  sets := bindings.sets
  graphs := bindings.graphs

theorem Bindings.setBinder {M : Interpretation D R} {N : R 0} {A : Operations M N}
    {natural addition multiplication : Nat} {nm sm : Nat → Nat}
    {numbers : Nat → Number M N} {sets : Nat → SetDomain M N}
    {objects : ObjectAssignment D} {predicates : PredicateAssignment R}
    (bindings : Bindings A natural addition multiplication nm sm numbers sets objects predicates)
    (P : R 0) :
    Bindings A (natural+1) addition multiplication nm (Functional.bindMap sm)
      numbers (pushObject sets (representedSet M N P)) objects (pushPredicate predicates 0 P) where
  natural := by simpa [pushPredicate] using bindings.natural
  numbers := bindings.numbers
  sets := by
    intro i
    cases i with
    | zero => simp [Functional.bindMap, pushPredicate, pushObject]
    | succ i => simpa [Functional.bindMap, pushPredicate, pushObject] using bindings.sets i
  graphs := {
    add := by intro x y z; simpa [pushPredicate] using bindings.graphs.add x y z
    multiply := by intro x y z; simpa [pushPredicate] using bindings.graphs.multiply x y z }

/-- Every source formula has the same truth as its explicit graph/guard
translation. Set quantifiers range over all represented subsets, via the
proved surjection from available unary predicates. -/
theorem Formula.translation_preserves_truth {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (p : Formula) :
    ∀ natural addition multiplication nm sm numbers sets objects predicates,
      Bindings A natural addition multiplication nm sm numbers sets objects predicates →
      ((p.translate natural addition multiplication nm sm).truth M objects predicates ↔
        p.truth A numbers sets) := by
  induction p with
  | equal s t =>
      intro natural addition multiplication nm sm numbers sets objects predicates bindings
      have hs (x : D) := s.graph_truth A addition multiplication predicates bindings.graphs numbers
        (fun i => .var (nm i+1)) (.var 0) (pushObject objects x) bindings.numbers
      have ht (x : D) := t.graph_truth A addition multiplication predicates bindings.graphs numbers
        (fun i => .var (nm i+1)) (.var 0) (pushObject objects x) bindings.numbers
      simp only [Formula.translate, Applicative.Formula.truth, hs, ht, Positive.Term.value,
        pushObject, Formula.truth]
      constructor
      · rintro ⟨x, hs, ht⟩; exact Subtype.ext (hs.symm.trans ht)
      · intro same; exact ⟨_, rfl, congrArg Subtype.val same⟩
  | member t i =>
      intro natural addition multiplication nm sm numbers sets objects predicates bindings
      have ht (x : D) := t.graph_truth A addition multiplication predicates bindings.graphs numbers
        (fun i => .var (nm i+1)) (.var 0) (pushObject objects x) bindings.numbers
      simp only [Formula.translate, Applicative.Formula.truth, ht, unary, Positive.Term.value,
        pushObject, Formula.truth]
      constructor
      · rintro ⟨x, rfl, h⟩; exact (bindings.member i _).mp h
      · intro h; exact ⟨_, rfl, (bindings.member i _).mpr h⟩
  | setEqual i j =>
      intro natural addition multiplication nm sm numbers sets objects predicates bindings
      simp only [Formula.translate, Applicative.Formula.truth, unary, Positive.Term.value,
        pushObject, Formula.truth, bindings.natural]
      rw [set_identity_iff_coextension]
      constructor
      · intro h x
        have hx := h x.val x.property
        exact (bindings.member i x).symm.trans ((Iff.intro hx.1 hx.2).trans (bindings.member j x))
      · intro h x hx
        have eq := (bindings.member i ⟨x,hx⟩).trans ((h ⟨x,hx⟩).trans (bindings.member j ⟨x,hx⟩).symm)
        exact ⟨eq.mp, eq.mpr⟩
  | falsum => intros; exact Iff.rfl
  | implies p q hp hq =>
      intro n a m nm sm ns ss os ps b
      exact imp_congr (hp _ _ _ _ _ _ _ _ _ b) (hq _ _ _ _ _ _ _ _ _ b)
  | conjunction p q hp hq =>
      intro n a m nm sm ns ss os ps b
      exact and_congr (hp _ _ _ _ _ _ _ _ _ b) (hq _ _ _ _ _ _ _ _ _ b)
  | disjunction p q hp hq =>
      intro n a m nm sm ns ss os ps b
      exact or_congr (hp _ _ _ _ _ _ _ _ _ b) (hq _ _ _ _ _ _ _ _ _ b)
  | existsNumber p ih =>
      intro n a m nm sm ns ss os ps b
      simp only [Formula.translate, Applicative.Formula.truth, unary, Positive.Term.value,
        pushObject, Formula.truth, b.natural]
      constructor
      · rintro ⟨x, hx, h⟩
        exact ⟨⟨x,hx⟩, (ih _ _ _ _ _ _ _ _ _ (b.numberBinder ⟨x,hx⟩)).mp h⟩
      · rintro ⟨x, h⟩
        exact ⟨x.val, x.property, (ih _ _ _ _ _ _ _ _ _ (b.numberBinder x)).mpr h⟩
  | forallNumber p ih =>
      intro n a m nm sm ns ss os ps b
      simp only [Formula.translate, Applicative.Formula.truth, unary, Positive.Term.value,
        pushObject, Formula.truth, b.natural]
      constructor
      · intro h x
        exact (ih _ _ _ _ _ _ _ _ _ (b.numberBinder x)).mp (h x.val x.property)
      · intro h x hx
        exact (ih _ _ _ _ _ _ _ _ _ (b.numberBinder ⟨x,hx⟩)).mpr (h ⟨x,hx⟩)
  | existsSet p ih =>
      intro n a m nm sm ns ss os ps b
      constructor
      · rintro ⟨P, h⟩
        exact ⟨representedSet M N P, (ih _ _ _ _ _ _ _ _ _ (b.setBinder P)).mp h⟩
      · rintro ⟨X, h⟩
        obtain ⟨P, rfl⟩ := representedSet_surjective M N X
        exact ⟨P, (ih _ _ _ _ _ _ _ _ _ (b.setBinder P)).mpr h⟩
  | forallSet p ih =>
      intro n a m nm sm ns ss os ps b
      constructor
      · intro h X
        obtain ⟨P, rfl⟩ := representedSet_surjective M N X
        exact (ih _ _ _ _ _ _ _ _ _ (b.setBinder P)).mp (h P)
      · intro h P
        exact (ih _ _ _ _ _ _ _ _ _ (b.setBinder P)).mpr (h (representedSet M N P))

noncomputable def arithmeticOperations {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) : Operations M N where
  domain := G.domain
  add := fun x y =>
    let existence := G.addition_total_unique x.val y.val x.property y.property
    ⟨Classical.choose existence,
      (G.addition_support _ _ _ (Classical.choose_spec existence).1).2.2⟩
  multiply := fun x y =>
    let existence := G.multiplication_total_unique x.val y.val x.property y.property
    ⟨Classical.choose existence,
      (G.multiplication_support _ _ _ (Classical.choose_spec existence).1).2.2⟩

theorem arithmetic_add_graph {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (x y : Number M N) (z : D) :
    member3 M G.addition x.val y.val z ↔ z = ((arithmeticOperations G).add x y).val := by
  have chosen := Classical.choose_spec (G.addition_total_unique x.val y.val x.property y.property)
  exact ⟨chosen.2 z, fun same => same.symm ▸ chosen.1⟩

theorem arithmetic_multiply_graph {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (x y : Number M N) (z : D) :
    member3 M G.multiplication x.val y.val z ↔ z = ((arithmeticOperations G).multiply x y).val := by
  have chosen := Classical.choose_spec (G.multiplication_total_unique x.val y.val x.property y.property)
  exact ⟨chosen.2 z, fun same => same.symm ▸ chosen.1⟩

noncomputable def setRepresentative {M : Interpretation D R} {N : R 0}
    (X : SetDomain M N) : R 0 := Classical.choose X.property

theorem setRepresentative_spec {M : Interpretation D R} {N : R 0}
    (X : SetDomain M N) : representedSet M N (setRepresentative X) = X := by
  apply Subtype.ext
  funext x
  exact propext ((Classical.choose_spec X.property x).symm)

/-- Reserved predicate slots are N at unary slot 0, and the two arithmetic
graphs at ternary slots 0 and 1. Source set parameters start at unary slot 1. -/
noncomputable def interpretationPredicates {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (full : HasFullComprehension M)
    (sets : Nat → SetDomain M N) : PredicateAssignment R :=
  let initial : PredicateAssignment R := fun arity i => match arity with
    | 0 => setRepresentative (sets i)
    | n+1 => Classical.choice (full.relations_nonempty (n+1))
  pushPredicate (pushPredicate (pushPredicate initial 2 G.multiplication) 2 G.addition) 0 N

theorem interpretation_bindings {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (full : HasFullComprehension M)
    (numbers : Nat → Number M N) (sets : Nat → SetDomain M N) :
    Bindings (arithmeticOperations G) 0 0 1 id Nat.succ numbers sets
      (fun i => (numbers i).val) (interpretationPredicates G full sets) where
  natural := by simp [interpretationPredicates, pushPredicate]
  numbers := fun _ => rfl
  sets := by intro i; simpa [interpretationPredicates, pushPredicate] using setRepresentative_spec (sets i)
  graphs := {
    add := by intro x y z; simpa [interpretationPredicates, pushPredicate, member3, ← triple_eq_arithmetic] using arithmetic_add_graph G x y z
    multiply := by intro x y z; simpa [interpretationPredicates, pushPredicate, member3, ← triple_eq_arithmetic] using arithmetic_multiply_graph G x y z }

theorem bound_interpretation_truth {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (full : HasFullComprehension M) (body : Formula)
    (numbers : Nat → Number M N) (sets : Nat → SetDomain M N) (x : Number M N) :
    (body.translate 0 0 1 id Nat.succ).truth M
      (pushObject (fun i => (numbers i).val) x.val) (interpretationPredicates G full sets) ↔
      body.truth (arithmeticOperations G) (pushObject numbers x) sets := by
  apply body.translation_preserves_truth
  have b := interpretation_bindings G full numbers sets
  exact {
    natural := b.natural
    numbers := by intro i; cases i with | zero => rfl | succ i => rfl
    sets := b.sets
    graphs := b.graphs }

/-- Every source formula inherits full comprehension from its proved target
translation, including formulas with alternating number/set quantifiers. -/
theorem source_formula_comprehension {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (full : HasFullComprehension M) (body : Formula)
    (numbers : Nat → Number M N) (sets : Nat → SetDomain M N) :
    ∃ X : SetDomain M N, ∀ x,
      X.val x ↔ body.truth (arithmeticOperations G) (pushObject numbers x) sets := by
  obtain ⟨P, law⟩ := full_comprehension_represents_unary_formula M full
    (body.translate 0 0 1 id Nat.succ) (fun i => (numbers i).val)
    (interpretationPredicates G full sets)
  exact ⟨representedSet M N P, fun x =>
    (law x.val).trans (bound_interpretation_truth G full body numbers sets x)⟩

/-- Induction for every actual source formula, with all parameters retained. -/
theorem source_formula_induction {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (full : HasFullComprehension M) (body : Formula)
    (numbers : Nat → Number M N) (sets : Nat → SetDomain M N)
    (base : body.truth (arithmeticOperations G)
      (pushObject numbers (arithmeticOperations G).zero) sets)
    (step : ∀ x, body.truth (arithmeticOperations G) (pushObject numbers x) sets →
      body.truth (arithmeticOperations G)
        (pushObject numbers ((arithmeticOperations G).successor x)) sets) :
    ∀ x, body.truth (arithmeticOperations G) (pushObject numbers x) sets := by
  have truth := bound_interpretation_truth G full body numbers sets
  have all := G.domain.formula_induction (body.translate 0 0 1 id Nat.succ)
    (fun i => (numbers i).val) (interpretationPredicates G full sets)
    ((truth _).mpr base)
    (fun x hx holds => (truth ((arithmeticOperations G).successor ⟨x,hx⟩)).mpr
      (step ⟨x,hx⟩ ((truth ⟨x,hx⟩).mp holds)))
  exact fun x => (truth x).mp (all x.val x.property)

theorem Formula.renameSets_truth {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (p : Formula) :
    ∀ map numbers sets, (p.renameSets map).truth A numbers sets ↔
      p.truth A numbers (fun i => sets (map i)) := by
  induction p with
  | equal _ _ => intros; exact Iff.rfl
  | member _ _ => intros; exact Iff.rfl
  | setEqual _ _ => intros; exact Iff.rfl
  | falsum => intros; exact Iff.rfl
  | implies _ _ hp hq => intros; exact imp_congr (hp _ _ _) (hq _ _ _)
  | conjunction _ _ hp hq => intros; exact and_congr (hp _ _ _) (hq _ _ _)
  | disjunction _ _ hp hq => intros; exact or_congr (hp _ _ _) (hq _ _ _)
  | existsNumber _ ih => intros; exact exists_congr (fun _ => ih _ _ _)
  | forallNumber _ ih => intros; exact forall_congr' (fun _ => ih _ _ _)
  | existsSet p ih =>
      intro map numbers sets
      apply exists_congr
      intro X
      refine (ih _ _ _).trans ?_
      have same : (fun i => pushObject sets X (Functional.bindMap map i)) =
          pushObject (fun i => sets (map i)) X := by funext i; cases i <;> rfl
      rw [same]
  | forallSet p ih =>
      intro map numbers sets
      apply forall_congr'
      intro X
      refine (ih _ _ _).trans ?_
      have same : (fun i => pushObject sets X (Functional.bindMap map i)) =
          pushObject (fun i => sets (map i)) X := by funext i; cases i <;> rfl
      rw [same]

theorem comprehension_truth {M : Interpretation D R} {N : R 0}
    (A : Operations M N) (body : Formula) (numbers : Nat → Number M N)
    (sets : Nat → SetDomain M N) :
    (comprehension body).truth A numbers sets ↔
      ∃ X : SetDomain M N, ∀ x, X.val x ↔ body.truth A (pushObject numbers x) sets := by
  simp only [comprehension, Formula.truth, iffF, Term.value, pushObject,
    Formula.renameSets_truth]
  constructor
  · rintro ⟨X, h⟩; exact ⟨X, fun x => ⟨(h x).1, (h x).2⟩⟩
  · rintro ⟨X, h⟩; exact ⟨X, fun x => ⟨(h x).mp, (h x).mpr⟩⟩

theorem addition_zero {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (y : Number M N) :
    (arithmeticOperations G).add (arithmeticOperations G).zero y = y := by
  apply Subtype.ext
  exact ((arithmetic_add_graph G (arithmeticOperations G).zero y y.val).mp
    ((G.addition_zero_recursion y.val y.val).mpr ⟨y.property, rfl⟩)).symm

theorem addition_successor {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (x y : Number M N) :
    (arithmeticOperations G).add ((arithmeticOperations G).successor x) y =
      (arithmeticOperations G).successor ((arithmeticOperations G).add x y) := by
  apply Subtype.ext
  exact ((arithmetic_add_graph G ((arithmeticOperations G).successor x) y _).mp
    ((G.addition_successor_recursion _ _ _).mpr
      ⟨_, (arithmetic_add_graph G x y _).mpr rfl, rfl⟩)).symm

theorem multiplication_zero {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (y : Number M N) :
    (arithmeticOperations G).multiply (arithmeticOperations G).zero y =
      (arithmeticOperations G).zero := by
  apply Subtype.ext
  exact ((arithmetic_multiply_graph G (arithmeticOperations G).zero y _).mp
    ((G.multiplication_zero_recursion y.val _).mpr ⟨y.property, rfl⟩)).symm

theorem multiplication_successor {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (x y : Number M N) :
    (arithmeticOperations G).multiply ((arithmeticOperations G).successor x) y =
      (arithmeticOperations G).add ((arithmeticOperations G).multiply x y) y := by
  apply Subtype.ext
  exact ((arithmetic_multiply_graph G ((arithmeticOperations G).successor x) y _).mp
    ((G.multiplication_successor_recursion _ _ _).mpr
      ⟨_, (arithmetic_multiply_graph G x y _).mpr rfl,
        (arithmetic_add_graph G ((arithmeticOperations G).multiply x y) y _).mpr rfl⟩)).symm

/-- Every actual Z2 axiom, including the full comprehension scheme and set
extensionality, holds in the interpreted structure. No arithmetic model is
assumed: the graph arguments are constructed from full TS in the next theorem. -/
theorem all_axioms_valid {M : Interpretation D R} {N : R 0}
    (G : FullArithmetic M N) (full : HasFullComprehension M) :
    ∀ p, Axiom p → Valid (arithmeticOperations G) p := by
  intro p hp numbers sets
  cases hp with
  | zeroNotSuccessor =>
      intro x same
      exact G.domain.zero_not_successor x.val (congrArg Subtype.val same)
  | successorInjective =>
      intro y x same
      exact Subtype.ext (G.domain.successor_injective x.val y.val (congrArg Subtype.val same))
  | additionZero => exact fun x => addition_zero G x
  | additionSuccessor => exact fun y x => addition_successor G x y
  | multiplicationZero => exact fun x => multiplication_zero G x
  | multiplicationSuccessor => exact fun y x => multiplication_successor G x y
  | induction =>
      intro X premise
      exact source_formula_induction G full (.member (.var 0) 0) numbers (pushObject sets X)
        premise.1 premise.2
  | extensionality =>
      intro Y X same
      exact (set_identity_iff_coextension M N X Y).mpr (fun x => ⟨(same x).1, (same x).2⟩)
  | comprehend body =>
      exact (comprehension_truth _ body numbers sets).mpr
        (source_formula_comprehension G full body numbers sets)

/-- Any full specification model contains an extensional Henkin model of all
of Z2, on its least inductive object domain with the constructed arithmetic graphs. -/
theorem full_ts_interprets_all_Z2_axioms (M : Interpretation D R)
    (full : FullTSConditions M) :
    ∃ (N : R 0) (G : FullArithmetic M N),
      ∀ p, Axiom p → Valid (arithmeticOperations G) p := by
  obtain ⟨N, ⟨G⟩⟩ := full_ts_has_arithmetic M full
  exact ⟨N, G, all_axioms_valid G full.full_comprehension⟩

theorem open_specification_interprets_all_Z2_axioms :
    ∃ N, ∃ G : FullArithmetic openSpecification N,
      ∀ p, Axiom p → Valid (arithmeticOperations G) p :=
  full_ts_interprets_all_Z2_axioms openSpecification openSpecification_satisfies_full_TS

end FregeanECA.Part2.SecondOrderArithmetic
