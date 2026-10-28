import FregeanECA.Pure
import FregeanECA.LogicBridge

/-! Ordinary single-sorted ECA in Foundation's actual first-order language.
There are no guards, predicates-as-objects, function sorts, or extra operations.
-/
namespace FregeanECA.Bare
open FFL FFL.FirstOrder

inductive Func : Nat → Type where
  | k : Func 0
  | s : Func 0
  | app : Func 2

inductive Rel : Nat → Type where
  | equal : Rel 2

def language : Language where
  Func := Func
  Rel := Rel
instance : language.Eq := ⟨Rel.equal⟩

abbrev Term (n : Nat) := Semiterm language Nat n
abbrev Formula (n : Nat) := Semiformula language Nat n
abbrev Map (n : Nat) := Nat → Term n

def bind (m : Map n) : Map (n+1)
  | 0 => .bvar 0
  | i+1 => Rew.bShift (m i)

def term (m : Map n) : Pure.Term → Term n
  | .var i => m i
  | .constantK => .func .k ![]
  | .constantS => .func .s ![]
  | .app f x => .func .app ![term m f, term m x]

def formula (m : Map n) : Pure.Formula → Formula n
  | .equal a b => .rel .equal ![term m a, term m b]
  | .falsum => .falsum
  | .implies a b => formula m a 🡒 formula m b
  | .conjunction a b => .and (formula m a) (formula m b)
  | .disjunction a b => .or (formula m a) (formula m b)
  | .existsObject body => .exs (formula (bind m) body)
  | .forallObject body => .all (formula (bind m) body)

noncomputable def sentence (φ : Pure.Formula) : Sentence language :=
  (formula (fun i => .fvar i) φ).univCl

universe u
variable (M : Type u) [Structure language M]

def extracted : Pure.Interpretation M where
  apply := fun a b => Structure.func (L := language) .app ![a,b]
  constantK := Structure.func (L := language) .k ![]
  constantS := Structure.func (L := language) .s ![]

theorem values_nil (b : Fin n → M) (free : Nat → M) :
    (fun i : Fin 0 => Semiterm.val b free ((![] : Fin 0 → Term n) i)) = ![] := by
  funext i; exact Fin.elim0 i

theorem values_two (a c : Term n) (b : Fin n → M) (free : Nat → M) :
    (fun i : Fin 2 => Semiterm.val b free (![a,c] i)) = ![a.val b free,c.val b free] := by
  funext i
  exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i

theorem term_value (t : Pure.Term) (m : Map n) (bound : Fin n → M)
    (free objects : Nat → M) (compatible : ∀ i, (m i).val bound free = objects i) :
    (term m t).val bound free = Pure.termValue (extracted M) objects t := by
  induction t with
  | var i => exact compatible i
  | constantK =>
      change Structure.func (L := language) .k _ = _
      rw [values_nil]
      rfl
  | constantS =>
      change Structure.func (L := language) .s _ = _
      rw [values_nil]
      rfl
  | app f x hf hx =>
      change Structure.func (L := language) .app _ = _
      rw [values_two, hf, hx]
      rfl

theorem bind_compatible {m : Map n} {bound : Fin n → M} {free objects : Nat → M}
    (h : ∀ i, (m i).val bound free = objects i) (x : M) :
    ∀ i, (bind m i).val (x :> bound) free = Positive.pushObject objects x i := by
  intro i
  cases i <;> simp [bind, Positive.pushObject, h]

theorem formula_truth [Structure.Eq language M] (φ : Pure.Formula) :
    ∀ {n} (m : Map n) (bound : Fin n → M) (free objects : Nat → M),
    (∀ i, (m i).val bound free = objects i) →
    (Semiformula.Eval bound free (formula m φ) ↔ φ.truth (extracted M) objects) := by
  induction φ with
  | equal a b =>
      intro n m bound free objects compatible
      change Structure.rel (L := language) .equal _ ↔ _
      rw [values_two, term_value M a _ _ _ _ compatible, term_value M b _ _ _ _ compatible]
      exact Structure.eq_lang (L := language) (M := M)
  | falsum => intros; exact Iff.rfl
  | implies a b ha hb =>
      intro n m bound free objects compatible
      simp only [formula, LogicalConnective.HomClass.map_imply, Pure.Formula.truth]
      exact imp_congr (ha _ _ _ _ compatible) (hb _ _ _ _ compatible)
  | conjunction a b ha hb =>
      intro n m bound free objects compatible
      exact and_congr (ha _ _ _ _ compatible) (hb _ _ _ _ compatible)
  | disjunction a b ha hb =>
      intro n m bound free objects compatible
      exact or_congr (ha _ _ _ _ compatible) (hb _ _ _ _ compatible)
  | existsObject body ih =>
      intro n m bound free objects compatible
      exact exists_congr (fun x => ih _ _ _ _ (bind_compatible M compatible x))
  | forallObject body ih =>
      intro n m bound free objects compatible
      exact forall_congr' (fun x => ih _ _ _ _ (bind_compatible M compatible x))

theorem sentence_truth [Nonempty M] [Structure.Eq language M] (φ : Pure.Formula) :
    (sentence φ).Realize M ↔ ∀ objects, φ.truth (extracted M) objects := by
  rw [sentence, Semiformula.eval_univCl]
  exact forall_congr' (fun objects => formula_truth M φ _ ![] objects objects (fun _ => rfl))

def kLaw : Pure.Formula := .forallObject (.forallObject
  (.equal (.app (.app .constantK (.var 0)) (.var 1)) (.var 0)))
def sLaw : Pure.Formula := .forallObject (.forallObject (.forallObject
  (.equal (.app (.app (.app .constantS (.var 0)) (.var 1)) (.var 2))
    (.app (.app (.var 0) (.var 2)) (.app (.var 1) (.var 2))))))
def extensionality : Pure.Formula := .forallObject (.forallObject
  (.implies (.forallObject (.equal (.app (.var 1) (.var 0)) (.app (.var 2) (.var 0))))
    (.equal (.var 0) (.var 1))))
def nontriviality : Pure.Formula := .existsObject (.existsObject
  (.implies (.equal (.var 0) (.var 1)) .falsum))

inductive Axiom : Pure.Formula → Prop where
  | k : Axiom kLaw
  | s : Axiom sLaw
  | ext : Axiom extensionality
  | nontrivial : Axiom nontriviality

noncomputable def theory : Theory language :=
  Theory.eqAxiom language ∪ {σ | ∃ φ, Axiom φ ∧ sentence φ = σ}

instance : Theory.eqAxiom language ⪯ theory :=
  Entailment.Axiomatized.le_of_subset (fun _ h => Or.inl h)

omit [Structure language M] in
theorem axioms_truth_iff (P : Pure.Interpretation M) :
    (∀ φ, Axiom φ → ∀ o, φ.truth P o) ↔ Pure.ECAConditions P := by
  let o : Nat → M := fun _ => P.constantK
  constructor
  · intro h
    exact ⟨fun x y => h _ .k o y x, fun x y z => h _ .s o z y x,
      fun a b => h _ .ext o b a,
      (by obtain ⟨b,a,different⟩ := h _ .nontrivial o; exact ⟨a,b,different⟩)⟩
  · intro h φ hp objects
    cases hp with
    | k => exact fun y x => h.constant x y
    | s => exact fun z y x => h.distribute x y z
    | ext => exact fun b a => h.extensional a b
    | nontrivial =>
        obtain ⟨a,b,different⟩ := h.nontrivial
        exact ⟨b,a,different⟩

theorem models_theory_iff [Nonempty M] [Structure.Eq language M] :
    M↓[language] ⊧* theory ↔ Pure.ECAConditions (extracted M) := by
  rw [← axioms_truth_iff M (extracted M)]
  constructor
  · intro h φ hφ
    exact (sentence_truth M φ).mp (h.models _ (Or.inr ⟨φ,hφ,rfl⟩))
  · intro h
    refine ⟨?_⟩
    intro σ hσ
    rcases hσ with he | ⟨φ,hφ,rfl⟩
    · exact (inferInstance : M↓[language] ⊧* Theory.eqAxiom language).models _ he
    · exact (sentence_truth M φ).mpr (h φ hφ)

@[instance_reducible] def structureFor {D : Type u} (P : Pure.Interpretation D) : Structure language D where
  func := fun {_} f xs => match f with
    | .k => P.constantK
    | .s => P.constantS
    | .app => P.apply (xs 0) (xs 1)
  rel := fun {_} r xs => match r with
    | .equal => xs 0 = xs 1

theorem structureFor_eq {D : Type u} (P : Pure.Interpretation D) :
    letI := structureFor P
    Structure.Eq language D := by
  letI := structureFor P
  exact ⟨fun _ _ => Iff.rfl⟩

def model {D : Type} [Nonempty D] (P : Pure.Interpretation D) : SmallStruc language :=
  @Structure.toStruc language D inferInstance (structureFor P)

theorem model_valid {D : Type} [Nonempty D] (P : Pure.Interpretation D)
    (h : Pure.ECAConditions P) : model P ⊧* theory := by
  letI := structureFor P
  haveI := structureFor_eq P
  exact (models_theory_iff D).mpr h

theorem model_truth {D : Type} [Nonempty D] (P : Pure.Interpretation D) (φ : Pure.Formula) :
    model P ⊧ sentence φ ↔ ∀ objects, φ.truth P objects := by
  letI := structureFor P
  haveI := structureFor_eq P
  exact sentence_truth D φ

end FregeanECA.Bare
