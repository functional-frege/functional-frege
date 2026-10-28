import FregeanECA.V3.Certificate

/-!
Truth values, concepts and Frege's strokes in the applicative fragment.

Church truth values: `T := K` and `F := K·I`; A5 is `T ≠ F`.  A *concept* is
an object `c` with `c·x ∈ {T, F}` for every `x`, and `x ∈ c` means `c·x = T`.

Every statement below is a pure applicative sentence (`Pure.Formula`).  Each
is proved valid in every structure satisfying `Pure.ECAConditions`, lifted to
derivability in the bare ECA calculus `Bare.theory` by completeness, and
transferred to NECA + RC and to FF by
`V3.Certificate.pure_conservativity_three_way`.

Positive results (`concepts_provable`):
* `lawV`: concepts with the same members are equal (Law V for concepts);
* `universalIdentity`, `existentialIdentity`: quantification over a concept
  is an identity, `∀x (c·x = T) ↔ c = K·T`, and for concepts
  `∃x (c·x = T) ↔ c ≠ K·F`;
* `connectives`: negation, conjunction and disjunction are objects with the
  expected truth tables on `{T, F}`;
* `closure`: concepts are closed under complement, intersection and union.

Collapse (`collapse_provable`): every object that is bivalent on the whole
domain is constant, `K·T` or `K·F`; so the concepts above are exactly these
two objects, and Frege's total concepts cannot be objects.

Negative results (`strokes_provable`): no object is Frege's horizontal
(`T ↦ T`, every other object `↦ F`), because every object has a fixed point
while `x ↦ h·x·F·T` has none; consequently there is no negation stroke, no
conditional stroke, no equality test, no bivalent quantifier object and no
whole-domain case operator.
-/

namespace FregeanECA.V4.TruthValues

open FFL FFL.FirstOrder Guarded

universe u

/-! ### Syntax -/

/-- `T := K`. -/
def tT : Pure.Term := .constantK
/-- `I := S·K·K`. -/
def tI : Pure.Term := .app (.app .constantS .constantK) .constantK
/-- `F := K·I`. -/
def tF : Pure.Term := .app .constantK tI

def fiff (a b : Pure.Formula) : Pure.Formula := .conjunction (.implies a b) (.implies b a)
def fnot (a : Pure.Formula) : Pure.Formula := .implies a .falsum

/-- Inside a quantifier `var 0` is the bound variable, so the object at index
`i` outside the quantifier is `var (i+1)` inside.  `concept i` says that this
object takes only the values `T` and `F`. -/
def concept (i : Nat) : Pure.Formula :=
  .forallObject (.disjunction (.equal (.app (.var (i+1)) (.var 0)) tT)
    (.equal (.app (.var (i+1)) (.var 0)) tF))

/-- Inside `∀x`: `x` belongs to the object at index `i` outside the quantifier. -/
def member (i : Nat) : Pure.Formula := .equal (.app (.var (i+1)) (.var 0)) tT

/-- The objects at indices `i` and `j` have the same members. -/
def sameMembers (i j : Nat) : Pure.Formula := .forallObject (fiff (member i) (member j))

/-- Law V for concepts: `∀c ∀d (concept c → concept d → (c = d ↔ ∀x (x ∈ c ↔ x ∈ d)))`. -/
def lawV : Pure.Formula :=
  .forallObject (.forallObject (.implies (concept 1) (.implies (concept 0)
    (fiff (.equal (.var 1) (.var 0)) (sameMembers 1 0)))))

/-- `∀c ((∀x c·x = T) ↔ c = K·T)`. -/
def universalIdentity : Pure.Formula :=
  .forallObject (fiff (.forallObject (member 0)) (.equal (.var 0) (.app .constantK tT)))

/-- `∀c (concept c → ((∃x c·x = T) ↔ c ≠ K·F))`. -/
def existentialIdentity : Pure.Formula :=
  .forallObject (.implies (concept 0)
    (fiff (.existsObject (member 0)) (fnot (.equal (.var 0) (.app .constantK tF)))))

/-- `∃n (n·T = F ∧ n·F = T)`. -/
def negationObject : Pure.Formula :=
  .existsObject (.conjunction (.equal (.app (.var 0) tT) tF) (.equal (.app (.var 0) tF) tT))

/-- `∃a` with the truth table of conjunction on `{T, F}`. -/
def conjunctionObject : Pure.Formula :=
  .existsObject (.conjunction (.equal (.app (.app (.var 0) tT) tT) tT)
    (.conjunction (.equal (.app (.app (.var 0) tT) tF) tF)
      (.conjunction (.equal (.app (.app (.var 0) tF) tT) tF)
        (.equal (.app (.app (.var 0) tF) tF) tF))))

/-- `∃o` with the truth table of disjunction on `{T, F}`. -/
def disjunctionObject : Pure.Formula :=
  .existsObject (.conjunction (.equal (.app (.app (.var 0) tT) tT) tT)
    (.conjunction (.equal (.app (.app (.var 0) tT) tF) tT)
      (.conjunction (.equal (.app (.app (.var 0) tF) tT) tT)
        (.equal (.app (.app (.var 0) tF) tF) tF))))

/-- Negation, conjunction and disjunction are objects. -/
def connectives : Pure.Formula :=
  .conjunction negationObject (.conjunction conjunctionObject disjunctionObject)

/-- Inside `∀c ∀d` (`c = var 1`, `d = var 0`): there is a concept `e` whose
members are described by `body`; `body` is read inside `∀x`, where `e = var 1`,
`d = var 2` and `c = var 3`. -/
def closureOf (body : Pure.Formula) : Pure.Formula :=
  .existsObject (.conjunction (concept 0) (.forallObject (fiff (member 0) body)))

/-- Concepts are closed under complement, intersection and union. -/
def closure : Pure.Formula :=
  .forallObject (.forallObject (.implies (concept 1) (.implies (concept 0)
    (.conjunction (closureOf (fnot (member 2)))
      (.conjunction (closureOf (.conjunction (member 2) (member 1)))
        (closureOf (.disjunction (member 2) (member 1))))))))

/-- Collapse of total concepts: `∀c (concept c → (∀x c·x = T) ∨ (∀x c·x = F))`. -/
def collapse : Pure.Formula :=
  .forallObject (.implies (concept 0)
    (.disjunction (.forallObject (member 0))
      (.forallObject (.equal (.app (.var 1) (.var 0)) tF))))

/-- `h` (`var 1`) is Frege's horizontal: `x = T → h·x = T` and `x ≠ T → h·x = F`. -/
def horizontalSpec : Pure.Formula :=
  .forallObject (.conjunction
    (.implies (.equal (.var 0) tT) (.equal (.app (.var 1) (.var 0)) tT))
    (.implies (fnot (.equal (.var 0) tT)) (.equal (.app (.var 1) (.var 0)) tF)))

/-- No object is the horizontal. -/
def noHorizontal : Pure.Formula := fnot (.existsObject horizontalSpec)

/-- Frege's negation stroke: `x = T → n·x = F` and `x ≠ T → n·x = T`. -/
def negationStrokeSpec : Pure.Formula :=
  .forallObject (.conjunction
    (.implies (.equal (.var 0) tT) (.equal (.app (.var 1) (.var 0)) tF))
    (.implies (fnot (.equal (.var 0) tT)) (.equal (.app (.var 1) (.var 0)) tT)))

def noNegationStroke : Pure.Formula := fnot (.existsObject negationStrokeSpec)

/-- Frege's conditional stroke (`c = var 2`, `x = var 1`, `y = var 0`):
`c·x·y = F` if `x = T` and `y ≠ T`, and `c·x·y = T` otherwise. -/
def conditionalStrokeSpec : Pure.Formula :=
  .forallObject (.forallObject (.conjunction
    (.implies (.conjunction (.equal (.var 1) tT) (fnot (.equal (.var 0) tT)))
      (.equal (.app (.app (.var 2) (.var 1)) (.var 0)) tF))
    (.implies (fnot (.conjunction (.equal (.var 1) tT) (fnot (.equal (.var 0) tT))))
      (.equal (.app (.app (.var 2) (.var 1)) (.var 0)) tT))))

def noConditionalStroke : Pure.Formula := fnot (.existsObject conditionalStrokeSpec)

/-- An equality test (`e = var 2`, `x = var 1`, `y = var 0`): `e·x·y = T` if
`x = y`, `e·x·y = F` otherwise. -/
def equalityTestSpec : Pure.Formula :=
  .forallObject (.forallObject (.conjunction
    (.implies (.equal (.var 1) (.var 0)) (.equal (.app (.app (.var 2) (.var 1)) (.var 0)) tT))
    (.implies (fnot (.equal (.var 1) (.var 0)))
      (.equal (.app (.app (.var 2) (.var 1)) (.var 0)) tF))))

def noEqualityTest : Pure.Formula := fnot (.existsObject equalityTestSpec)

/-- A bivalent quantifier object (`q = var 1`, `f = var 0`): `q·f = T` if
`∀y f·y = T`, and `q·f = F` otherwise. -/
def quantifierObjectSpec : Pure.Formula :=
  .forallObject (.conjunction
    (.implies (.forallObject (member 0)) (.equal (.app (.var 1) (.var 0)) tT))
    (.implies (fnot (.forallObject (member 0))) (.equal (.app (.var 1) (.var 0)) tF)))

def noQuantifierObject : Pure.Formula := fnot (.existsObject quantifierObjectSpec)

/-- A whole-domain case operator (`d = var 4`, `x = var 3`, `y = var 2`,
`u = var 1`, `v = var 0`): `d·x·y·u·v = u` if `x = y`, and `= v` otherwise. -/
def caseOperatorSpec : Pure.Formula :=
  .forallObject (.forallObject (.forallObject (.forallObject (.conjunction
    (.implies (.equal (.var 3) (.var 2))
      (.equal (.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.var 1)))
    (.implies (fnot (.equal (.var 3) (.var 2)))
      (.equal (.app (.app (.app (.app (.var 4) (.var 3)) (.var 2)) (.var 1)) (.var 0)) (.var 0)))))))

def noCaseOperator : Pure.Formula := fnot (.existsObject caseOperatorSpec)

/-! ### Semantics in an arbitrary nontrivial extensional combinatory algebra -/

/-- The value of `I = S·K·K`. -/
def Iv {D : Type u} (P : Pure.Interpretation D) : D :=
  P.apply (P.apply P.constantS P.constantK) P.constantK

/-- The value of `F = K·I`. -/
def Fv {D : Type u} (P : Pure.Interpretation D) : D := P.apply P.constantK (Iv P)

/-- Polynomials in one variable with coefficients in `D`. -/
inductive Poly (D : Type u) where
  | var : Poly D
  | const : D → Poly D
  | app : Poly D → Poly D → Poly D

namespace Poly

variable {D : Type u} (P : Pure.Interpretation D)

def eval : Poly D → D → D
  | .var, v => v
  | .const a, _ => a
  | .app p q, v => P.apply (eval p v) (eval q v)

/-- Bracket abstraction of the variable. -/
def abs : Poly D → D
  | .var => Iv P
  | .const a => P.apply P.constantK a
  | .app p q => P.apply (P.apply P.constantS (abs p)) (abs q)

end Poly

section Semantics

variable {D : Type u} (P : Pure.Interpretation D)

theorem I_apply (h : Pure.ECAConditions P) (x : D) : P.apply (Iv P) x = x := by
  show P.apply (P.apply (P.apply P.constantS P.constantK) P.constantK) x = x
  rw [h.distribute, h.constant]

theorem F_apply (h : Pure.ECAConditions P) (a b : D) : P.apply (P.apply (Fv P) a) b = b := by
  show P.apply (P.apply (P.apply P.constantK (Iv P)) a) b = b
  rw [h.constant, I_apply P h]

theorem T_ne_F (h : Pure.ECAConditions P) : P.constantK ≠ Fv P := by
  intro e
  obtain ⟨a, b, ne⟩ := h.nontrivial
  apply ne
  calc a = P.apply (P.apply P.constantK a) b := (h.constant a b).symm
    _ = P.apply (P.apply (Fv P) a) b := by rw [e]
    _ = b := F_apply P h a b

theorem Poly.abs_apply (h : Pure.ECAConditions P) (p : Poly D) (v : D) : P.apply (Poly.abs P p) v = Poly.eval P p v := by
  induction p with
  | var => exact I_apply P h v
  | const a => exact h.constant a v
  | app p q ihp ihq =>
      show P.apply (P.apply (P.apply P.constantS (Poly.abs P p)) (Poly.abs P q)) v =
        P.apply (Poly.eval P p v) (Poly.eval P q v)
      rw [h.distribute, ihp, ihq]

/-- Every object has a fixed point: `m := λx. g·(x·x)` and `w := m·m`. -/
theorem fixed_point (h : Pure.ECAConditions P) (g : D) : ∃ w, P.apply g w = w := by
  have hsii : ∀ x, P.apply (P.apply (P.apply P.constantS (Iv P)) (Iv P)) x = P.apply x x := by
    intro x
    rw [h.distribute, I_apply P h]
  have hm : ∀ x, P.apply (P.apply (P.apply P.constantS (P.apply P.constantK g))
      (P.apply (P.apply P.constantS (Iv P)) (Iv P))) x = P.apply g (P.apply x x) := by
    intro x
    rw [h.distribute, h.constant, hsii]
  exact ⟨_, (hm (P.apply (P.apply P.constantS (P.apply P.constantK g))
      (P.apply (P.apply P.constantS (Iv P)) (Iv P)))).symm⟩

/-! #### Positive results -/

theorem lawV_sem (h : Pure.ECAConditions P) (c d : D)
    (hc : ∀ x, P.apply c x = P.constantK ∨ P.apply c x = Fv P)
    (hd : ∀ x, P.apply d x = P.constantK ∨ P.apply d x = Fv P) :
    (c = d → ∀ x, (P.apply c x = P.constantK → P.apply d x = P.constantK) ∧
        (P.apply d x = P.constantK → P.apply c x = P.constantK)) ∧
      ((∀ x, (P.apply c x = P.constantK → P.apply d x = P.constantK) ∧
        (P.apply d x = P.constantK → P.apply c x = P.constantK)) → c = d) := by
  refine ⟨fun e x => ?_, fun same => ?_⟩
  · subst e
    exact ⟨id, id⟩
  · apply h.extensional
    intro x
    rcases hc x with hcx | hcx
    · rw [hcx, (same x).1 hcx]
    · rcases hd x with hdx | hdx
      · have := (same x).2 hdx
        rw [hcx] at this
        exact (T_ne_F P h this.symm).elim
      · rw [hcx, hdx]

theorem universal_sem (h : Pure.ECAConditions P) (c : D) :
    ((∀ x, P.apply c x = P.constantK) → c = P.apply P.constantK P.constantK) ∧
      (c = P.apply P.constantK P.constantK → ∀ x, P.apply c x = P.constantK) := by
  constructor
  · intro all
    apply h.extensional
    intro x
    rw [all x, h.constant]
  · intro e x
    rw [e, h.constant]

theorem existential_sem (h : Pure.ECAConditions P) (c : D)
    (hc : ∀ x, P.apply c x = P.constantK ∨ P.apply c x = Fv P) :
    ((∃ x, P.apply c x = P.constantK) → (c = P.apply P.constantK (Fv P) → False)) ∧
      ((c = P.apply P.constantK (Fv P) → False) → ∃ x, P.apply c x = P.constantK) := by
  constructor
  · rintro ⟨x, hx⟩ e
    rw [e, h.constant] at hx
    exact T_ne_F P h hx.symm
  · intro ne
    apply Classical.byContradiction
    intro none
    apply ne
    apply h.extensional
    intro x
    rw [h.constant]
    rcases hc x with hx | hx
    · exact (none ⟨x, hx⟩).elim
    · exact hx

theorem negation_sem (h : Pure.ECAConditions P) :
    ∃ n : D, P.apply n P.constantK = Fv P ∧ P.apply n (Fv P) = P.constantK := by
  refine ⟨Poly.abs P (.app (.app .var (.const (Fv P))) (.const P.constantK)), ?_, ?_⟩
  · rw [Poly.abs_apply P h]
    show P.apply (P.apply P.constantK (Fv P)) P.constantK = Fv P
    exact h.constant _ _
  · rw [Poly.abs_apply P h]
    show P.apply (P.apply (Fv P) (Fv P)) P.constantK = P.constantK
    exact F_apply P h _ _

/-- `λp. S·(S·(K·p)·I)·(K·F)`, so that `a·p·q = p·q·F`. -/
def conjunctionPoly : Poly D :=
  .app (.app (.const P.constantS) (.app (.app (.const P.constantS) (.app (.const P.constantK) .var))
    (.const (Iv P)))) (.app (.const P.constantK) (.const (Fv P)))

theorem conjunctionPoly_apply (h : Pure.ECAConditions P) (p q : D) :
    P.apply (P.apply (Poly.abs P (conjunctionPoly P)) p) q = P.apply (P.apply p q) (Fv P) := by
  rw [Poly.abs_apply P h]
  show P.apply (P.apply (P.apply P.constantS (P.apply (P.apply P.constantS (P.apply P.constantK p))
    (Iv P))) (P.apply P.constantK (Fv P))) q = P.apply (P.apply p q) (Fv P)
  simp only [h.distribute, h.constant, I_apply P h]

theorem conjunction_sem (h : Pure.ECAConditions P) :
    ∃ a : D, P.apply (P.apply a P.constantK) P.constantK = P.constantK ∧
      P.apply (P.apply a P.constantK) (Fv P) = Fv P ∧
      P.apply (P.apply a (Fv P)) P.constantK = Fv P ∧
      P.apply (P.apply a (Fv P)) (Fv P) = Fv P := by
  refine ⟨Poly.abs P (conjunctionPoly P), ?_, ?_, ?_, ?_⟩ <;>
    rw [conjunctionPoly_apply P h] <;> simp only [h.constant, F_apply P h]

/-- `λp. S·(S·(K·p)·(K·K))·I`, so that `o·p·q = p·K·q`. -/
def disjunctionPoly : Poly D :=
  .app (.app (.const P.constantS) (.app (.app (.const P.constantS) (.app (.const P.constantK) .var))
    (.app (.const P.constantK) (.const P.constantK)))) (.const (Iv P))

theorem disjunctionPoly_apply (h : Pure.ECAConditions P) (p q : D) :
    P.apply (P.apply (Poly.abs P (disjunctionPoly P)) p) q = P.apply (P.apply p P.constantK) q := by
  rw [Poly.abs_apply P h]
  show P.apply (P.apply (P.apply P.constantS (P.apply (P.apply P.constantS (P.apply P.constantK p))
    (P.apply P.constantK P.constantK))) (Iv P)) q = P.apply (P.apply p P.constantK) q
  simp only [h.distribute, h.constant, I_apply P h]

theorem disjunction_sem (h : Pure.ECAConditions P) :
    ∃ o : D, P.apply (P.apply o P.constantK) P.constantK = P.constantK ∧
      P.apply (P.apply o P.constantK) (Fv P) = P.constantK ∧
      P.apply (P.apply o (Fv P)) P.constantK = P.constantK ∧
      P.apply (P.apply o (Fv P)) (Fv P) = Fv P := by
  refine ⟨Poly.abs P (disjunctionPoly P), ?_, ?_, ?_, ?_⟩ <;>
    rw [disjunctionPoly_apply P h] <;> simp only [h.constant, F_apply P h]

theorem complement_sem (h : Pure.ECAConditions P) (c : D)
    (hc : ∀ x, P.apply c x = P.constantK ∨ P.apply c x = Fv P) :
    ∃ e : D, (∀ x, P.apply e x = P.constantK ∨ P.apply e x = Fv P) ∧
      ∀ x, (P.apply e x = P.constantK → (P.apply c x = P.constantK → False)) ∧
        ((P.apply c x = P.constantK → False) → P.apply e x = P.constantK) := by
  obtain ⟨e, he⟩ : ∃ e : D, ∀ x,
      P.apply e x = P.apply (P.apply (P.apply c x) (Fv P)) P.constantK :=
    ⟨Poly.abs P (.app (.app (.app (.const c) .var) (.const (Fv P))) (.const P.constantK)),
      fun x => Poly.abs_apply P h _ x⟩
  refine ⟨e, fun x => ?_, fun x => ⟨fun hex hcx => ?_, fun hcx => ?_⟩⟩
  · rcases hc x with hcx | hcx
    · right
      rw [he, hcx, h.constant]
    · left
      rw [he, hcx, F_apply P h]
  · rw [he, hcx, h.constant] at hex
    exact T_ne_F P h hex.symm
  · rcases hc x with hcx' | hcx'
    · exact (hcx hcx').elim
    · rw [he, hcx', F_apply P h]

theorem intersection_sem (h : Pure.ECAConditions P) (c d : D)
    (hc : ∀ x, P.apply c x = P.constantK ∨ P.apply c x = Fv P)
    (hd : ∀ x, P.apply d x = P.constantK ∨ P.apply d x = Fv P) :
    ∃ e : D, (∀ x, P.apply e x = P.constantK ∨ P.apply e x = Fv P) ∧
      ∀ x, (P.apply e x = P.constantK → P.apply c x = P.constantK ∧ P.apply d x = P.constantK) ∧
        (P.apply c x = P.constantK ∧ P.apply d x = P.constantK → P.apply e x = P.constantK) := by
  obtain ⟨e, he⟩ : ∃ e : D, ∀ x,
      P.apply e x = P.apply (P.apply (P.apply c x) (P.apply d x)) (Fv P) :=
    ⟨Poly.abs P (.app (.app (.app (.const c) .var) (.app (.const d) .var)) (.const (Fv P))),
      fun x => Poly.abs_apply P h _ x⟩
  refine ⟨e, fun x => ?_, fun x => ⟨fun hex => ?_, fun both => ?_⟩⟩
  · rcases hc x with hcx | hcx <;> rcases hd x with hdx | hdx
    · left
      rw [he, hcx, hdx, h.constant]
    · right
      rw [he, hcx, hdx, h.constant]
    · right
      rw [he, hcx, hdx, F_apply P h]
    · right
      rw [he, hcx, hdx, F_apply P h]
  · rcases hc x with hcx | hcx <;> rcases hd x with hdx | hdx
    · exact ⟨hcx, hdx⟩
    · rw [he, hcx, hdx, h.constant] at hex
      exact (T_ne_F P h hex.symm).elim
    · rw [he, hcx, hdx, F_apply P h] at hex
      exact (T_ne_F P h hex.symm).elim
    · rw [he, hcx, hdx, F_apply P h] at hex
      exact (T_ne_F P h hex.symm).elim
  · rw [he, both.1, both.2, h.constant]

theorem union_sem (h : Pure.ECAConditions P) (c d : D)
    (hc : ∀ x, P.apply c x = P.constantK ∨ P.apply c x = Fv P)
    (hd : ∀ x, P.apply d x = P.constantK ∨ P.apply d x = Fv P) :
    ∃ e : D, (∀ x, P.apply e x = P.constantK ∨ P.apply e x = Fv P) ∧
      ∀ x, (P.apply e x = P.constantK → P.apply c x = P.constantK ∨ P.apply d x = P.constantK) ∧
        (P.apply c x = P.constantK ∨ P.apply d x = P.constantK → P.apply e x = P.constantK) := by
  obtain ⟨e, he⟩ : ∃ e : D, ∀ x,
      P.apply e x = P.apply (P.apply (P.apply c x) P.constantK) (P.apply d x) :=
    ⟨Poly.abs P (.app (.app (.app (.const c) .var) (.const P.constantK)) (.app (.const d) .var)),
      fun x => Poly.abs_apply P h _ x⟩
  refine ⟨e, fun x => ?_, fun x => ⟨fun hex => ?_, fun either => ?_⟩⟩
  · rcases hc x with hcx | hcx <;> rcases hd x with hdx | hdx
    · left
      rw [he, hcx, hdx, h.constant]
    · left
      rw [he, hcx, hdx, h.constant]
    · left
      rw [he, hcx, hdx, F_apply P h]
    · right
      rw [he, hcx, hdx, F_apply P h]
  · rcases hc x with hcx | hcx
    · exact Or.inl hcx
    · rcases hd x with hdx | hdx
      · exact Or.inr hdx
      · rw [he, hcx, hdx, F_apply P h] at hex
        exact (T_ne_F P h hex.symm).elim
  · rcases either with hcx | hdx
    · rw [he, hcx, h.constant]
    · rcases hc x with hcx | hcx
      · rw [he, hcx, h.constant]
      · rw [he, hcx, hdx, F_apply P h]

/-! #### Collapse of total concepts -/

/-- A total bivalent object is constant: if `c·a = T` and `c·b = F`, the fixed
point `w` of `z ↦ c·z·b·a` satisfies `w = b` when `c·w = T` and `w = a` when
`c·w = F`, and either case gives `T = F`. -/
theorem collapse_sem (h : Pure.ECAConditions P) (c : D)
    (hc : ∀ x, P.apply c x = P.constantK ∨ P.apply c x = Fv P) :
    (∀ x, P.apply c x = P.constantK) ∨ (∀ x, P.apply c x = Fv P) := by
  classical
  by_cases allT : ∀ x, P.apply c x = P.constantK
  · exact Or.inl allT
  · right
    obtain ⟨b, hb⟩ := Classical.not_forall.mp allT
    have hbF : P.apply c b = Fv P := (hc b).resolve_left hb
    intro x
    rcases hc x with hxT | hxF
    · exfalso
      obtain ⟨g, hg⟩ : ∃ g : D, ∀ z, P.apply g z = P.apply (P.apply (P.apply c z) b) x :=
        ⟨Poly.abs P (.app (.app (.app (.const c) .var) (.const b)) (.const x)),
          fun z => Poly.abs_apply P h _ z⟩
      obtain ⟨w, hw⟩ := fixed_point P h g
      rcases hc w with hwT | hwF
      · have wb : w = b := by
          calc w = P.apply g w := hw.symm
            _ = P.apply (P.apply (P.apply c w) b) x := hg w
            _ = b := by rw [hwT, h.constant]
        rw [wb, hbF] at hwT
        exact T_ne_F P h hwT.symm
      · have wx : w = x := by
          calc w = P.apply g w := hw.symm
            _ = P.apply (P.apply (P.apply c w) b) x := hg w
            _ = x := by rw [hwF, F_apply P h]
        rw [wx, hxT] at hwF
        exact T_ne_F P h hwF
    · exact hxF

/-! #### Negative results -/

/-- No object is the horizontal: `x ↦ h·x·F·T` would have no fixed point. -/
theorem no_horizontal_sem (h : Pure.ECAConditions P) (hh : D)
    (spec : ∀ x, (x = P.constantK → P.apply hh x = P.constantK) ∧
      ((x = P.constantK → False) → P.apply hh x = Fv P)) : False := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : D, ∀ x,
      P.apply g x = P.apply (P.apply (P.apply hh x) (Fv P)) P.constantK :=
    ⟨Poly.abs P (.app (.app (.app (.const hh) .var) (.const (Fv P))) (.const P.constantK)),
      fun x => Poly.abs_apply P h _ x⟩
  obtain ⟨w, hw⟩ := fixed_point P h g
  by_cases wT : w = P.constantK
  · have h1 := (spec w).1 wT
    have wF : w = Fv P := by
      calc w = P.apply g w := hw.symm
        _ = P.apply (P.apply (P.apply hh w) (Fv P)) P.constantK := hg w
        _ = Fv P := by rw [h1, h.constant]
    exact T_ne_F P h (wT.symm.trans wF)
  · have h2 := (spec w).2 wT
    apply wT
    calc w = P.apply g w := hw.symm
      _ = P.apply (P.apply (P.apply hh w) (Fv P)) P.constantK := hg w
      _ = P.constantK := by rw [h2, F_apply P h]

/-- The negation stroke `n` would give the horizontal `x ↦ n·(n·x)`. -/
theorem no_negation_stroke_sem (h : Pure.ECAConditions P) (n : D)
    (spec : ∀ x, (x = P.constantK → P.apply n x = Fv P) ∧
      ((x = P.constantK → False) → P.apply n x = P.constantK)) : False := by
  obtain ⟨hh, hhh⟩ : ∃ hh : D, ∀ x, P.apply hh x = P.apply n (P.apply n x) :=
    ⟨Poly.abs P (.app (.const n) (.app (.const n) .var)), fun x => Poly.abs_apply P h _ x⟩
  apply no_horizontal_sem P h hh
  intro x
  refine ⟨fun xT => ?_, fun xF => ?_⟩
  · rw [hhh, (spec x).1 xT]
    exact (spec (Fv P)).2 (fun e => T_ne_F P h e.symm)
  · rw [hhh, (spec x).2 xF]
    exact (spec P.constantK).1 rfl

/-- The conditional stroke `c` would give the negation stroke `x ↦ c·x·F`. -/
theorem no_conditional_stroke_sem (h : Pure.ECAConditions P) (c : D)
    (spec : ∀ x y, ((x = P.constantK ∧ (y = P.constantK → False)) →
        P.apply (P.apply c x) y = Fv P) ∧
      (((x = P.constantK ∧ (y = P.constantK → False)) → False) →
        P.apply (P.apply c x) y = P.constantK)) : False := by
  obtain ⟨n, hn⟩ : ∃ n : D, ∀ x, P.apply n x = P.apply (P.apply c x) (Fv P) :=
    ⟨Poly.abs P (.app (.app (.const c) .var) (.const (Fv P))), fun x => Poly.abs_apply P h _ x⟩
  apply no_negation_stroke_sem P h n
  intro x
  refine ⟨fun xT => ?_, fun xF => ?_⟩
  · rw [hn]
    exact (spec x (Fv P)).1 ⟨xT, fun e => T_ne_F P h e.symm⟩
  · rw [hn]
    exact (spec x (Fv P)).2 (fun both => xF both.1)

/-- An equality test `e` would give the horizontal `x ↦ e·x·T`. -/
theorem no_equality_test_sem (h : Pure.ECAConditions P) (e : D)
    (spec : ∀ x y, (x = y → P.apply (P.apply e x) y = P.constantK) ∧
      ((x = y → False) → P.apply (P.apply e x) y = Fv P)) : False := by
  obtain ⟨hh, hhh⟩ : ∃ hh : D, ∀ x, P.apply hh x = P.apply (P.apply e x) P.constantK :=
    ⟨Poly.abs P (.app (.app (.const e) .var) (.const P.constantK)),
      fun x => Poly.abs_apply P h _ x⟩
  apply no_horizontal_sem P h hh
  intro x
  refine ⟨fun xT => ?_, fun xF => ?_⟩
  · rw [hhh]
    exact (spec x P.constantK).1 xT
  · rw [hhh]
    exact (spec x P.constantK).2 xF

/-- A bivalent quantifier object `q` would give the horizontal `x ↦ q·(K·x)`. -/
theorem no_quantifier_object_sem (h : Pure.ECAConditions P) (q : D)
    (spec : ∀ f, ((∀ y, P.apply f y = P.constantK) → P.apply q f = P.constantK) ∧
      (((∀ y, P.apply f y = P.constantK) → False) → P.apply q f = Fv P)) : False := by
  obtain ⟨hh, hhh⟩ : ∃ hh : D, ∀ x, P.apply hh x = P.apply q (P.apply P.constantK x) :=
    ⟨Poly.abs P (.app (.const q) (.app (.const P.constantK) .var)),
      fun x => Poly.abs_apply P h _ x⟩
  apply no_horizontal_sem P h hh
  intro x
  refine ⟨fun xT => ?_, fun xF => ?_⟩
  · rw [hhh]
    exact (spec _).1 (fun y => (h.constant x y).trans xT)
  · rw [hhh]
    exact (spec _).2 (fun all => xF ((h.constant x x).symm.trans (all x)))

/-- A whole-domain case operator `d` would give the horizontal `x ↦ d·x·T·T·F`. -/
theorem no_case_operator_sem (h : Pure.ECAConditions P) (d : D)
    (spec : ∀ x y u v, (x = y → P.apply (P.apply (P.apply (P.apply d x) y) u) v = u) ∧
      ((x = y → False) → P.apply (P.apply (P.apply (P.apply d x) y) u) v = v)) : False := by
  obtain ⟨hh, hhh⟩ : ∃ hh : D, ∀ x, P.apply hh x =
      P.apply (P.apply (P.apply (P.apply d x) P.constantK) P.constantK) (Fv P) :=
    ⟨Poly.abs P (.app (.app (.app (.app (.const d) .var) (.const P.constantK))
        (.const P.constantK)) (.const (Fv P))),
      fun x => Poly.abs_apply P h _ x⟩
  apply no_horizontal_sem P h hh
  intro x
  refine ⟨fun xT => ?_, fun xF => ?_⟩
  · rw [hhh]
    exact (spec x P.constantK P.constantK (Fv P)).1 xT
  · rw [hhh]
    exact (spec x P.constantK P.constantK (Fv P)).2 xF

/-! #### Validity of the sentences -/

theorem lawV_valid (h : Pure.ECAConditions P) (o : Nat → D) : lawV.truth P o :=
  fun c d hc hd => lawV_sem P h c d hc hd

theorem universalIdentity_valid (h : Pure.ECAConditions P) (o : Nat → D) : universalIdentity.truth P o :=
  fun c => universal_sem P h c

theorem existentialIdentity_valid (h : Pure.ECAConditions P) (o : Nat → D) : existentialIdentity.truth P o :=
  fun c hc => existential_sem P h c hc

theorem connectives_valid (h : Pure.ECAConditions P) (o : Nat → D) : connectives.truth P o :=
  ⟨negation_sem P h, conjunction_sem P h, disjunction_sem P h⟩

theorem closure_valid (h : Pure.ECAConditions P) (o : Nat → D) : closure.truth P o :=
  fun c d hc hd => ⟨complement_sem P h c hc, intersection_sem P h c d hc hd, union_sem P h c d hc hd⟩

theorem collapse_valid (h : Pure.ECAConditions P) (o : Nat → D) : collapse.truth P o :=
  fun c hc => collapse_sem P h c hc

theorem noHorizontal_valid (h : Pure.ECAConditions P) (o : Nat → D) : noHorizontal.truth P o :=
  fun ⟨hh, spec⟩ => no_horizontal_sem P h hh spec

theorem noNegationStroke_valid (h : Pure.ECAConditions P) (o : Nat → D) : noNegationStroke.truth P o :=
  fun ⟨n, spec⟩ => no_negation_stroke_sem P h n spec

theorem noConditionalStroke_valid (h : Pure.ECAConditions P) (o : Nat → D) : noConditionalStroke.truth P o :=
  fun ⟨c, spec⟩ => no_conditional_stroke_sem P h c spec

theorem noEqualityTest_valid (h : Pure.ECAConditions P) (o : Nat → D) : noEqualityTest.truth P o :=
  fun ⟨e, spec⟩ => no_equality_test_sem P h e spec

theorem noQuantifierObject_valid (h : Pure.ECAConditions P) (o : Nat → D) : noQuantifierObject.truth P o :=
  fun ⟨q, spec⟩ => no_quantifier_object_sem P h q spec

theorem noCaseOperator_valid (h : Pure.ECAConditions P) (o : Nat → D) : noCaseOperator.truth P o :=
  fun ⟨d, spec⟩ => no_case_operator_sem P h d spec

end Semantics

/-! ### Derivability in NECA, NECA + RC and FF -/

abbrev TF := V3.Cleaner.theory
abbrev TR := V3.RelationalComprehension.theory

/-- A pure sentence valid in every nontrivial extensional combinatory algebra
is derivable in the bare ECA calculus, by completeness. -/
theorem bare_of_valid (φ : Pure.Formula)
    (valid : ∀ {D : Type} (P : Pure.Interpretation D), Pure.ECAConditions P →
      ∀ o, φ.truth P o) :
    Bare.theory ⊢ Bare.sentence φ := by
  apply Theory.Proof.complete_on_eq_models.{0, 0} (Bare.sentence φ)
  intro D _ _ _ model
  have eca := (Bare.models_theory_iff D).mp model
  exact (Bare.sentence_truth D φ).mpr (valid (Bare.extracted D) eca)

/-- Transfer from the bare calculus to NECA + RC and to FF (Theorem 5.2). -/
theorem both_of_bare (φ : Pure.Formula) (proof : Bare.theory ⊢ Bare.sentence φ) :
    (TR ⊢ sentence φ.functional) ∧ (TF ⊢ sentence φ.functional) :=
  ⟨(V3.Certificate.pure_conservativity_three_way φ).1.mp proof,
    (V3.Certificate.pure_conservativity_three_way φ).2.mp
      ((V3.Certificate.pure_conservativity_three_way φ).1.mp proof)⟩

theorem lawV_provable : (TR ⊢ sentence lawV.functional) ∧ (TF ⊢ sentence lawV.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => lawV_valid P hP))

theorem universalIdentity_provable :
    (TR ⊢ sentence universalIdentity.functional) ∧ (TF ⊢ sentence universalIdentity.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => universalIdentity_valid P hP))

theorem existentialIdentity_provable :
    (TR ⊢ sentence existentialIdentity.functional) ∧
      (TF ⊢ sentence existentialIdentity.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => existentialIdentity_valid P hP))

theorem connectives_provable :
    (TR ⊢ sentence connectives.functional) ∧ (TF ⊢ sentence connectives.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => connectives_valid P hP))

theorem closure_provable :
    (TR ⊢ sentence closure.functional) ∧ (TF ⊢ sentence closure.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => closure_valid P hP))

/-- `prop:concepts`: Law V for concepts, quantification as identity, the
Boolean connectives as objects, and closure of concepts under complement,
intersection and union, in NECA + RC and in FF. -/
theorem concepts_provable :
    type_of% lawV_provable ∧ type_of% universalIdentity_provable ∧
    type_of% existentialIdentity_provable ∧ type_of% connectives_provable ∧
    type_of% closure_provable :=
  ⟨lawV_provable, universalIdentity_provable, existentialIdentity_provable,
    connectives_provable, closure_provable⟩

/-- `thm:collapse`: every total bivalent object is constant, in NECA + RC and FF. -/
theorem collapse_provable :
    (TR ⊢ sentence collapse.functional) ∧ (TF ⊢ sentence collapse.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => collapse_valid P hP))

theorem noHorizontal_provable :
    (TR ⊢ sentence noHorizontal.functional) ∧ (TF ⊢ sentence noHorizontal.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => noHorizontal_valid P hP))

theorem noNegationStroke_provable :
    (TR ⊢ sentence noNegationStroke.functional) ∧ (TF ⊢ sentence noNegationStroke.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => noNegationStroke_valid P hP))

theorem noConditionalStroke_provable :
    (TR ⊢ sentence noConditionalStroke.functional) ∧
      (TF ⊢ sentence noConditionalStroke.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => noConditionalStroke_valid P hP))

theorem noEqualityTest_provable :
    (TR ⊢ sentence noEqualityTest.functional) ∧ (TF ⊢ sentence noEqualityTest.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => noEqualityTest_valid P hP))

theorem noQuantifierObject_provable :
    (TR ⊢ sentence noQuantifierObject.functional) ∧
      (TF ⊢ sentence noQuantifierObject.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => noQuantifierObject_valid P hP))

theorem noCaseOperator_provable :
    (TR ⊢ sentence noCaseOperator.functional) ∧ (TF ⊢ sentence noCaseOperator.functional) :=
  both_of_bare _ (bare_of_valid _ (fun P hP => noCaseOperator_valid P hP))

/-- `thm:horizontal`: no object is Frege's horizontal, and hence there is no
negation stroke, no conditional stroke, no equality test, no bivalent
quantifier object and no whole-domain case operator, in NECA + RC and in FF. -/
theorem strokes_provable :
    type_of% noHorizontal_provable ∧ type_of% noNegationStroke_provable ∧
    type_of% noConditionalStroke_provable ∧ type_of% noEqualityTest_provable ∧
    type_of% noQuantifierObject_provable ∧ type_of% noCaseOperator_provable :=
  ⟨noHorizontal_provable, noNegationStroke_provable, noConditionalStroke_provable,
    noEqualityTest_provable, noQuantifierObject_provable, noCaseOperator_provable⟩

end FregeanECA.V4.TruthValues

#print axioms FregeanECA.V4.TruthValues.collapse_provable
#print axioms FregeanECA.V4.TruthValues.concepts_provable
#print axioms FregeanECA.V4.TruthValues.strokes_provable
