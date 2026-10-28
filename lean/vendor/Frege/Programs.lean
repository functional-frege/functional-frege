/- Intrinsically scoped program trees. Coefficients are fixed outside all program
binders. This formalises the program-tree layer, not the mutual ambient PE syntax. -/
namespace Frege

universe u

inductive Program (Coeff : Type u) : Nat → Type u where
  | var : Fin n → Program Coeff n
  | coeff : Coeff → Program Coeff n
  | app : Program Coeff n → Program Coeff n → Program Coeff n
  | lam : Program Coeff (n + 1) → Program Coeff n
  deriving Repr, DecidableEq

namespace Program

variable {C : Type u} {n m k : Nat}

def liftRen (ρ : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

def rename : {n m : Nat} → (Fin n → Fin m) → Program C n → Program C m
  | _, _, ρ, .var i => .var (ρ i)
  | _, _, _, .coeff c => .coeff c
  | _, _, ρ, .app p q => .app (rename ρ p) (rename ρ q)
  | _, _, ρ, .lam p => .lam (rename (liftRen ρ) p)

@[simp] theorem liftRen_zero (ρ : Fin n → Fin m) : liftRen ρ 0 = 0 := rfl
@[simp] theorem liftRen_succ (ρ : Fin n → Fin m) (i : Fin n) :
    liftRen ρ i.succ = (ρ i).succ := rfl

theorem liftRen_id : liftRen (id : Fin n → Fin n) = id := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem liftRen_comp (ρ : Fin n → Fin m) (τ : Fin m → Fin k) :
    (fun i => liftRen τ (liftRen ρ i)) = liftRen (fun i => τ (ρ i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem rename_id (p : Program C n) : rename id p = p := by
  induction p with
  | var i => rfl
  | coeff c => rfl
  | app p q hp hq => simp [rename, hp, hq]
  | lam p hp => simp [rename, liftRen_id, hp]

theorem rename_comp (p : Program C n) (ρ : Fin n → Fin m)
    (τ : Fin m → Fin k) :
    rename τ (rename ρ p) = rename (fun i => τ (ρ i)) p := by
  induction p generalizing m k with
  | var i => rfl
  | coeff c => rfl
  | app p q hp hq => simp [rename, hp, hq]
  | lam p hp => simp [rename, hp, liftRen_comp]

def liftSub (σ : Fin n → Program C m) : Fin (n+1) → Program C (m+1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

def subst : {n m : Nat} → (Fin n → Program C m) → Program C n → Program C m
  | _, _, σ, .var i => σ i
  | _, _, _, .coeff c => .coeff c
  | _, _, σ, .app p q => .app (subst σ p) (subst σ q)
  | _, _, σ, .lam p => .lam (subst (liftSub σ) p)

@[simp] theorem liftSub_zero (σ : Fin n → Program C m) :
    liftSub σ 0 = .var 0 := rfl
@[simp] theorem liftSub_succ (σ : Fin n → Program C m) (i : Fin n) :
    liftSub σ i.succ = rename Fin.succ (σ i) := rfl

theorem liftSub_var : liftSub (Program.var : Fin n → Program C n) = Program.var := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

@[simp] theorem subst_var (p : Program C n) : subst Program.var p = p := by
  induction p with
  | var i => rfl
  | coeff c => rfl
  | app p q hp hq => simp [subst, hp, hq]
  | lam p hp => simp [subst, liftSub_var, hp]

theorem subst_rename (p : Program C n) (ρ : Fin n → Fin m)
    (σ : Fin m → Program C k) :
    subst σ (rename ρ p) = subst (fun i => σ (ρ i)) p := by
  induction p generalizing m k with
  | var i => rfl
  | coeff c => rfl
  | app p q hp hq => simp [rename, subst, hp, hq]
  | lam p hp =>
    simp only [rename, subst, hp]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem rename_subst (p : Program C n) (σ : Fin n → Program C m)
    (ρ : Fin m → Fin k) :
    rename ρ (subst σ p) = subst (fun i => rename ρ (σ i)) p := by
  induction p generalizing m k with
  | var i => rfl
  | coeff c => rfl
  | app p q hp hq => simp [rename, subst, hp, hq]
  | lam p hp =>
    simp only [rename, subst, hp]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [liftSub_succ, rename_comp]
      rfl

theorem subst_comp (p : Program C n) (σ : Fin n → Program C m)
    (τ : Fin m → Program C k) :
    subst τ (subst σ p) = subst (fun i => subst τ (σ i)) p := by
  induction p generalizing m k with
  | var i => rfl
  | coeff c => rfl
  | app p q hp hq => simp [subst, hp, hq]
  | lam p hp =>
    simp only [subst, hp]
    congr 2
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [liftSub_succ, subst_rename, rename_subst]

def single (q : Program C n) : Fin (n+1) → Program C n := Fin.cases q .var

def beta (p : Program C (n+1)) (q : Program C n) : Program C n := subst (single q) p

inductive Step {C : Type u} : {n : Nat} → Program C n → Program C n → Prop where
  | beta {n : Nat} (p : Program C (n+1)) (q : Program C n) :
      Step (.app (.lam p) q) (beta p q)
  | left {n : Nat} {p p' q : Program C n} : Step p p' → Step (.app p q) (.app p' q)
  | right {n : Nat} {p q q' : Program C n} : Step q q' → Step (.app p q) (.app p q')
  | underLam {n : Nat} {p p' : Program C (n+1)} : Step p p' → Step (.lam p) (.lam p')

inductive Steps : Program C n → Program C n → Prop where
  | refl (p) : Steps p p
  | next : Step p q → Steps q r → Steps p r

end Program
end Frege
