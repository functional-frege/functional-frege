import FregeanECA.Research.Z2Reverse.InternalTermQuotient
import FregeanECA.Research.Z2Reverse.InternalParallelBetaConfluence
import FregeanECA.Research.Z2Reverse.InternalPaths

/-!
Concrete K and S equations witnessed by internally coded beta paths.
The constants are the explicit numeric lambda codes used by the quotient
presentation; no combinatory algebra equations are assumed.
-/
namespace FregeanECA.Research.Z2Reverse.InternalCombinators
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open InternalLambdaCode InternalLambdaScope InternalBoundShift InternalBoundSubstitution
open InternalTermQuotient InternalParallelBeta InternalPaths
open scoped FFL.FirstOrder

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗣𝗔]

theorem shift_closed (t : V) (ht : IsScoped 0 t) (cutoff increment : V) :
    shift t cutoff increment = t :=
  shift_of_scoped t ht.term cutoff increment (ht.mono (by simp))

theorem substitute_closed (t : V) (ht : IsScoped 0 t) (cutoff replacement : V) :
    substitute t cutoff replacement = t :=
  substitute_of_scoped t ht.term cutoff replacement (ht.mono (by simp))

theorem beta_step {n body argument : V}
    (hb : IsScoped (n + 1) body) (ha : IsScoped n argument) :
    Parallel n (app (lam body) argument) (beta body argument) :=
  (Parallel.refl _ _ hb).beta (Parallel.refl _ _ ha)

theorem parallel_fo_definable (n : V) : Language.DefinableRel ℒₒᵣ (Parallel n) := by
  apply InternalPAInduction.definable_of_hierarchy (Γ := 𝚺₁)
  definability

theorem beta_K_first (x : V) (hx : IsScoped 0 x) :
    beta (lam (bvar 1)) x = lam x := by
  simp [beta, substitute_lam, shift_closed x hx]

theorem beta_S_first (x : V) (hx : IsScoped 0 x) :
    beta (lam (lam (app (app (bvar 2) (bvar 0)) (app (bvar 1) (bvar 0))))) x =
      lam (lam (app (app x (bvar 0)) (app (bvar 1) (bvar 0)))) := by
  simp [beta, substitute_lam, substitute_app, shift_closed x hx,
    one_add_one_eq_two, substitute_bvar_lt]

theorem beta_S_second (x y : V) (hx : IsScoped 0 x) (hy : IsScoped 0 y) :
    beta (lam (app (app x (bvar 0)) (app (bvar 1) (bvar 0)))) y =
      lam (app (app x (bvar 0)) (app y (bvar 0))) := by
  simp [beta, substitute_lam, substitute_app, hx.term, shift_closed y hy,
    substitute_closed x hx, substitute_bvar_lt]

theorem beta_S_third (x y z : V) (hx : IsScoped 0 x) (hy : IsScoped 0 y) :
    beta (app (app x (bvar 0)) (app y (bvar 0))) z = app (app x z) (app y z) := by
  simp [beta, substitute_app, hx.term, hy.term, substitute_closed x hx, substitute_closed y hy]

/-- K x y reduces to x by two internal parallel-beta steps. -/
theorem K_reduces (x y : V) (hx : IsScoped 0 x) (hy : IsScoped 0 y) :
    Reach (Parallel 0) (app (app constantK x) y) x := by
  have first : Parallel 0 (app constantK x) (lam x) := by
    simpa only [constantK, beta_K_first x hx] using
      beta_step (n := (0 : V)) (body := lam (bvar 1)) (by simp) hx
  have second : Parallel 0 (app (lam x) y) x := by
    simpa only [beta, substitute_closed x hx] using
      beta_step (hx.mono (by simp : (0 : V) ≤ 0 + 1)) hy
  exact reach_trans (Parallel 0) (parallel_fo_definable 0)
    (reach_single (first.app (Parallel.refl _ _ hy))) (reach_single second)

/-- S x y z reduces to (x z)(y z) by three internal parallel-beta steps. -/
theorem S_reduces (x y z : V) (hx : IsScoped 0 x) (hy : IsScoped 0 y) (hz : IsScoped 0 z) :
    Reach (Parallel 0) (app (app (app constantS x) y) z) (app (app x z) (app y z)) := by
  have first : Parallel 0 (app constantS x)
      (lam (lam (app (app x (bvar 0)) (app (bvar 1) (bvar 0))))) := by
    simpa only [constantS, beta_S_first x hx] using
      beta_step (n := (0 : V))
        (body := lam (lam (app (app (bvar 2) (bvar 0)) (app (bvar 1) (bvar 0)))))
        (by simp [one_add_one_eq_two]) hx
  have second : Parallel 0
      (app (lam (lam (app (app x (bvar 0)) (app (bvar 1) (bvar 0))))) y)
      (lam (app (app x (bvar 0)) (app y (bvar 0)))) := by
    simpa only [beta_S_second x y hx hy] using
      beta_step (n := (0 : V))
        (body := lam (app (app x (bvar 0)) (app (bvar 1) (bvar 0))))
        (by simp [hx.mono (by simp : (0 : V) ≤ 2), one_add_one_eq_two]) hy
  have third : Parallel 0
      (app (lam (app (app x (bvar 0)) (app y (bvar 0)))) z)
      (app (app x z) (app y z)) := by
    simpa only [beta_S_third x y z hx hy] using
      beta_step (n := (0 : V)) (body := app (app x (bvar 0)) (app y (bvar 0)))
        (by simp [hx.mono (by simp : (0 : V) ≤ 1), hy.mono (by simp : (0 : V) ≤ 1)]) hz
  exact reach_trans (Parallel 0) (parallel_fo_definable 0)
    (reach_single ((first.app (Parallel.refl _ _ hy)).app (Parallel.refl _ _ hz)))
    (reach_trans (Parallel 0) (parallel_fo_definable 0)
      (reach_single (second.app (Parallel.refl _ _ hz))) (reach_single third))

end FregeanECA.Research.Z2Reverse.InternalCombinators
