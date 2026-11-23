import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace GSTStage07

-- The actual clipping rule, not an assumed variational inequality.
theorem clipping_variational_sign
    (r U w u : ℝ)
    (hr : 0 < r) (hU : 0 < U)
    (hu0 : 0 ≤ u) (huU : u ≤ U) :
    let v := max 0 (min U (w / (2 * r)))
    (-2 * r * v + w) * (u - v) ≤ 0 := by
  dsimp only
  have hden : 0 < 2 * r := by linarith
  by_cases hlo : w / (2 * r) ≤ 0
  · have hmin : min U (w / (2 * r)) ≤ 0 :=
      le_trans (min_le_right _ _) hlo
    rw [max_eq_left hmin]
    have hw : w ≤ 0 := by
      have h := (div_le_iff₀ hden).mp hlo
      nlinarith
    simpa using mul_nonpos_of_nonpos_of_nonneg hw hu0
  · have hx : 0 < w / (2 * r) := lt_of_not_ge hlo
    by_cases hhi : U ≤ w / (2 * r)
    · rw [min_eq_left hhi, max_eq_right hU.le]
      have hw : 0 ≤ -2 * r * U + w := by
        have h := (le_div_iff₀ hden).mp hhi
        nlinarith
      exact mul_nonpos_of_nonneg_of_nonpos hw (sub_nonpos.mpr huU)
    · have hxU : w / (2 * r) ≤ U := (lt_of_not_ge hhi).le
      rw [min_eq_right hxU, max_eq_right hx.le]
      have hzero : -2 * r * (w / (2 * r)) + w = 0 := by
        have hr0 : r ≠ 0 := ne_of_gt hr
        field_simp
        ring
      rw [hzero]
      simp

-- Derivation of equation (13) for d = c*p - eta*z.
-- S is expanded here as a*p + 2*q*(omega - target).
theorem costate_difference_derivative
    (p z : ℝ → ℝ)
    (t a c eta rho q omega target v : ℝ)
    (hp : HasDerivAt p
      ((rho + a) * p t + 2 * q * (omega - target)) t)
    (hz : HasDerivAt z
      ((rho + eta * v) * z t - c * v * p t) t) :
    HasDerivAt (fun s => c * p s - eta * z s)
      ((rho + eta * v) * (c * p t - eta * z t)
        + c * (a * p t + 2 * q * (omega - target))) t := by
  convert (hp.const_mul c).sub (hz.const_mul eta) using 1
  all_goals ring

#print axioms clipping_variational_sign
#print axioms costate_difference_derivative

end GSTStage07
