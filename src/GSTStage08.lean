import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage08

-- Fundamental theorem with an explicitly supplied a.e. derivative.
-- No assumption of differentiability at every point.
theorem ac_integral_identity
    (H D : ℝ → ℝ) (a b : ℝ)
    (hAC : AbsolutelyContinuousOnInterval H a b)
    (hD : ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt H (D t) t) :
    (∫ t in a..b, D t) = H b - H a := by
  calc
    (∫ t in a..b, D t) = ∫ t in a..b, deriv H t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hD] with t ht hmem
      exact (ht (uIoc_subset_uIcc hmem)).deriv.symm
    _ = H b - H a := hAC.integral_deriv_eq_sub

-- Replacement for the stage03 estimate:
-- absolute continuity + derivative relation almost everywhere.
theorem ac_finite_interval_nonpos
    (H R m : ℝ → ℝ) (eta T : ℝ)
    (heta : 0 < eta) (hT : 0 ≤ T)
    (hAC : AbsolutelyContinuousOnInterval H 0 T)
    (hD : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt H (R t - eta * m t) t)
    (hR : IntervalIntegrable R volume 0 T)
    (hm : IntervalIntegrable m volume 0 T)
    (hsign : ∀ t ∈ Icc (0 : ℝ) T, R t ≤ 0)
    (hboundary : H 0 ≤ H T) :
    (∫ t in (0 : ℝ)..T, m t) ≤ 0 := by
  have hz : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 T :=
    intervalIntegrable_const
  have hRzero : (∫ t in (0 : ℝ)..T, R t) ≤ 0 := by
    simpa using intervalIntegral.integral_mono_on hT hR hz hsign
  have hFTC := ac_integral_identity
    H (fun t => R t - eta * m t) 0 T hAC hD
  rw [intervalIntegral.integral_sub hR (hm.const_mul eta),
      intervalIntegral.integral_const_mul] at hFTC
  by_contra hn
  have hpos : 0 < (∫ t in (0 : ℝ)..T, m t) := lt_of_not_ge hn
  have hprod := mul_pos heta hpos
  linarith

#print axioms ac_integral_identity
#print axioms ac_finite_interval_nonpos

end GSTStage08
