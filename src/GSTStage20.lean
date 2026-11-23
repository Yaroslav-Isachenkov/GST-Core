import GSTStage19
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage19

namespace GSTStage20

theorem discounted_polynomial_tendsto_zero
    (rho C : ℝ) (n : ℕ) (hrho : 0 < rho) :
    Tendsto
      (fun t : ℝ =>
        C * (Real.exp (-rho * t) + t ^ n * Real.exp (-rho * t)))
      atTop (𝓝 0) := by
  have hzero : Tendsto
      (fun t : ℝ => Real.exp (-rho * t)) atTop (𝓝 0) := by
    simpa using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 rho hrho
  have hn : Tendsto
      (fun t : ℝ => t ^ n * Real.exp (-rho * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (n : ℝ) rho hrho
  simpa using (hzero.add hn).const_mul C

theorem weight_le_discount
    (v : ℝ → ℝ) (eta rho t : ℝ)
    (heta : 0 ≤ eta) (ht : 0 ≤ t)
    (hv : ∀ᵐ s : ℝ, 0 ≤ s → 0 ≤ v s) :
    weight v eta rho t ≤ Real.exp (-rho * t) := by
  have hnonneg : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) t),
      0 ≤ v s := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hv] with s hs hmem
    exact hs hmem.1
  have hint : 0 ≤ ∫ s in (0 : ℝ)..t, v s :=
    intervalIntegral.integral_nonneg_of_ae_restrict ht hnonneg
  unfold weight cumulative
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (mul_nonneg heta hint)

-- The polynomial bound is explicit; it is not derived here.
theorem weighted_tail_from_polynomial_bound
    (v d : ℝ → ℝ) (eta rho C : ℝ) (n : ℕ)
    (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hv : ∀ᵐ s : ℝ, 0 ≤ s → 0 ≤ v s)
    (hpoly : ∀ t : ℝ, 0 ≤ t → |d t| ≤ C * (1 + t ^ n)) :
    Tendsto (fun t => weight v eta rho t * d t)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ?_
    (discounted_polynomial_tendsto_zero rho C n hrho)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (weight_positive v eta rho t)]
  calc
    weight v eta rho t * |d t|
        ≤ Real.exp (-rho * t) * |d t| :=
      mul_le_mul_of_nonneg_right
        (weight_le_discount v eta rho t heta ht hv) (abs_nonneg _)
    _ ≤ Real.exp (-rho * t) * (C * (1 + t ^ n)) :=
      mul_le_mul_of_nonneg_left (hpoly t ht)
        (le_of_lt (Real.exp_pos _))
    _ = C * (Real.exp (-rho * t) + t ^ n * Real.exp (-rho * t)) := by
      ring

-- The terminal-limit hypothesis of stage19 has been replaced
-- by a polynomial-growth bound, positive discount and v >= 0 a.e.
theorem d_nonneg_from_polynomial_bound
    (v d S : ℝ → ℝ) (eta rho c C : ℝ) (n : ℕ)
    (heta : 0 ≤ eta) (hrho : 0 < rho) (hc : 0 ≤ c)
    (hvnonneg : ∀ᵐ s : ℝ, 0 ≤ s → 0 ≤ v s)
    (hv : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable v volume 0 T)
    (hdAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval d 0 T)
    (hScont : ∀ T : ℝ, 0 ≤ T →
      ContinuousOn S (uIcc (0 : ℝ) T))
    (hdODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt d ((rho + eta * v t) * d t + c * S t) t)
    (hS : ∀ t : ℝ, 0 ≤ t → S t ≤ 0)
    (hpoly : ∀ t : ℝ, 0 ≤ t → |d t| ≤ C * (1 + t ^ n)) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ d t := by
  exact d_nonneg_from_weighted_limit
    v d S eta rho c hc hv hdAC hScont hdODE hS
    (weighted_tail_from_polynomial_bound
      v d eta rho C n heta hrho hvnonneg hpoly)

#print axioms discounted_polynomial_tendsto_zero
#print axioms weight_le_discount
#print axioms weighted_tail_from_polynomial_bound
#print axioms d_nonneg_from_polynomial_bound

end GSTStage20
