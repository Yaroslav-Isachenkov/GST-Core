import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage04

-- Arbitrary natural degree, arbitrary positive discount.
theorem discounted_monomial_integrable
    (rho : ℝ) (hrho : 0 < rho) (n : ℕ) :
    IntegrableOn
      (fun t : ℝ => t^n * Real.exp (-rho * t))
      (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := (1 : ℝ)) (b := rho)
    (by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith) (by rfl) hrho
  simpa only [Real.rpow_natCast, Real.rpow_one] using h

theorem envelope_integrable
    (rho C : ℝ) (hrho : 0 < rho) (n : ℕ) :
    IntegrableOn
      (fun t : ℝ => C * (1 + t^n) * Real.exp (-rho * t))
      (Ioi (0 : ℝ)) := by
  have h0 : IntegrableOn
      (fun t : ℝ => Real.exp (-rho * t)) (Ioi (0 : ℝ)) := by
    simpa using discounted_monomial_integrable rho hrho 0
  have hn := discounted_monomial_integrable rho hrho n
  have heq :
      (fun t : ℝ =>
        C * (Real.exp (-rho * t) + t^n * Real.exp (-rho * t))) =
      (fun t : ℝ =>
        C * (1 + t^n) * Real.exp (-rho * t)) := by
    funext t
    ring
  rw [← heq]
  exact (h0.add hn).const_mul C

-- Measurability and the explicit bound are hypotheses.
-- Integrability is a conclusion, not an assumption.
theorem dominated_integrable
    (f : ℝ → ℝ) (rho C : ℝ) (n : ℕ)
    (hrho : 0 < rho)
    (hmeas : AEStronglyMeasurable f
      (volume.restrict (Ioi (0 : ℝ))))
    (hbound : ∀ t : ℝ, 0 < t →
      |f t| ≤ C * (1 + t^n) * Real.exp (-rho * t)) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  apply (envelope_integrable rho C hrho n).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using hbound t ht

theorem partial_integrals_converge
    (f : ℝ → ℝ) (rho C : ℝ) (n : ℕ)
    (hrho : 0 < rho)
    (hmeas : AEStronglyMeasurable f
      (volume.restrict (Ioi (0 : ℝ))))
    (hbound : ∀ t : ℝ, 0 < t →
      |f t| ≤ C * (1 + t^n) * Real.exp (-rho * t)) :
    Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t)
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), f t)) := by
  exact intervalIntegral_tendsto_integral_Ioi 0
    (dominated_integrable f rho C n hrho hmeas hbound)
    tendsto_id

-- Infinite-horizon sign, with convergence obtained from the bound.
theorem improper_integral_nonpos
    (f : ℝ → ℝ) (rho C : ℝ) (n : ℕ)
    (hrho : 0 < rho)
    (hmeas : AEStronglyMeasurable f
      (volume.restrict (Ioi (0 : ℝ))))
    (hbound : ∀ t : ℝ, 0 < t →
      |f t| ≤ C * (1 + t^n) * Real.exp (-rho * t))
    (hfinite : ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, f t) ≤ 0) :
    (∫ t in Ioi (0 : ℝ), f t) ≤ 0 := by
  apply le_of_tendsto
    (partial_integrals_converge f rho C n hrho hmeas hbound)
  exact Filter.eventually_atTop.2
    ⟨0, fun T hT => hfinite T hT⟩

#print axioms discounted_monomial_integrable
#print axioms envelope_integrable
#print axioms dominated_integrable
#print axioms partial_integrals_converge
#print axioms improper_integral_nonpos

end GSTStage04
