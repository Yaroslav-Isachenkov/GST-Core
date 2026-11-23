import GSTStage134

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage135

theorem costate_pair_unique_of_polynomial_growth
    (x : GSTStage28.CostateData) (P Z : ℝ → ℝ)
    (CP CZ : ℝ) (nP nZ : ℕ)
    (hPAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval P 0 T)
    (hZAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval Z 0 T)
    (hPODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt P
        ((x.rho + x.a) * P t +
          2 * x.q * (x.omega t - x.target)) t)
    (hZODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt Z
        ((x.rho + x.eta * x.u t) * Z t -
          x.c * x.u t * P t) t)
    (hPBound : ∀ t : ℝ, 0 ≤ t →
      |P t| ≤ CP * (1 + t ^ nP))
    (hZBound : ∀ t : ℝ, 0 ≤ t →
      |Z t| ≤ CZ * (1 + t ^ nZ)) :
    ∀ t : ℝ, 0 ≤ t →
      P t = GSTStage28.pOf x t ∧
      Z t = GSTStage28.zOf x t := by
  have hp := GSTStage134.p_unique_of_polynomial_growth
    x P CP nP hPAC hPODE hPBound
  have hZODE' : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt Z
        ((x.rho + x.eta * x.u t) * Z t -
          x.c * x.u t * GSTStage28.pOf x t) t := by
    filter_upwards [hZODE] with t ht ht0
    have hd := ht ht0
    rw [hp t ht0] at hd
    exact hd
  have hz := GSTStage134.z_unique_of_polynomial_growth
    x Z CZ nZ hZAC hZODE' hZBound
  exact fun t ht => ⟨hp t ht, hz t ht⟩

theorem state_costate_pair_unique_of_polynomial_growth
    (x : GSTStage31.StateData) (P Z : ℝ → ℝ)
    (CP CZ : ℝ) (nP nZ : ℕ)
    (hPAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval P 0 T)
    (hZAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval Z 0 T)
    (hPODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt P
        ((x.rho + x.a) * P t +
          2 * x.q * (GSTStage31.state x t - x.target)) t)
    (hZODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt Z
        ((x.rho + x.eta * x.u t) * Z t -
          x.c * x.u t * P t) t)
    (hPBound : ∀ t : ℝ, 0 ≤ t →
      |P t| ≤ CP * (1 + t ^ nP))
    (hZBound : ∀ t : ℝ, 0 ≤ t →
      |Z t| ≤ CZ * (1 + t ^ nZ)) :
    ∀ t : ℝ, 0 ≤ t →
      P t = GSTStage31.p x t ∧
      Z t = GSTStage31.z x t := by
  exact costate_pair_unique_of_polynomial_growth
    (GSTStage31.toCostateData x) P Z CP CZ nP nZ
    hPAC hZAC hPODE hZODE hPBound hZBound

end GSTStage135

#print axioms GSTStage135.costate_pair_unique_of_polynomial_growth
#print axioms GSTStage135.state_costate_pair_unique_of_polynomial_growth
