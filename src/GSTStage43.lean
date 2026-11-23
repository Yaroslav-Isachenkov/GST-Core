import GSTStage35
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage43

-- Algebraic consequence of clipping; no assumption on S.
theorem clipped_product_nonneg
    (R D r U : ℝ)
    (hR : 0 < R) (hr : 0 < r) :
    0 ≤ max 0 (min U (R * D / (2 * r))) * D := by
  by_cases hD : 0 ≤ D
  · exact mul_nonneg (le_max_left _ _) hD
  · have hDneg : D < 0 := lt_of_not_ge hD
    have hden : 0 < 2 * r := by linarith
    have hquot : R * D / (2 * r) ≤ 0 :=
      le_of_lt (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hR hDneg) hden)
    have hmin : min U (R * D / (2 * r)) ≤ 0 :=
      le_trans (min_le_right _ _) hquot
    rw [max_eq_left hmin, zero_mul]

theorem candidate_ud_nonneg
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))) :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ x.u t * d x t := by
  intro t ht
  rw [hclip t ht]
  exact clipped_product_nonneg
    (resource x.u x.eta x.B x.phiInitial t) (d x t) r x.U
    (resource_positive x.u x.eta x.B x.phiInitial t x.hB hi ht) hr

-- The same integral-defined z, with its existing AC and ODE properties.
theorem z_solution_rewritten
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (z x) 0 T ∧
      (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt (z x) (x.rho * z x t - x.u t * d x t) t) := by
  have hz :
      AbsolutelyContinuousOnInterval (z x) 0 T ∧
        (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
          HasDerivAt (z x)
            ((x.rho + x.eta * x.u t) * z x t -
              x.c * x.u t * p x t) t) :=
    GSTStage28.z_solution (toCostateData x) T hT
  refine ⟨hz.1, ?_⟩
  filter_upwards [hz.2] with t ht
  intro hmem
  have h := ht hmem
  have heq :
      x.rho * z x t - x.u t * d x t =
        (x.rho + x.eta * x.u t) * z x t -
          x.c * x.u t * p x t := by
    dsimp [d, GSTStage18.canonicalD]
    ring
  rw [heq]
  exact h

theorem discounted_z_tendsto_zero
    (x : StateData) :
    Tendsto (fun t => Real.exp (-x.rho * t) * z x t)
      atTop (𝓝 0) := by
  obtain ⟨Z, _hZ, hz⟩ := GSTStage35.z_linear_growth x
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ?_
    (GSTStage20.discounted_polynomial_tendsto_zero x.rho Z 1 x.hrho)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-x.rho * t) * |z x t|
        ≤ Real.exp (-x.rho * t) * (Z * (1 + t)) :=
      mul_le_mul_of_nonneg_left (hz t ht) (Real.exp_pos _).le
    _ = Z * (Real.exp (-x.rho * t) +
        t ^ (1 : ℕ) * Real.exp (-x.rho * t)) := by ring

#print axioms clipped_product_nonneg
#print axioms candidate_ud_nonneg
#print axioms z_solution_rewritten
#print axioms discounted_z_tendsto_zero

end GSTStage43
