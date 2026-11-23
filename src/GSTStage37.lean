import GSTStage36
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage36

namespace GSTStage37

-- J is the negative of the discounted running-cost integral.
noncomputable def objective
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) : ℝ :=
  -(∫ t in Ioi (0 : ℝ), discountedCost x r u t)

theorem cost_difference_integral_eq_objective_gap
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    (∫ t in Ioi (0 : ℝ), costDifference x r u t) =
      objective x r x.u - objective x r u := by
  have huInt := discounted_cost_integrable x r u huMeas huBound
  have hvInt := discounted_cost_integrable x r x.u x.huMeas x.hu
  have heq : costDifference x r u =
      (fun t => discountedCost x r u t - discountedCost x r x.u t) := by
    funext t
    dsimp [costDifference, discountedCost, competitorState, state]
    ring
  unfold objective
  rw [heq, integral_sub huInt hvInt]
  ring

theorem infinite_cost_gap
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))) :
    (∫ t in Ioi (0 : ℝ), gap x r u t) ≤
      ∫ t in Ioi (0 : ℝ), costDifference x r u t := by
  have hconv := GSTStage36.partial_integrals_converge x r u huMeas huBound
  have hboundary := GSTStage35.boundary_tendsto_zero x u huMeas huBound
  have hleft :
      Tendsto
        (fun T : ℝ =>
          (∫ t in (0 : ℝ)..T, gap x r u t) + boundary x u T)
        atTop (𝓝 ((∫ t in Ioi (0 : ℝ), gap x r u t) + 0)) :=
    hconv.2.1.add hboundary
  have hfinite : ∀ᶠ T : ℝ in atTop,
      (∫ t in (0 : ℝ)..T, gap x r u t) + boundary x u T ≤
        ∫ t in (0 : ℝ)..T, costDifference x r u t := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact GSTStage34.finite_cost_gap
      x r u T hT hr hU hphiInitial hS huMeas huBound hclip
  have h := le_of_tendsto_of_tendsto hleft hconv.2.2 hfinite
  simpa only [add_zero] using h

theorem objective_gap_bound
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))) :
    (∫ t in Ioi (0 : ℝ), gap x r u t) ≤
      objective x r x.u - objective x r u := by
  rw [← cost_difference_integral_eq_objective_gap x r u huMeas huBound]
  exact infinite_cost_gap
    x r u hr hU hphiInitial hS huMeas huBound hclip

theorem gap_integral_nonneg
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hq : 0 ≤ x.q) (hr : 0 ≤ r) :
    0 ≤ ∫ t in Ioi (0 : ℝ), gap x r u t := by
  apply integral_nonneg
  intro t
  unfold gap
  exact mul_nonneg (Real.exp_pos _).le
    (add_nonneg
      (mul_nonneg hq (sq_nonneg _))
      (mul_nonneg hr (sq_nonneg _)))

-- Conditional global optimality in the stated class of controls.
-- This does not assert that a clipped candidate exists.
theorem objective_optimal
    (x : StateData) (r : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))) :
    ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r x.u := by
  intro u huMeas huBound
  have hgap := objective_gap_bound
    x r u hr hU hphiInitial hS huMeas huBound hclip
  have hnonneg := gap_integral_nonneg x r u hq hr.le
  linarith

#print axioms cost_difference_integral_eq_objective_gap
#print axioms infinite_cost_gap
#print axioms objective_gap_bound
#print axioms gap_integral_nonneg
#print axioms objective_optimal

end GSTStage37
