import GSTStage37
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage36 GSTStage37

namespace GSTStage38

theorem control_eq_of_gap_zero
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (t : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r)
    (hzero : gap x r u t = 0) :
    u t = x.u t := by
  unfold gap at hzero
  have hsum :
      x.q * (competitorState x u t - state x t) ^ 2 +
        r * (u t - x.u t) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left
      (ne_of_gt (Real.exp_pos _))
  have hstate :
      0 ≤ x.q * (competitorState x u t - state x t) ^ 2 :=
    mul_nonneg hq (sq_nonneg _)
  have hcontrol : r * (u t - x.u t) ^ 2 = 0 := by
    apply le_antisymm
    · linarith
    · exact mul_nonneg hr.le (sq_nonneg _)
  have hsquare : (u t - x.u t) ^ 2 = 0 :=
    (mul_eq_zero.mp hcontrol).resolve_left (ne_of_gt hr)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

theorem control_eq_ae_of_gap_integral_zero
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hzero : (∫ t in Ioi (0 : ℝ), gap x r u t) = 0) :
    u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u := by
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] gap x r u := by
    apply Filter.Eventually.of_forall
    intro t
    change 0 ≤ gap x r u t
    unfold gap
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg
        (mul_nonneg hq (sq_nonneg _))
        (mul_nonneg hr.le (sq_nonneg _)))
  have hint := GSTStage36.gap_integrable x r u huMeas huBound
  have hgap : gap x r u =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  filter_upwards [hgap] with t ht
  have htzero : gap x r u t = 0 := ht
  exact control_eq_of_gap_zero x r u t hq hr htzero

-- Equality of objective values forces equality of controls a.e.
-- The class remains measurable, pointwise-bounded representatives.
theorem optimal_control_unique_ae
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r))))
    (heq : objective x r u = objective x r x.u) :
    u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u := by
  have hgap := GSTStage37.objective_gap_bound
    x r u hr hU hphiInitial hS huMeas huBound hclip
  rw [heq, sub_self] at hgap
  have hzero : (∫ t in Ioi (0 : ℝ), gap x r u t) = 0 :=
    le_antisymm hgap (GSTStage37.gap_integral_nonneg x r u hq hr.le)
  exact control_eq_ae_of_gap_integral_zero
    x r u hq hr huMeas huBound hzero

theorem strict_objective_loss_of_not_ae_eq
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r))))
    (hne : ¬ (u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u)) :
    objective x r u < objective x r x.u := by
  have hle := GSTStage37.objective_optimal
    x r hq hr hU hphiInitial hS hclip u huMeas huBound
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact (hne (optimal_control_unique_ae
      x r u hq hr hU hphiInitial hS huMeas huBound hclip heq)).elim

#print axioms control_eq_of_gap_zero
#print axioms control_eq_ae_of_gap_integral_zero
#print axioms optimal_control_unique_ae
#print axioms strict_objective_loss_of_not_ae_eq

end GSTStage38
