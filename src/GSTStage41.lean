import GSTStage40
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage36 GSTStage37
open GSTStage39 GSTStage40

namespace GSTStage41

theorem integrable_of_ae_bounds
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    IntegrableOn (discountedCost x r u) (Ioi (0 : ℝ)) ∧
      IntegrableOn (gap x r u) (Ioi (0 : ℝ)) := by
  let v := boundedRepresentative x.U u
  have hvMeas : Measurable v := representative_measurable x.U u huMeas
  have hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U := by
    intro t _ht
    exact representative_bounds x.U u (toCostateData x).hU t
  have heq : v =ᵐ[volume.restrict (Ioi (0 : ℝ))] u :=
    representative_ae_on_Ioi x.U u huBound
  have hcost := GSTStage36.discounted_cost_integrable x r v hvMeas hvBound
  have hgap := GSTStage36.gap_integrable x r v hvMeas hvBound
  exact ⟨
    hcost.congr (discounted_cost_ae_eq x r v u heq),
    hgap.congr (gap_ae_eq x r v u heq)
  ⟩

theorem objective_gap_bound_ae
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))) :
    (∫ t in Ioi (0 : ℝ), gap x r u t) ≤
      objective x r x.u - objective x r u := by
  let v := boundedRepresentative x.U u
  have hvMeas : Measurable v := representative_measurable x.U u huMeas
  have hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U := by
    intro t _ht
    exact representative_bounds x.U u hU.le t
  have heq : v =ᵐ[volume.restrict (Ioi (0 : ℝ))] u :=
    representative_ae_on_Ioi x.U u huBound
  have hgap := GSTStage37.objective_gap_bound
    x r v hr hU hphiInitial hS hvMeas hvBound hclip
  have hJ : objective x r v = objective x r u :=
    objective_eq_of_ae x r v u heq
  have hI :
      (∫ t in Ioi (0 : ℝ), gap x r v t) =
        ∫ t in Ioi (0 : ℝ), gap x r u t :=
    integral_congr_ae (gap_ae_eq x r v u heq)
  rw [hJ, hI] at hgap
  exact hgap

theorem objective_optimal_ae
    (x : StateData) (r : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))) :
    ∀ u : ℝ → ℝ, Measurable u →
      (∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r x.u := by
  intro u huMeas huBound
  have hgap := objective_gap_bound_ae
    x r u hr hU hphiInitial hS huMeas huBound hclip
  have hnonneg := GSTStage37.gap_integral_nonneg x r u hq hr.le
  linarith

theorem optimal_control_unique_ae
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r))))
    (hJ : objective x r u = objective x r x.u) :
    u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u := by
  let v := boundedRepresentative x.U u
  have hvMeas : Measurable v := representative_measurable x.U u huMeas
  have hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U := by
    intro t _ht
    exact representative_bounds x.U u hU.le t
  have heq : v =ᵐ[volume.restrict (Ioi (0 : ℝ))] u :=
    representative_ae_on_Ioi x.U u huBound
  have hvJ : objective x r v = objective x r x.u :=
    (objective_eq_of_ae x r v u heq).trans hJ
  have hvUnique : v =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u :=
    GSTStage38.optimal_control_unique_ae
      x r v hq hr hU hphiInitial hS hvMeas hvBound hclip hvJ
  exact heq.symm.trans hvUnique

theorem strict_objective_loss_ae
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hq : 0 ≤ x.q) (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r))))
    (hne : ¬ (u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u)) :
    objective x r u < objective x r x.u := by
  have hle := objective_optimal_ae
    x r hq hr hU hphiInitial hS hclip u huMeas huBound
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact (hne (optimal_control_unique_ae
      x r u hq hr hU hphiInitial hS huMeas huBound hclip heq)).elim

#print axioms integrable_of_ae_bounds
#print axioms objective_gap_bound_ae
#print axioms objective_optimal_ae
#print axioms optimal_control_unique_ae
#print axioms strict_objective_loss_ae

end GSTStage41
