import GSTStage41
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage36 GSTStage37
open GSTStage39 GSTStage40

namespace GSTStage42

-- No pointwise bounds or Borel measurability of the original control
-- are required. The representative is constructed, not assumed.
theorem measurable_bounded_representative
    (U : ℝ) (u : ℝ → ℝ) (hU : 0 ≤ U)
    (huMeas : AEMeasurable u (volume.restrict (Ioi (0 : ℝ))))
    (huBound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ u t ∧ u t ≤ U) :
    ∃ v : ℝ → ℝ,
      Measurable v ∧
      (∀ t : ℝ, 0 ≤ v t ∧ v t ≤ U) ∧
      v =ᵐ[volume.restrict (Ioi (0 : ℝ))] u := by
  rcases huMeas with ⟨w, hwMeas, huw⟩
  refine ⟨boundedRepresentative U w,
    representative_measurable U w hwMeas,
    representative_bounds U w hU, ?_⟩
  filter_upwards [huw, huBound] with t heq ht
  have hw : 0 ≤ w t ∧ w t ≤ U := by
    simpa only [heq] using ht
  exact (representative_eq_of_bounds U w t hw.1 hw.2).trans heq.symm

-- Consolidated sufficiency theorem.
-- x.u is the candidate; its states and costates are the previously
-- defined explicit trajectories and integral costates.
-- Existence of such a candidate is not asserted by this theorem.
theorem theorem2_sufficiency_and_uniqueness
    (x : StateData) (r : ℝ)
    (hq : 0 < x.q) (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))) :
    ∀ u : ℝ → ℝ,
      AEMeasurable u (volume.restrict (Ioi (0 : ℝ))) →
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ u t ∧ u t ≤ x.U) →
      IntegrableOn (discountedCost x r u) (Ioi (0 : ℝ)) ∧
      IntegrableOn (gap x r u) (Ioi (0 : ℝ)) ∧
      ((∫ t in Ioi (0 : ℝ), gap x r u t) ≤
        objective x r x.u - objective x r u) ∧
      (objective x r u ≤ objective x r x.u) ∧
      (objective x r u = objective x r x.u →
        u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u) ∧
      (¬ (u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u) →
        objective x r u < objective x r x.u) := by
  intro u huMeas huBound
  obtain ⟨v, hvMeas, hvAll, heq⟩ :=
    measurable_bounded_representative x.U u hU.le huMeas huBound
  have hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U := by
    intro t _ht
    exact hvAll t
  have hJv : objective x r v = objective x r u :=
    objective_eq_of_ae x r v u heq
  have hIv :
      (∫ t in Ioi (0 : ℝ), gap x r v t) =
        ∫ t in Ioi (0 : ℝ), gap x r u t :=
    integral_congr_ae (gap_ae_eq x r v u heq)
  have hcost : IntegrableOn (discountedCost x r u) (Ioi (0 : ℝ)) :=
    (GSTStage36.discounted_cost_integrable x r v hvMeas hvBound).congr
      (discounted_cost_ae_eq x r v u heq)
  have hgapInt : IntegrableOn (gap x r u) (Ioi (0 : ℝ)) :=
    (GSTStage36.gap_integrable x r v hvMeas hvBound).congr
      (gap_ae_eq x r v u heq)
  have hgap := GSTStage37.objective_gap_bound
    x r v hr hU hphiInitial hS hvMeas hvBound hclip
  rw [hJv, hIv] at hgap
  have hoptimal : objective x r u ≤ objective x r x.u := by
    have hnonneg := GSTStage37.gap_integral_nonneg x r u hq.le hr.le
    linarith
  have hunique :
      objective x r u = objective x r x.u →
        u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u := by
    intro hsame
    have hvJ : objective x r v = objective x r x.u := hJv.trans hsame
    have hvUnique := GSTStage38.optimal_control_unique_ae
      x r v hq.le hr hU hphiInitial hS hvMeas hvBound hclip hvJ
    exact heq.symm.trans hvUnique
  refine ⟨hcost, hgapInt, hgap, hoptimal, hunique, ?_⟩
  intro hne
  rcases lt_or_eq_of_le hoptimal with hlt | hequal
  · exact hlt
  · exact (hne (hunique hequal)).elim

#print axioms measurable_bounded_representative
#print axioms theorem2_sufficiency_and_uniqueness

end GSTStage42
