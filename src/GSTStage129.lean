import GSTStage128

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage37 GSTStage128

namespace GSTStage129

theorem continuous_optimal_representative
    (x : StateData) (r : ℝ) (hr : 0 < r)
    (hoptimal : ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r x.u) :
    Continuous (clippedControl x r) ∧
    Measurable (clippedControl x r) ∧
    (∀ t : ℝ,
      0 ≤ clippedControl x r t ∧ clippedControl x r t ≤ x.U) ∧
    (clippedControl x r =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u) ∧
    (∀ t : ℝ, 0 ≤ t →
      resource (clippedControl x r) x.eta x.B x.phiInitial t =
        resource x.u x.eta x.B x.phiInitial t) ∧
    (∀ t : ℝ, 0 ≤ t →
      competitorState x (clippedControl x r) t =
        competitorState x x.u t) ∧
    objective x r (clippedControl x r) = objective x r x.u ∧
    (∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r (clippedControl x r)) := by
  have hc := clipped_control_continuous x r
  have ha := optimal_control_clipping_ae x r hr hoptimal
  have heq :
      clippedControl x r =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u := by
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with t ht hmem
    have ht0 : 0 ≤ t := le_of_lt (show 0 < t from hmem)
    exact (clipped_control_eq x r t ht0).trans ht.symm
  have hphi : ∀ t : ℝ, 0 ≤ t →
      resource (clippedControl x r) x.eta x.B x.phiInitial t =
        resource x.u x.eta x.B x.phiInitial t := by
    intro t ht
    exact GSTStage40.resource_eq_of_ae
      (clippedControl x r) x.u x.eta x.B x.phiInitial t ht heq
  have homega : ∀ t : ℝ, 0 ≤ t →
      competitorState x (clippedControl x r) t =
        competitorState x x.u t := by
    intro t ht
    exact GSTStage40.omega_eq_of_ae
      (clippedControl x r) x.u
      x.eta x.B x.phiInitial x.a x.c x.omegaInitial t ht heq
  have hJ : objective x r (clippedControl x r) = objective x r x.u :=
    GSTStage40.objective_eq_of_ae x r (clippedControl x r) x.u heq
  refine ⟨hc, hc.measurable, clipped_control_bounds x r,
    heq, hphi, homega, hJ, ?_⟩
  intro u huMeas huBound
  rw [hJ]
  exact hoptimal u huMeas huBound

end GSTStage129

#print axioms GSTStage129.continuous_optimal_representative
