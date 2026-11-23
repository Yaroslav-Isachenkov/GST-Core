import GSTStage130

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage37 GSTStage128

namespace GSTStage131

-- All model parameters and initial conditions are inherited from x.
noncomputable def continuousRepresentativeData
    (x : StateData) (r : ℝ) : StateData :=
  { x with
    u := clippedControl x r
    huMeas := (clipped_control_continuous x r).measurable
    hu := fun t _ => clipped_control_bounds x r t }

theorem optimal_representative_self_clipping
    (x : StateData) (r : ℝ) (hr : 0 < r)
    (hoptimal : ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r x.u) :
    let y := continuousRepresentativeData x r
    Continuous y.u ∧
    (y.u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u) ∧
    (∀ t : ℝ, 0 ≤ t →
      resource y.u y.eta y.B y.phiInitial t =
        resource x.u x.eta x.B x.phiInitial t) ∧
    (∀ t : ℝ, 0 ≤ t → state y t = state x t) ∧
    objective y r y.u = objective x r x.u ∧
    (∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ y.U) →
      objective y r u ≤ objective y r y.u) ∧
    (∀ t : ℝ, 0 ≤ t →
      y.u t = max 0 (min y.U
        ((resource y.u y.eta y.B y.phiInitial t * d y t) / (2 * r)))) := by
  dsimp only
  let y := continuousRepresentativeData x r
  obtain ⟨hc, _hm, _hb, heq, hphi, homega, hJ, hopt⟩ :=
    GSTStage129.continuous_optimal_representative x r hr hoptimal
  have hyCont : Continuous y.u := hc
  have hyEq : y.u =ᵐ[volume.restrict (Ioi (0 : ℝ))] x.u := heq
  have hyPhi : ∀ t : ℝ, 0 ≤ t →
      resource y.u y.eta y.B y.phiInitial t =
        resource x.u x.eta x.B x.phiInitial t := hphi
  have hyState : ∀ t : ℝ, 0 ≤ t → state y t = state x t := by
    intro t ht
    exact homega t ht
  have hyJ : objective y r y.u = objective x r x.u := hJ
  have hyOpt : ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ y.U) →
      objective y r u ≤ objective y r y.u := by
    intro u huMeas huBound
    exact hopt u huMeas huBound
  have hyClip := GSTStage130.continuous_optimal_control_clipping
    y r hr hyCont.continuousOn hyOpt
  exact ⟨hyCont, hyEq, hyPhi, hyState, hyJ, hyOpt, hyClip⟩

end GSTStage131

#print axioms GSTStage131.optimal_representative_self_clipping
