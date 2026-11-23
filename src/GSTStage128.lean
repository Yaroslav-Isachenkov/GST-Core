import GSTStage127

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage37

namespace GSTStage128

-- The value at zero provides a continuous extension to negative times.
noncomputable def clippedControl (x : StateData) (r t : ℝ) : ℝ :=
  max 0 (min x.U
    ((resource x.u x.eta x.B x.phiInitial (max 0 t) *
      d x (max 0 t)) / (2 * r)))

theorem clipped_control_continuous (x : StateData) (r : ℝ) :
    Continuous (clippedControl x r) := by
  have hphi : ContinuousOn
      (resource x.u x.eta x.B x.phiInitial) (Ici (0 : ℝ)) := by
    apply continuousOn_nonnegative_of_finite
    intro T hT
    exact resource_continuousOn x.u x.eta x.B x.phiInitial T
      (GSTStage27.bounded_control_integrable
        x.u x.U T hT x.huMeas x.hu)
  have hd : ContinuousOn (d x) (Ici (0 : ℝ)) := by
    apply continuousOn_nonnegative_of_finite
    intro T hT
    exact ((state_costates_verified x).1 T hT).continuousOn
  have hraw : ContinuousOn
      (fun t => (resource x.u x.eta x.B x.phiInitial t * d x t) /
        (2 * r)) (Ici (0 : ℝ)) := by
    simpa only [div_eq_mul_inv] using
      (hphi.mul hd).mul
        (continuousOn_const :
          ContinuousOn (fun _ : ℝ => (2 * r)⁻¹) (Ici (0 : ℝ)))
  have hext : Continuous
      (fun t => (resource x.u x.eta x.B x.phiInitial (max 0 t) *
        d x (max 0 t)) / (2 * r)) := by
    exact hraw.comp_continuous
      (continuous_const.max continuous_id)
      (fun t => by
        change (0 : ℝ) ≤ max 0 t
        exact le_max_left (0 : ℝ) t)
  exact continuous_const.max (continuous_const.min hext)

theorem clipped_control_bounds (x : StateData) (r t : ℝ) :
    0 ≤ clippedControl x r t ∧ clippedControl x r t ≤ x.U := by
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  exact GSTStage127.clipping_bounds r x.U
    (resource x.u x.eta x.B x.phiInitial (max 0 t) *
      d x (max 0 t)) hU

theorem clipped_control_eq (x : StateData) (r t : ℝ) (ht : 0 ≤ t) :
    clippedControl x r t =
      max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r))) := by
  simp only [clippedControl, max_eq_right ht]

theorem optimal_control_clipping_ae
    (x : StateData) (r : ℝ) (hr : 0 < r)
    (hoptimal : ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r x.u) :
    ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r))) := by
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  have hvMeas : Measurable (clippedControl x r) :=
    (clipped_control_continuous x r).measurable
  have hvBound : ∀ t : ℝ, 0 ≤ t →
      0 ≤ clippedControl x r t ∧ clippedControl x r t ≤ x.U :=
    fun t _ => clipped_control_bounds x r t
  have hInt : IntegrableOn
      (stationarity x r (clippedControl x r)) (Ioi (0 : ℝ)) :=
    GSTStage117.stationarity_halfline_integrable
      x r (clippedControl x r) hvMeas hvBound
  have hle :
      (∫ t in Ioi (0 : ℝ), stationarity x r (clippedControl x r) t) ≤ 0 :=
    GSTStage126.optimal_control_variational_inequality
      x r hoptimal (clippedControl x r) hvMeas hvBound
  have hnonneg :
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        0 ≤ stationarity x r (clippedControl x r) t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt (show 0 < t from ht)
    have hb := GSTStage127.clipping_stationarity_lower
      r x.U (resource x.u x.eta x.B x.phiInitial t * d x t)
      (x.u t) hr hU (x.hu t ht0).1 (x.hu t ht0).2
    dsimp only at hb
    have hp :
        0 ≤ (-2 * r * x.u t +
          resource x.u x.eta x.B x.phiInitial t * d x t) *
            (clippedControl x r t - x.u t) := by
      rw [clipped_control_eq x r t ht0]
      exact (mul_nonneg (mul_nonneg (by norm_num) hr.le)
        (sq_nonneg _)).trans hb
    exact mul_nonneg (Real.exp_pos _).le hp
  have hzero :
      (∫ t in Ioi (0 : ℝ), stationarity x r (clippedControl x r) t) = 0 :=
    le_antisymm hle (integral_nonneg_of_ae hnonneg)
  have hae :
      stationarity x r (clippedControl x r)
        =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hInt).mp hzero
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with t ht hmem
  have ht0 : 0 ≤ t := le_of_lt (show 0 < t from hmem)
  change Real.exp (-x.rho * t) *
    ((-2 * r * x.u t +
      resource x.u x.eta x.B x.phiInitial t * d x t) *
        (clippedControl x r t - x.u t)) = 0 at ht
  have hp := (mul_eq_zero.mp ht).resolve_left (ne_of_gt (Real.exp_pos _))
  rw [clipped_control_eq x r t ht0] at hp
  exact GSTStage127.eq_clipping_of_stationarity_nonpos
    r x.U (resource x.u x.eta x.B x.phiInitial t * d x t)
    (x.u t) hr hU (x.hu t ht0).1 (x.hu t ht0).2 hp.le

end GSTStage128

#print axioms GSTStage128.clipped_control_continuous
#print axioms GSTStage128.clipped_control_bounds
#print axioms GSTStage128.clipped_control_eq
#print axioms GSTStage128.optimal_control_clipping_ae
