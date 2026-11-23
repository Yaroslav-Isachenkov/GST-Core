import GSTStage115

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage32 GSTStage34

namespace GSTStage116

theorem stationarity_interval_integrable
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    IntervalIntegrable (stationarity x r u) volume 0 T := by
  have hu := GSTStage27.bounded_control_integrable
    u x.U T hT huMeas huBound
  have hv := GSTStage27.bounded_control_integrable
    x.u x.U T hT x.huMeas x.hu

  have hprodOn : IntegrableOn
      (fun t => x.u t * (u t - x.u t)) (Icc (0 : ℝ) T) := by
    apply Integrable.of_bound
      ((x.huMeas.mul (huMeas.sub x.huMeas)).aestronglyMeasurable)
      (|x.U| * |x.U|)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hb : |x.u t| ≤ |x.U| := by
      rw [abs_of_nonneg (x.hu t ht.1).1]
      exact (x.hu t ht.1).2.trans (le_abs_self x.U)
    have hd : |u t - x.u t| ≤ |x.U| :=
      (GSTStage33.abs_sub_le_common_upper (u t) (x.u t) x.U
        (huBound t ht.1).1 (huBound t ht.1).2
        (x.hu t ht.1).1 (x.hu t ht.1).2).trans (le_abs_self x.U)
    calc
      ‖x.u t * (u t - x.u t)‖ =
          |x.u t| * |u t - x.u t| := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |x.U| * |x.U| :=
        mul_le_mul hb hd (abs_nonneg _) (abs_nonneg x.U)

  have hprod : IntervalIntegrable
      (fun t => x.u t * (u t - x.u t)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hprodOn

  have hdCont : ContinuousOn (d x) (uIcc (0 : ℝ) T) :=
    ((state_costates_verified x).1 T hT).continuousOn
  have hphiCont :=
    resource_continuousOn x.u x.eta x.B x.phiInitial T hv
  have heCont : ContinuousOn
      (fun t : ℝ => Real.exp (-x.rho * t)) (uIcc (0 : ℝ) T) :=
    (continuous_const.mul continuous_id).rexp.continuousOn

  have hh : IntervalIntegrable
      (fun t => Real.exp (-x.rho * t) *
        ((-2 * r) * (x.u t * (u t - x.u t)) +
          (resource x.u x.eta x.B x.phiInitial t * d x t) *
            (u t - x.u t))) volume 0 T :=
    ((hprod.const_mul (-2 * r)).add
      ((hu.sub hv).continuousOn_mul (hphiCont.mul hdCont))).continuousOn_mul
        heCont

  have heq : stationarity x r u =
      (fun t => Real.exp (-x.rho * t) *
        ((-2 * r) * (x.u t * (u t - x.u t)) +
          (resource x.u x.eta x.B x.phiInitial t * d x t) *
            (u t - x.u t))) := by
    funext t
    dsimp only [stationarity]
    ring
  rw [heq]
  exact hh

theorem finite_cost_difference_identity
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    (∫ t in (0 : ℝ)..T, costDifference x r u t) =
      (∫ t in (0 : ℝ)..T, gap x r u t) -
      (∫ t in (0 : ℝ)..T, stationarity x r u t) -
      (∫ t in (0 : ℝ)..T, comparisonIntegrand x u t) +
      boundary x u T := by
  have hu := GSTStage27.bounded_control_integrable
    u x.U T hT huMeas huBound
  have hAC := GSTStage34.boundary_ac x u T hT hu
  have hODE := GSTStage34.boundary_derivative_ae x r u T hT hu
  obtain ⟨hc, hg, hm⟩ :=
    GSTStage34.integrands_integrable x r u T hT huMeas huBound
  have hs := stationarity_interval_integrable x r u T hT huMeas huBound
  have hFTC := GSTStage08.ac_integral_identity
    (boundary x u)
    (fun t => costDifference x r u t - gap x r u t +
      stationarity x r u t + comparisonIntegrand x u t)
    0 T hAC hODE
  rw [intervalIntegral.integral_add ((hc.sub hg).add hs) hm,
      intervalIntegral.integral_add (hc.sub hg) hs,
      intervalIntegral.integral_sub hc hg,
      GSTStage34.boundary_initial] at hFTC
  linarith

end GSTStage116

#print axioms GSTStage116.stationarity_interval_integrable
#print axioms GSTStage116.finite_cost_difference_identity
