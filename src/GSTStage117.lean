import GSTStage116

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage32 GSTStage34 GSTStage37

namespace GSTStage117

theorem stationarity_halfline_integrable
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    IntegrableOn (stationarity x r u) (Ioi (0 : ℝ)) := by
  have hdCont : ContinuousOn (d x) (Ici (0 : ℝ)) := by
    apply continuousOn_nonnegative_of_finite
    intro T hT
    exact ((state_costates_verified x).1 T hT).continuousOn
  have hdCont' : ContinuousOn (d x) (Ioi (0 : ℝ)) := by
    apply hdCont.mono
    intro t ht
    change (0 : ℝ) < t at ht
    exact ht.le

  have hdMeas : AEStronglyMeasurable (d x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hdCont'.aestronglyMeasurable measurableSet_Ioi
  have hphiMeas : AEStronglyMeasurable
      (resource x.u x.eta x.B x.phiInitial)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (resource_measurable x.u x.eta x.B x.phiInitial
      x.huMeas).aestronglyMeasurable
  have hbaseMeas : AEStronglyMeasurable
      (fun t => -2 * r * x.u t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (measurable_const.mul x.huMeas).aestronglyMeasurable
  have hduMeas : AEStronglyMeasurable (fun t => u t - x.u t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (huMeas.sub x.huMeas).aestronglyMeasurable
  have heMeas : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-x.rho * t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((continuous_const.mul continuous_id).rexp.measurable).aestronglyMeasurable
  have hsMeas : AEStronglyMeasurable (stationarity x r u)
      (volume.restrict (Ioi (0 : ℝ))) :=
    heMeas.mul ((hbaseMeas.add (hphiMeas.mul hdMeas)).mul hduMeas)

  obtain ⟨D, hD, hd⟩ := (state_costates_verified x).2.2.1
  let R : ℝ := x.phiInitial + x.B
  have hR : 0 ≤ R := add_nonneg x.hphiInitial x.hB
  have hU : 0 ≤ x.U :=
    le_trans (x.hu 0 le_rfl).1 (x.hu 0 le_rfl).2
  let A : ℝ := 2 * |r| * x.U
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg r)) hU
  let K : ℝ := R * D
  have hK : 0 ≤ K := mul_nonneg hR hD

  apply GSTStage04.dominated_integrable
    (stationarity x r u) x.rho ((A + 2 * K) * x.U) 2
    x.hrho hsMeas
  intro t ht
  have ht0 : 0 ≤ t := ht.le
  have htime : 0 ≤ 1 + t := by linarith

  have hphi : |resource x.u x.eta x.B x.phiInitial t| ≤ R * (1 + t) := by
    rw [abs_of_nonneg (GSTStage30.resource_nonneg
      x.u x.eta x.B x.phiInitial t x.hB x.hphiInitial ht0)]
    have hb := GSTStage33.resource_upper
      x.u x.eta x.B x.phiInitial x.U t ht0 x.heta.le
      x.hB x.hphiInitial x.huMeas x.hu
    dsimp only [R]
    nlinarith [x.hB, mul_nonneg x.hphiInitial ht0]

  have hdu : |u t - x.u t| ≤ x.U :=
    GSTStage33.abs_sub_le_common_upper (u t) (x.u t) x.U
      (huBound t ht0).1 (huBound t ht0).2
      (x.hu t ht0).1 (x.hu t ht0).2
  have hv : |x.u t| ≤ x.U := by
    rw [abs_of_nonneg (x.hu t ht0).1]
    exact (x.hu t ht0).2

  have hfirst : |-2 * r * x.u t| ≤ A := by
    calc
      |-2 * r * x.u t| = (2 * |r|) * |x.u t| := by
        simp only [abs_mul]
        norm_num
      _ ≤ (2 * |r|) * x.U :=
        mul_le_mul_of_nonneg_left hv
          (mul_nonneg (by norm_num) (abs_nonneg r))

  have hsecond :
      |resource x.u x.eta x.B x.phiInitial t * d x t| ≤ K * (1 + t)^2 := by
    rw [abs_mul]
    calc
      |resource x.u x.eta x.B x.phiInitial t| * |d x t|
          ≤ (R * (1 + t)) * (D * (1 + t)) :=
        mul_le_mul hphi (hd t ht0) (abs_nonneg _)
          (mul_nonneg hR htime)
      _ = K * (1 + t)^2 := by dsimp only [K]; ring

  have hcoef :
      |-2 * r * x.u t +
        resource x.u x.eta x.B x.phiInitial t * d x t|
        ≤ A + K * (1 + t)^2 :=
    (abs_add_le _ _).trans (add_le_add hfirst hsecond)

  have hpoly : A + K * (1 + t)^2 ≤ (A + 2 * K) * (1 + t^2) := by
    have hp : (1 + t)^2 ≤ 2 * (1 + t^2) := by
      nlinarith [sq_nonneg (t - 1)]
    have hpK := mul_le_mul_of_nonneg_left hp hK
    nlinarith [mul_nonneg hA (sq_nonneg t)]

  have hcoef' := hcoef.trans hpoly
  have hright : 0 ≤ (A + 2 * K) * (1 + t^2) :=
    mul_nonneg (add_nonneg hA (mul_nonneg (by norm_num) hK))
      (by nlinarith [sq_nonneg t])
  have hprod :
      |-2 * r * x.u t +
        resource x.u x.eta x.B x.phiInitial t * d x t| *
        |u t - x.u t| ≤
      ((A + 2 * K) * (1 + t^2)) * x.U :=
    mul_le_mul hcoef' hdu (abs_nonneg _) hright
  have he : 0 ≤ Real.exp (-x.rho * t) := (Real.exp_pos _).le
  change |Real.exp (-x.rho * t) *
    ((-2 * r * x.u t +
      resource x.u x.eta x.B x.phiInitial t * d x t) *
      (u t - x.u t))| ≤ _
  rw [abs_mul, abs_of_nonneg he, abs_mul]
  calc
    Real.exp (-x.rho * t) *
        (|-2 * r * x.u t +
          resource x.u x.eta x.B x.phiInitial t * d x t| *
          |u t - x.u t|)
        ≤ Real.exp (-x.rho * t) *
          (((A + 2 * K) * (1 + t^2)) * x.U) :=
      mul_le_mul_of_nonneg_left hprod he
    _ = ((A + 2 * K) * x.U) * (1 + t^2) *
        Real.exp (-x.rho * t) := by ring

theorem objective_difference_identity
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    objective x r u - objective x r x.u =
      (∫ t in Ioi (0 : ℝ), stationarity x r u t) +
      (∫ t in Ioi (0 : ℝ), comparisonIntegrand x u t) -
      (∫ t in Ioi (0 : ℝ), gap x r u t) := by
  have hs := stationarity_halfline_integrable x r u huMeas huBound
  have hsConv :
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, stationarity x r u t)
        atTop (𝓝 (∫ t in Ioi (0 : ℝ), stationarity x r u t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hs tendsto_id
  have hconv := GSTStage36.partial_integrals_converge x r u huMeas huBound
  have hm := GSTStage33.mixed_integrable_and_limit x u huMeas huBound
  have hb := GSTStage35.boundary_tendsto_zero x u huMeas huBound
  have hrhs := (((hconv.2.1).sub hsConv).sub hm.2).add hb
  have he :
      (fun T : ℝ =>
        (∫ t in (0 : ℝ)..T, gap x r u t) -
        (∫ t in (0 : ℝ)..T, stationarity x r u t) -
        (∫ t in (0 : ℝ)..T, comparisonIntegrand x u t) +
        boundary x u T)
      =ᶠ[atTop]
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, costDifference x r u t) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (GSTStage116.finite_cost_difference_identity
      x r u T hT huMeas huBound).symm
  have hlim := tendsto_nhds_unique hconv.2.2 (hrhs.congr' he)
  have hcost := GSTStage37.cost_difference_integral_eq_objective_gap
    x r u huMeas huBound
  linarith

end GSTStage117

#print axioms GSTStage117.stationarity_halfline_integrable
#print axioms GSTStage117.objective_difference_identity
