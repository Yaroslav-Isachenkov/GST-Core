import GSTStage06
import GSTStage07
import GSTStage33

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage32

namespace GSTStage34

noncomputable def competitorState
    (x : StateData) (u : ℝ → ℝ) : ℝ → ℝ :=
  GSTStage29.omega u x.eta x.B x.phiInitial x.a x.c x.omegaInitial

noncomputable def boundary
    (x : StateData) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-x.rho * t) *
    (p x t * (competitorState x u t - state x t) +
      z x t * (resource u x.eta x.B x.phiInitial t -
        resource x.u x.eta x.B x.phiInitial t))

noncomputable def costDifference
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-x.rho * t) *
    (GSTStage06.runningCost x.q r x.target (competitorState x u t) (u t) -
      GSTStage06.runningCost x.q r x.target (state x t) (x.u t))

noncomputable def gap
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-x.rho * t) *
    (x.q * (competitorState x u t - state x t)^2 +
      r * (u t - x.u t)^2)

noncomputable def stationarity
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-x.rho * t) *
    ((-2 * r * x.u t +
      resource x.u x.eta x.B x.phiInitial t * d x t) *
      (u t - x.u t))

theorem bounded_square_integrable
    (f : ℝ → ℝ) (M T : ℝ)
    (hT : 0 ≤ T) (hf : Measurable f)
    (hb : ∀ t ∈ Icc (0 : ℝ) T, |f t| ≤ M) :
    IntervalIntegrable (fun t => (f t)^2) volume 0 T := by
  have hconst : IntervalIntegrable
      (fun _ : ℝ => M^2) volume 0 T := intervalIntegrable_const
  apply hconst.mono_fun' (hf.pow_const 2).aestronglyMeasurable
  rw [uIoc_of_le hT]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hbt := hb t ⟨le_of_lt ht.1, ht.2⟩
  have hM : 0 ≤ M := le_trans (abs_nonneg _) hbt
  have hn := mul_nonneg
    (sub_nonneg.mpr hbt) (add_nonneg hM (abs_nonneg (f t)))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f t))]
  nlinarith [sq_abs (f t)]

theorem integrands_integrable
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    IntervalIntegrable (costDifference x r u) volume 0 T ∧
    IntervalIntegrable (gap x r u) volume 0 T ∧
    IntervalIntegrable (comparisonIntegrand x u) volume 0 T := by
  have hu := GSTStage27.bounded_control_integrable
    u x.U T hT huMeas huBound
  have hv := GSTStage27.bounded_control_integrable
    x.u x.U T hT x.huMeas x.hu
  have ho : ContinuousOn (competitorState x u) (uIcc (0 : ℝ) T) :=
    (GSTStage29.omega_solution
      u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hu).1.continuousOn
  have hoc : ContinuousOn (state x) (uIcc (0 : ℝ) T) :=
    (GSTStage29.omega_solution
      x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hv).1.continuousOn
  have he : ContinuousOn
      (fun t : ℝ => Real.exp (-x.rho * t)) (uIcc (0 : ℝ) T) :=
    (continuous_const.mul continuous_id).rexp.continuousOn

  have hu2 := bounded_square_integrable u x.U T hT huMeas
    (by
      intro t ht
      rw [abs_of_nonneg (huBound t ht.1).1]
      exact (huBound t ht.1).2)
  have hv2 := bounded_square_integrable x.u x.U T hT x.huMeas
    (by
      intro t ht
      rw [abs_of_nonneg (x.hu t ht.1).1]
      exact (x.hu t ht.1).2)
  have hdu2 := bounded_square_integrable
    (fun t => u t - x.u t) x.U T hT (huMeas.sub x.huMeas)
    (by
      intro t ht
      exact GSTStage33.abs_sub_le_common_upper (u t) (x.u t) x.U
        (huBound t ht.1).1 (huBound t ht.1).2
        (x.hu t ht.1).1 (x.hu t ht.1).2)

  have hcu : IntervalIntegrable
      (fun t => GSTStage06.runningCost x.q r x.target
        (competitorState x u t) (u t)) volume 0 T :=
    (((ho.sub continuousOn_const).pow 2).intervalIntegrable.const_mul x.q).add (hu2.const_mul r)
  have hcv : IntervalIntegrable
      (fun t => GSTStage06.runningCost x.q r x.target
        (state x t) (x.u t)) volume 0 T :=
    (((hoc.sub continuousOn_const).pow 2).intervalIntegrable.const_mul x.q).add (hv2.const_mul r)
  have hg : IntervalIntegrable
      (fun t => x.q * (competitorState x u t - state x t)^2 +
        r * (u t - x.u t)^2) volume 0 T :=
    (((ho.sub hoc).pow 2).intervalIntegrable.const_mul x.q).add (hdu2.const_mul r)

  have hd : ContinuousOn (d x) (uIcc (0 : ℝ) T) :=
    ((state_costates_verified x).1 T hT).continuousOn
  have hphi := resource_continuousOn u x.eta x.B x.phiInitial T hu
  have hpsi := resource_continuousOn x.u x.eta x.B x.phiInitial T hv
  have hcoef := (he.mul hd).mul (hphi.sub hpsi)

  exact ⟨
    (hcu.sub hcv).continuousOn_mul he,
    hg.continuousOn_mul he,
    (hu.sub hv).continuousOn_mul hcoef
  ⟩

theorem boundary_ac
    (x : StateData) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (hu : IntervalIntegrable u volume 0 T) :
    AbsolutelyContinuousOnInterval (boundary x u) 0 T := by
  have hv := GSTStage27.bounded_control_integrable
    x.u x.U T hT x.huMeas x.hu
  have ho := (GSTStage29.omega_solution
    u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hu).1
  have hoc := (GSTStage29.omega_solution
    x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hv).1
  have hf := GSTStage12.resource_ac u x.eta x.B x.phiInitial T hu
  have hfc := GSTStage12.resource_ac x.u x.eta x.B x.phiInitial T hv
  have hp := (GSTStage28.p_solution (toCostateData x) T hT).1
  have hz := (GSTStage28.z_solution (toCostateData x) T hT).1
  exact (GSTStage30.linear_exponential_ac (-x.rho) T).mul
    ((hp.mul (ho.fun_sub hoc)).fun_add (hz.mul (hf.fun_sub hfc)))

theorem boundary_initial
    (x : StateData) (u : ℝ → ℝ) :
    boundary x u 0 = 0 := by
  simp [boundary, competitorState, state,
    GSTStage29.omega_initial, resource_initial]

theorem boundary_derivative_ae
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T)
    (hu : IntervalIntegrable u volume 0 T) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (boundary x u)
        (costDifference x r u t - gap x r u t +
          stationarity x r u t + comparisonIntegrand x u t) t := by
  have hv := GSTStage27.bounded_control_integrable
    x.u x.U T hT x.huMeas x.hu
  have ho := (GSTStage29.omega_solution
    u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hu).2
  have hoc := (GSTStage29.omega_solution
    x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T hv).2
  have hf := GSTStage12.resource_ode_ae u x.eta x.B x.phiInitial T hu
  have hfc := GSTStage12.resource_ode_ae x.u x.eta x.B x.phiInitial T hv
  have hp := (GSTStage28.p_solution (toCostateData x) T hT).2
  have hz := (GSTStage28.z_solution (toCostateData x) T hT).2

  filter_upwards [ho, hoc, hf, hfc, hp, hz] with t hot hoct hft hfct hpt hzt
  intro ht

  have hf' : HasDerivAt (resource u x.eta x.B x.phiInitial)
      (x.B - x.eta * resource u x.eta x.B x.phiInitial t * u t) t := by
    convert hft ht using 1
    ring
  have hfc' : HasDerivAt (resource x.u x.eta x.B x.phiInitial)
      (x.B - x.eta * resource x.u x.eta x.B x.phiInitial t * x.u t) t := by
    convert hfct ht using 1
    ring

  have h := GSTStage06.objective_boundary_identity
    (competitorState x u) (state x)
    (resource u x.eta x.B x.phiInitial)
    (resource x.u x.eta x.B x.phiInitial)
    (p x) (z x)
    t x.a x.c x.eta x.B x.rho x.q r x.target (u t) (x.u t)
    (by simpa only [mul_assoc] using hot ht)
    (by simpa only [mul_assoc] using hoct ht)
    hf' hfc' (hpt ht) (hzt ht)

  convert h using 1
  dsimp only [costDifference, gap, stationarity, comparisonIntegrand,
    GSTStage16.mixed, d, GSTStage18.canonicalD]
  ring

theorem stationarity_nonpos
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (t : ℝ)
    (hr : 0 < r) (hU : 0 < x.U) (ht : 0 ≤ t)
    (huBound : ∀ s : ℝ, 0 ≤ s → 0 ≤ u s ∧ u s ≤ x.U)
    (hclip : ∀ s : ℝ, 0 ≤ s →
      x.u s = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial s * d x s) / (2 * r)))) :
    stationarity x r u t ≤ 0 := by
  have h := GSTStage07.clipping_variational_sign
    r x.U (resource x.u x.eta x.B x.phiInitial t * d x t) (u t)
    hr hU (huBound t ht).1 (huBound t ht).2
  dsimp only at h
  rw [← hclip t ht] at h
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) h

theorem finite_cost_gap
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hr : 0 < r) (hU : 0 < x.U)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U)
    (hclip : ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r)))) :
    (∫ t in (0 : ℝ)..T, gap x r u t) + boundary x u T ≤
      ∫ t in (0 : ℝ)..T, costDifference x r u t := by
  have hu := GSTStage27.bounded_control_integrable
    u x.U T hT huMeas huBound
  have hAC := boundary_ac x u T hT hu
  have hODE := boundary_derivative_ae x r u T hT hu
  obtain ⟨hcost, hgap, hmix⟩ :=
    integrands_integrable x r u T hT huMeas huBound

  have hle : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (boundary x u) t ≤
        costDifference x r u t - gap x r u t + comparisonIntegrand x u t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hODE] with t hd ht
    have ht' : t ∈ uIcc (0 : ℝ) T := by
      rw [uIcc_of_le hT]
      exact ht
    rw [(hd ht').deriv]
    have hs := stationarity_nonpos x r u t hr hU ht.1 huBound hclip
    linarith

  have hi := intervalIntegral.integral_mono_ae_restrict
    hT hAC.intervalIntegrable_deriv ((hcost.sub hgap).add hmix) hle
  rw [hAC.integral_deriv_eq_sub,
    intervalIntegral.integral_add (hcost.sub hgap) hmix,
    intervalIntegral.integral_sub hcost hgap,
    boundary_initial] at hi
  have hm := GSTStage32.state_finite_mixed_nonpos
    x u T hT hphiInitial hS hu
  linarith

#print axioms bounded_square_integrable
#print axioms integrands_integrable
#print axioms boundary_ac
#print axioms boundary_initial
#print axioms boundary_derivative_ae
#print axioms stationarity_nonpos
#print axioms finite_cost_gap

end GSTStage34
