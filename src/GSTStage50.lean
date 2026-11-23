import GSTStage49

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage50

theorem state_initial (x : StateData) :
    state x 0 = x.omegaInitial := by
  simp [state, GSTStage29.omega, GSTStage29.linearState]

-- Right continuity at zero provides a whole finite interval.
theorem state_below_target_near_initial
    (x : StateData) (ho : x.omegaInitial < x.target) :
    ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Icc (0 : ℝ) T, state x t < x.target := by
  have hzero : state x 0 < x.target := by
    rw [state_initial]
    exact ho
  have hc : ContinuousWithinAt (state x) (Ici (0 : ℝ)) 0 :=
    state_continuousOn x 0 (show (0 : ℝ) ≤ 0 from le_rfl)
  have hnear :
      {t : ℝ | state x t < x.target} ∈ 𝓝[Ici (0 : ℝ)] (0 : ℝ) :=
    hc (Iio_mem_nhds hzero)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  refine ⟨ε / 2, by linarith, ?_⟩
  intro t ht
  have hball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  exact hsub ⟨hball, ht.1⟩

-- Only the nonpositive sign of the integral is needed.
theorem discounted_p_le_initial_of_state_le_target
    (x : StateData) (T : ℝ)
    (hq : 0 ≤ x.q) (hT : 0 ≤ T)
    (ho : ∀ t ∈ Icc (0 : ℝ) T, state x t ≤ x.target) :
    Real.exp (-(x.rho + x.a) * T) * p x T ≤ p x 0 := by
  have hint :
      (∫ t in (0 : ℝ)..T,
        Real.exp (-(x.rho + x.a) * t) *
          (2 * x.q * (state x t - x.target))) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hT]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hmem : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
    exact mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_pos _).le
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) hq)
        (sub_nonpos.mpr (ho t hmem)))
  have hid := GSTStage46.discounted_p_integral_identity x T hT
  change
    (∫ t in (0 : ℝ)..T,
      Real.exp (-(x.rho + x.a) * t) *
        (2 * x.q * (state x t - x.target))) =
      Real.exp (-(x.rho + x.a) * T) * p x T - p x 0 at hid
  linarith

theorem candidate_p_initial_positive
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : x.omegaInitial < x.target)
    (hclip : GSTStage44.Clipping x r) :
    0 < p x 0 := by
  have htarget : 0 < x.target :=
    lt_of_le_of_lt x.homegaInitial ho
  obtain ⟨T, hT, hbelow⟩ := state_below_target_near_initial x ho
  have hpT : 0 < p x T :=
    GSTStage49.candidate_p_positive_of_state_lt_target
      x r T hr hi ha hq htarget hT hclip
      (hbelow T ⟨hT.le, le_rfl⟩)
  have hcomparison := discounted_p_le_initial_of_state_le_target
    x T hq.le hT.le (fun t ht => (hbelow t ht).le)
  exact lt_of_lt_of_le (mul_pos (Real.exp_pos _) hpT) hcomparison

#print axioms state_initial
#print axioms state_below_target_near_initial
#print axioms discounted_p_le_initial_of_state_le_target
#print axioms candidate_p_initial_positive

end GSTStage50
