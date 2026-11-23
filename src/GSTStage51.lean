import GSTStage50

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage51

theorem right_strict_decrease_of_deriv_neg
    (f : ℝ → ℝ) (v s : ℝ)
    (hf : HasDerivAt f v s) (hv : v < 0) :
    ∀ᶠ t in 𝓝[>] s, f t < f s := by
  have hslope : Tendsto (slope f s) (𝓝[>] s) (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have hnear : ∀ᶠ t in 𝓝[>] s, slope f s t < 0 :=
    hslope.eventually (Iio_mem_nhds hv)
  filter_upwards [hnear, self_mem_nhdsWithin] with t ht hst
  have hpos : 0 < t - s := sub_pos.mpr (show s < t from hst)
  have hdiv : (f t - f s) / (t - s) < 0 := by
    change (t - s)⁻¹ * (f t - f s) < 0 at ht
    simpa only [div_eq_mul_inv, mul_comm] using ht
  have hdiff := (div_lt_iff₀ hpos).mp hdiv
  linarith

-- Comparison between arbitrary nonnegative endpoints.
theorem discounted_p_interval_comparison
    (x : StateData) (s T : ℝ)
    (hq : 0 ≤ x.q) (hs : 0 ≤ s) (hsT : s ≤ T)
    (ho : ∀ t ∈ Icc s T, state x t ≤ x.target) :
    Real.exp (-(x.rho + x.a) * T) * p x T ≤
      Real.exp (-(x.rho + x.a) * s) * p x s := by
  have hT : 0 ≤ T := le_trans hs hsT
  have hsub : uIcc s T ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hsT, uIcc_of_le hT]
    intro t ht
    exact ⟨le_trans hs ht.1, ht.2⟩
  have hAC : AbsolutelyContinuousOnInterval
      (fun t => Real.exp (-(x.rho + x.a) * t) * p x t) 0 T :=
    GSTStage46.discounted_p_ac x T hT
  have hfull : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt
        (fun t => Real.exp (-(x.rho + x.a) * t) * p x t)
        (Real.exp (-(x.rho + x.a) * t) *
          (2 * x.q * (state x t - x.target))) t :=
    GSTStage46.discounted_p_derivative_ae x T hT
  have hlocal : ∀ᵐ t : ℝ, t ∈ uIcc s T →
      HasDerivAt
        (fun t => Real.exp (-(x.rho + x.a) * t) * p x t)
        (Real.exp (-(x.rho + x.a) * t) *
          (2 * x.q * (state x t - x.target))) t := by
    filter_upwards [hfull] with t ht hmem
    exact ht (hsub hmem)
  have hid := GSTStage08.ac_integral_identity
    (fun t => Real.exp (-(x.rho + x.a) * t) * p x t)
    (fun t => Real.exp (-(x.rho + x.a) * t) *
      (2 * x.q * (state x t - x.target)))
    s T (hAC.mono hsub) hlocal
  have hint :
      (∫ t in s..T,
        Real.exp (-(x.rho + x.a) * t) *
          (2 * x.q * (state x t - x.target))) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hsT]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hmem : t ∈ Icc s T := ⟨ht.1.le, ht.2⟩
    exact mul_nonpos_of_nonneg_of_nonpos
      (Real.exp_pos _).le
      (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) hq)
        (sub_nonpos.mpr (ho t hmem)))
  linarith

theorem candidate_p_positive_at_target
    (x : StateData) (r s : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (htarget : 0 < x.target) (hs : 0 < s)
    (hclip : GSTStage44.Clipping x r)
    (ho : state x s = x.target) :
    0 < p x s := by
  by_contra hnot
  have hp : p x s ≤ 0 := le_of_not_gt hnot
  have hu : x.u s = 0 :=
    GSTStage46.control_zero_of_p_nonpos x r hr hi hclip s hs.le hp
  have hder : HasDerivAt (state x) (-x.a * x.target) s := by
    have h := GSTStage47.state_ode_at x r hclip s hs
    simpa only [hu, ho, mul_zero, add_zero] using h
  have hnegative : -x.a * x.target < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos ha) htarget
  have hnear : ∀ᶠ t in 𝓝[>] s, state x t < x.target := by
    have h := right_strict_decrease_of_deriv_neg
      (state x) (-x.a * x.target) s hder hnegative
    simpa only [ho] using h
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  let T : ℝ := s + ε / 2
  have hsT : s < T := by
    dsimp [T]
    linarith
  have hT : 0 < T := lt_trans hs hsT
  have hright : ∀ t ∈ Ioc s T, state x t < x.target := by
    intro t ht
    have hball : t ∈ Metric.ball s ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1.le)]
      have htT : t ≤ s + ε / 2 := ht.2
      linarith
    exact hsub ⟨hball, ht.1⟩
  have hbelow : ∀ t ∈ Icc s T, state x t ≤ x.target := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with heq | hlt
    · simpa only [← heq] using ho.le
    · exact (hright t ⟨hlt, ht.2⟩).le
  have hpT : 0 < p x T :=
    GSTStage49.candidate_p_positive_of_state_lt_target
      x r T hr hi ha hq htarget hT hclip
      (hright T ⟨hsT, le_rfl⟩)
  have hcomparison := discounted_p_interval_comparison
    x s T hq.le hs.le hsT.le hbelow
  have hleft : 0 < Real.exp (-(x.rho + x.a) * T) * p x T :=
    mul_pos (Real.exp_pos _) hpT
  have hright_nonpos :
      Real.exp (-(x.rho + x.a) * s) * p x s ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hp
  linarith

theorem candidate_p_positive_of_state_le_target
    (x : StateData) (r s : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (htarget : 0 < x.target) (hs : 0 < s)
    (hclip : GSTStage44.Clipping x r)
    (ho : state x s ≤ x.target) :
    0 < p x s := by
  rcases lt_or_eq_of_le ho with hlt | heq
  · exact GSTStage49.candidate_p_positive_of_state_lt_target
      x r s hr hi ha hq htarget hs hclip hlt
  · exact candidate_p_positive_at_target
      x r s hr hi ha hq htarget hs hclip heq

#print axioms right_strict_decrease_of_deriv_neg
#print axioms discounted_p_interval_comparison
#print axioms candidate_p_positive_at_target
#print axioms candidate_p_positive_of_state_le_target

end GSTStage51
