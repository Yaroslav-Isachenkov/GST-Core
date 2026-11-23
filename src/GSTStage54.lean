import GSTStage53

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31

namespace GSTStage54

-- This discount is rho, not rho + a.
noncomputable def discountedP (x : StateData) (t : ℝ) : ℝ :=
  Real.exp (-x.rho * t) * p x t

theorem discounted_p_ac
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (discountedP x) 0 T := by
  exact (GSTStage30.linear_exponential_ac (-x.rho) T).mul
    (GSTStage28.p_solution (toCostateData x) T hT).1

theorem discounted_p_derivative_ae
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (discountedP x)
        (Real.exp (-x.rho * t) * S x t) t := by
  have hpFull : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (p x)
        ((x.rho + x.a) * p x t +
          2 * x.q * (state x t - x.target)) t :=
    (GSTStage28.p_solution (toCostateData x) T hT).2
  filter_upwards [hpFull] with t hp ht
  have he := ((hasDerivAt_id t).const_mul (-x.rho)).exp
  convert he.mul (hp ht) using 1
  dsimp [discountedP, GSTStage31.S, GSTStage18.canonicalS]
  ring

theorem discounted_p_integral_identity
    (x : StateData) (s T : ℝ)
    (hs : 0 ≤ s) (hsT : s ≤ T) :
    (∫ t in s..T, Real.exp (-x.rho * t) * S x t) =
      discountedP x T - discountedP x s := by
  have hT : 0 ≤ T := le_trans hs hsT
  have hsub : uIcc s T ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hsT, uIcc_of_le hT]
    intro t ht
    exact ⟨le_trans hs ht.1, ht.2⟩
  have hlocal : ∀ᵐ t : ℝ, t ∈ uIcc s T →
      HasDerivAt (discountedP x)
        (Real.exp (-x.rho * t) * S x t) t := by
    filter_upwards [discounted_p_derivative_ae x T hT] with t ht hmem
    exact ht (hsub hmem)
  exact GSTStage08.ac_integral_identity
    (discountedP x) (fun t => Real.exp (-x.rho * t) * S x t)
    s T ((discounted_p_ac x T hT).mono hsub) hlocal

theorem discounted_p_terminal_comparison
    (x : StateData) (s T : ℝ)
    (hs : 0 ≤ s) (hsT : s ≤ T)
    (hS : ∀ t ∈ Icc s T, 0 ≤ S x t) :
    discountedP x s ≤ discountedP x T := by
  have hint : 0 ≤ ∫ t in s..T, Real.exp (-x.rho * t) * S x t := by
    apply intervalIntegral.integral_nonneg hsT
    intro t ht
    exact mul_nonneg (Real.exp_pos _).le (hS t ht)
  have hid := discounted_p_integral_identity x s T hs hsT
  linarith

theorem discounted_p_tendsto_zero
    (x : StateData) :
    Tendsto (discountedP x) atTop (𝓝 0) := by
  obtain ⟨P, _hP, hp⟩ := GSTStage35.p_linear_growth x
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ?_
    (GSTStage20.discounted_polynomial_tendsto_zero x.rho P 1 x.hrho)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change ‖Real.exp (-x.rho * t) * p x t‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-x.rho * t) * |p x t|
        ≤ Real.exp (-x.rho * t) * (P * (1 + t)) :=
      mul_le_mul_of_nonneg_left (hp t ht) (Real.exp_pos _).le
    _ = P * (Real.exp (-x.rho * t) +
        t ^ (1 : ℕ) * Real.exp (-x.rho * t)) := by ring

-- S cannot remain strictly positive on an infinite future tail.
theorem candidate_s_nonpos_later
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : x.omegaInitial < x.target)
    (hclip : GSTStage44.Clipping x r) :
    ∀ s : ℝ, 0 ≤ s → ∃ T : ℝ, s < T ∧ S x T ≤ 0 := by
  intro s hs
  by_contra hnot
  have hpositive : ∀ T : ℝ, s < T → 0 < S x T := by
    intro T hsT
    by_contra hn
    exact hnot ⟨T, hsT, le_of_not_gt hn⟩
  let b : ℝ := s + 1
  have hsb : s < b := by
    dsimp [b]
    linarith
  have hb : 0 ≤ b := le_trans hs hsb.le
  have hp : 0 < p x b :=
    GSTStage52.candidate_p_positive x r hr hi ha hq ho hclip b hb
  have hdpositive : 0 < discountedP x b :=
    mul_pos (Real.exp_pos _) hp
  have hevent : ∀ᶠ T : ℝ in atTop,
      discountedP x b ≤ discountedP x T := by
    filter_upwards [eventually_ge_atTop b] with T hbT
    apply discounted_p_terminal_comparison x b T hb hbT
    intro t ht
    exact (hpositive t (lt_of_lt_of_le hsb ht.1)).le
  have hnonpos : discountedP x b ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (discounted_p_tendsto_zero x) hevent
  exact (not_lt_of_ge hnonpos) hdpositive

#print axioms discounted_p_ac
#print axioms discounted_p_derivative_ae
#print axioms discounted_p_integral_identity
#print axioms discounted_p_terminal_comparison
#print axioms discounted_p_tendsto_zero
#print axioms candidate_s_nonpos_later

end GSTStage54
