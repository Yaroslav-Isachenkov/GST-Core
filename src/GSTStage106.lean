import GSTStage105

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage106

theorem bounded_weighted_product_integrable
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (f g p : α → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hfMeas : Measurable f) (hgMeas : Measurable g) (hpMeas : Measurable p)
    (hf : ∀ᵐ t ∂μ, ‖f t‖ ≤ U)
    (hg : ∀ᵐ t ∂μ, ‖g t‖ ≤ U)
    (hp : ∀ᵐ t ∂μ, 0 ≤ p t ∧ p t ≤ 1) :
    Integrable (fun t => p t * f t * g t) μ := by
  apply Integrable.of_bound
    ((hpMeas.mul hfMeas).mul hgMeas).aestronglyMeasurable (U ^ 2)
  filter_upwards [hf, hg, hp] with t hft hgt hpt
  have hpn : ‖p t‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpt.1] using hpt.2
  rw [norm_mul, norm_mul]
  calc
    ‖p t‖ * ‖f t‖ * ‖g t‖ ≤ (1 * U) * U :=
      mul_le_mul
        (mul_le_mul hpn hft (norm_nonneg _) zero_le_one)
        hgt (norm_nonneg _) (by positivity)
    _ = U ^ 2 := by ring

theorem bounded_weight_weak_square_lower
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (u : ℕ → α → ℝ) (a p : α → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (huMeas : ∀ n, Measurable (u n))
    (haMeas : Measurable a) (hpMeas : Measurable p)
    (huBound : ∀ n, ∀ᵐ t ∂μ, ‖u n t‖ ≤ U)
    (haBound : ∀ᵐ t ∂μ, ‖a t‖ ≤ U)
    (hp : ∀ᵐ t ∂μ, 0 ≤ p t ∧ p t ≤ 1)
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ)
    (hv : ∀ n, (v n : α → ℝ) =ᵐ[μ] u n)
    (hw : (w : α → ℝ) =ᵐ[μ] a)
    (hweak : ∀ h : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (v n) h)
        atTop (𝓝 (inner ℝ w h))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ t, p t * (a t) ^ 2 ∂μ) ≤
          (∫ t, p t * (u n t) ^ 2 ∂μ) + ε := by
  have htest : MemLp (fun t => p t * a t) 2 μ := by
    apply MemLp.of_bound (hpMeas.mul haMeas).aestronglyMeasurable U
    filter_upwards [hp, haBound] with t hpt hat
    have hpn : ‖p t‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hpt.1] using hpt.2
    rw [norm_mul]
    calc
      ‖p t‖ * ‖a t‖ ≤ 1 * U :=
        mul_le_mul hpn hat (norm_nonneg _) zero_le_one
      _ = U := one_mul U
  have hsq (f : α → ℝ) (hfMeas : Measurable f)
      (hf : ∀ᵐ t ∂μ, ‖f t‖ ≤ U) :
      Integrable (fun t => p t * (f t) ^ 2) μ := by
    have h := bounded_weighted_product_integrable
      f f p U hU hfMeas hfMeas hpMeas hf hf hp
    have he : (fun t => p t * f t * f t) =
        (fun t => p t * (f t) ^ 2) := by
      funext t
      ring
    rw [he] at h
    exact h
  apply GSTStage105.weak_weighted_square_integral_eventually_lower
    u a p v w hv hw hweak
    (hp.mono fun _ ht => ht.1) htest
    (fun n => hsq (u n) (huMeas n) (huBound n))
    (hsq a haMeas haBound)
  intro n
  exact bounded_weighted_product_integrable
    a (u n) p U hU haMeas (huMeas n) hpMeas haBound (huBound n) hp

theorem discounted_interval_control_square_lower
    (T rho U : ℝ) (hrho : 0 ≤ rho)
    (u : ℕ → ℝ → ℝ) (a : ℝ → ℝ)
    (huMeas : ∀ n, Measurable (u n)) (haMeas : Measurable a)
    (huBound : ∀ n, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ u n t ∧ u n t ≤ U)
    (haBound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ a t ∧ a t ≤ U)
    (v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)))
    (w : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hv : ∀ n, (v n : ℝ → ℝ) =ᵐ[
      volume.restrict (Icc (0 : ℝ) T)] u n)
    (hw : (w : ℝ → ℝ) =ᵐ[
      volume.restrict (Icc (0 : ℝ) T)] a)
    (hweak : ∀ h : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
      Tendsto (fun n => inner ℝ (v n) h)
        atTop (𝓝 (inner ℝ w h))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ t in Icc (0 : ℝ) T, Real.exp (-rho * t) * (a t) ^ 2) ≤
          (∫ t in Icc (0 : ℝ) T,
            Real.exp (-rho * t) * (u n t) ^ 2) + ε := by
  have hpMeas : Measurable (fun t : ℝ => Real.exp (-rho * t)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
  have hp : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ Real.exp (-rho * t) ∧ Real.exp (-rho * t) ≤ 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have hn : -rho * t ≤ 0 := by
      nlinarith [mul_nonneg hrho ht.1]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hn
  have hun : ∀ n, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      ‖u n t‖ ≤ |U| := by
    intro n
    filter_upwards [huBound n] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans (le_abs_self U)
  have han : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      ‖a t‖ ≤ |U| := by
    filter_upwards [haBound] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans (le_abs_self U)
  exact bounded_weight_weak_square_lower
    u a (fun t => Real.exp (-rho * t)) |U| (abs_nonneg U)
    huMeas haMeas hpMeas hun han hp v w hv hw hweak

end GSTStage106

#print axioms GSTStage106.bounded_weighted_product_integrable
#print axioms GSTStage106.bounded_weight_weak_square_lower
#print axioms GSTStage106.discounted_interval_control_square_lower
