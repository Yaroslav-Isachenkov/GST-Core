import GSTStage103

open MeasureTheory Filter
open scoped Topology

namespace GSTStage104

theorem weak_norm_sq_eventually_lower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E) (w : E)
    (hweak : ∀ h : E,
      Tendsto (fun n => inner ℝ (v n) h)
        atTop (𝓝 (inner ℝ w h))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ‖w‖ ^ 2 ≤ ‖v n‖ ^ 2 + ε := by
  intro ε hε
  have hl : Tendsto (fun n => inner ℝ (v n) w)
      atTop (𝓝 (‖w‖ ^ 2)) := by
    simpa only [real_inner_self_eq_norm_sq] using hweak w
  have he : ∀ᶠ n in atTop,
      ‖w‖ ^ 2 - ε / 2 < inner ℝ (v n) w :=
    (tendsto_order.1 hl).1 (‖w‖ ^ 2 - ε / 2) (by linarith)
  filter_upwards [he] with n hn
  have hi : inner ℝ (v n) w ≤ ‖v n‖ * ‖w‖ :=
    le_trans (le_abs_self _) (abs_real_inner_le_norm (v n) w)
  nlinarith [sq_nonneg (‖v n‖ - ‖w‖)]

theorem weak_L2_square_integral_eventually_lower
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℕ → α → ℝ) (a : α → ℝ)
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ)
    (hv : ∀ n, (v n : α → ℝ) =ᵐ[μ] u n)
    (hw : (w : α → ℝ) =ᵐ[μ] a)
    (hweak : ∀ h : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (v n) h)
        atTop (𝓝 (inner ℝ w h))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ t, (a t) ^ 2 ∂μ) ≤ (∫ t, (u n t) ^ 2 ∂μ) + ε := by
  have hnorm (z : Lp ℝ 2 μ) :
      ‖z‖ ^ 2 = ∫ t, (z t) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq z, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with t
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

  have hvIntegral (n : ℕ) :
      ‖v n‖ ^ 2 = ∫ t, (u n t) ^ 2 ∂μ := by
    rw [hnorm]
    apply integral_congr_ae
    filter_upwards [hv n] with t ht
    rw [ht]

  have hwIntegral : ‖w‖ ^ 2 = ∫ t, (a t) ^ 2 ∂μ := by
    rw [hnorm]
    apply integral_congr_ae
    filter_upwards [hw] with t ht
    rw [ht]

  intro ε hε
  have he := weak_norm_sq_eventually_lower v w hweak ε hε
  filter_upwards [he] with n hn
  simpa only [hwIntegral, hvIntegral] using hn

end GSTStage104

#print axioms GSTStage104.weak_norm_sq_eventually_lower
#print axioms GSTStage104.weak_L2_square_integral_eventually_lower
