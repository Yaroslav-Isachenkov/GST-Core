import GSTStage104

open MeasureTheory Filter
open scoped Topology

namespace GSTStage105

theorem weighted_square_lower_of_cross_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℕ → α → ℝ) (a p : α → ℝ)
    (hp : ∀ᵐ t ∂μ, 0 ≤ p t)
    (huInt : ∀ n, Integrable (fun t => p t * (u n t) ^ 2) μ)
    (haInt : Integrable (fun t => p t * (a t) ^ 2) μ)
    (hcrossInt : ∀ n, Integrable (fun t => p t * a t * u n t) μ)
    (hcross : Tendsto (fun n => ∫ t, p t * a t * u n t ∂μ)
      atTop (𝓝 (∫ t, p t * (a t) ^ 2 ∂μ))) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ t, p t * (a t) ^ 2 ∂μ) ≤
          (∫ t, p t * (u n t) ^ 2 ∂μ) + ε := by
  intro ε hε
  have he : ∀ᶠ n in atTop,
      (∫ t, p t * (a t) ^ 2 ∂μ) - ε / 2 <
        ∫ t, p t * a t * u n t ∂μ :=
    (tendsto_order.1 hcross).1
      ((∫ t, p t * (a t) ^ 2 ∂μ) - ε / 2) (by linarith)
  filter_upwards [he] with n hn
  have hpoint : ∀ᵐ t ∂μ,
      2 * (p t * a t * u n t) - p t * (a t) ^ 2 ≤
        p t * (u n t) ^ 2 := by
    filter_upwards [hp] with t ht
    nlinarith [mul_nonneg ht (sq_nonneg (u n t - a t))]
  have hi := integral_mono_ae
    (((hcrossInt n).const_mul 2).sub haInt) (huInt n) hpoint
  change (∫ t, 2 * (p t * a t * u n t) - p t * (a t) ^ 2 ∂μ) ≤
    (∫ t, p t * (u n t) ^ 2 ∂μ) at hi
  rw [integral_sub ((hcrossInt n).const_mul 2) haInt,
    integral_const_mul] at hi
  linarith

theorem weak_weighted_square_integral_eventually_lower
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : ℕ → α → ℝ) (a p : α → ℝ)
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ)
    (hv : ∀ n, (v n : α → ℝ) =ᵐ[μ] u n)
    (hw : (w : α → ℝ) =ᵐ[μ] a)
    (hweak : ∀ h : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (v n) h)
        atTop (𝓝 (inner ℝ w h)))
    (hp : ∀ᵐ t ∂μ, 0 ≤ p t)
    (htest : MemLp (fun t => p t * a t) 2 μ)
    (huInt : ∀ n, Integrable (fun t => p t * (u n t) ^ 2) μ)
    (haInt : Integrable (fun t => p t * (a t) ^ 2) μ)
    (hcrossInt : ∀ n, Integrable (fun t => p t * a t * u n t) μ) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop,
        (∫ t, p t * (a t) ^ 2 ∂μ) ≤
          (∫ t, p t * (u n t) ^ 2 ∂μ) + ε := by
  let h : Lp ℝ 2 μ := htest.toLp (fun t => p t * a t)
  have hh : (h : α → ℝ) =ᵐ[μ] (fun t => p t * a t) :=
    htest.coeFn_toLp
  have hl :
      Tendsto (fun n => ∫ t, v n t * h t ∂μ)
        atTop (𝓝 (∫ t, w t * h t ∂μ)) := by
    simpa [L2.inner_def, mul_comm] using hweak h
  have hn (n : ℕ) :
      (∫ t, v n t * h t ∂μ) =
        ∫ t, p t * a t * u n t ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv n, hh] with t ht ht'
    rw [ht, ht']
    ring
  have hw' :
      (∫ t, w t * h t ∂μ) = ∫ t, p t * (a t) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw, hh] with t ht ht'
    rw [ht, ht']
    ring
  rw [hw'] at hl
  have hcross :
      Tendsto (fun n => ∫ t, p t * a t * u n t ∂μ)
        atTop (𝓝 (∫ t, p t * (a t) ^ 2 ∂μ)) :=
    hl.congr' (Filter.Eventually.of_forall hn)
  exact weighted_square_lower_of_cross_tendsto
    u a p hp huInt haInt hcrossInt hcross

end GSTStage105

#print axioms GSTStage105.weighted_square_lower_of_cross_tendsto
#print axioms GSTStage105.weak_weighted_square_integral_eventually_lower
