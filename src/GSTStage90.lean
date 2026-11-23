import GSTStage89

open MeasureTheory Filter
open scoped Topology

namespace GSTStage90

theorem weak_strong_product_integral_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ)
    (h : ℕ → Lp ℝ 2 μ) (hlim : Lp ℝ 2 μ)
    (C : ℝ)
    (hbound : ∀ n, ‖v n‖ ≤ C)
    (hweak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (v n) g)
        atTop (𝓝 (inner ℝ w g)))
    (hstrong : Tendsto h atTop (𝓝 hlim)) :
    Tendsto (fun n => ∫ t, (v n t) * (h n t) ∂μ)
      atTop (𝓝 (∫ t, (w t) * (hlim t) ∂μ)) := by
  have hl := GSTStage89.weak_strong_inner_tendsto
    v w h hlim C hbound hweak hstrong
  simpa [L2.inner_def, mul_comm] using hl

theorem original_product_integral_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u phi : ℕ → α → ℝ) (a Phi : α → ℝ)
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ)
    (h : ℕ → Lp ℝ 2 μ) (hlim : Lp ℝ 2 μ)
    (C : ℝ)
    (hv : ∀ n, (v n : α → ℝ) =ᵐ[μ] u n)
    (hw : (w : α → ℝ) =ᵐ[μ] a)
    (hh : ∀ n, (h n : α → ℝ) =ᵐ[μ] phi n)
    (hhlim : (hlim : α → ℝ) =ᵐ[μ] Phi)
    (hbound : ∀ n, ‖v n‖ ≤ C)
    (hweak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (v n) g)
        atTop (𝓝 (inner ℝ w g)))
    (hstrong : Tendsto h atTop (𝓝 hlim)) :
    Tendsto (fun n => ∫ t, phi n t * u n t ∂μ)
      atTop (𝓝 (∫ t, Phi t * a t ∂μ)) := by
  have hl := weak_strong_product_integral_tendsto
    v w h hlim C hbound hweak hstrong
  have he (n : ℕ) :
      (∫ t, v n t * h n t ∂μ) =
        ∫ t, phi n t * u n t ∂μ := by
    apply integral_congr_ae
    filter_upwards [hv n, hh n] with t ht hu
    rw [ht, hu, mul_comm]
  have helim :
      (∫ t, w t * hlim t ∂μ) =
        ∫ t, Phi t * a t ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw, hhlim] with t ht hu
    rw [ht, hu, mul_comm]
  rw [helim] at hl
  exact hl.congr' (Filter.Eventually.of_forall he)

end GSTStage90

#print axioms GSTStage90.weak_strong_product_integral_tendsto
#print axioms GSTStage90.original_product_integral_tendsto
