import GSTStage78
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage79

theorem weak_L2_setIntegral_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ)
    (hweak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (v n) g) atTop (𝓝 (inner ℝ w g)))
    (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) :
    Tendsto (fun n => ∫ t in s, v n t ∂μ)
      atTop (𝓝 (∫ t in s, w t ∂μ)) := by
  have heq (f : Lp ℝ 2 μ) :
      inner ℝ f (indicatorConstLp 2 hs hμs (1 : ℝ)) =
        ∫ t in s, f t ∂μ := by
    rw [real_inner_comm]
    exact L2.inner_indicatorConstLp_one hs hμs f
  simpa only [heq] using hweak (indicatorConstLp 2 hs hμs (1 : ℝ))

theorem weak_L2_preserves_bounds
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (v : ℕ → Lp ℝ 2 μ) (w : Lp ℝ 2 μ) (U : ℝ)
    (hbound : ∀ n, ∀ᵐ t ∂μ, 0 ≤ v n t ∧ v n t ≤ U)
    (hweak : ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ (v n) g) atTop (𝓝 (inner ℝ w g))) :
    ∀ᵐ t ∂μ, 0 ≤ w t ∧ w t ≤ U := by
  have hint (f : Lp ℝ 2 μ) : Integrable (fun t => f t) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (integrableOn_Lp_of_measure_ne_top (s := Set.univ)
        f (by norm_num) (by finiteness))
  have hlo : (fun _ : α => (0 : ℝ)) ≤ᵐ[μ] (fun t => w t) := by
    apply ae_le_of_forall_setIntegral_le (integrable_const 0) (hint w)
    intro s hs hμs
    have hl := weak_L2_setIntegral_tendsto v w hweak s hs hμs.ne
    have hn (n : ℕ) : 0 ≤ ∫ t in s, v n t ∂μ :=
      integral_nonneg_of_ae
        (ae_restrict_of_ae ((hbound n).mono (fun _ ht => ht.1)))
    simpa only [integral_zero] using ge_of_tendsto' hl hn
  have hhi : (fun t => w t) ≤ᵐ[μ] (fun _ : α => U) := by
    apply ae_le_of_forall_setIntegral_le (hint w) (integrable_const U)
    intro s hs hμs
    have hl := weak_L2_setIntegral_tendsto v w hweak s hs hμs.ne
    apply le_of_tendsto' hl
    intro n
    exact integral_mono_ae (hint (v n)).integrableOn
      (integrable_const U)
      (ae_restrict_of_ae ((hbound n).mono (fun _ ht => ht.2)))
  filter_upwards [hlo, hhi] with t ht0 htU
  exact ⟨ht0, htU⟩

#print axioms GSTStage79.weak_L2_setIntegral_tendsto
#print axioms GSTStage79.weak_L2_preserves_bounds

end GSTStage79
