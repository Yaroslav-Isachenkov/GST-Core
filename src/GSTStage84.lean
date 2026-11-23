import GSTStage83

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage84

theorem weak_L2_original_setIntegral_tendsto
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Set α) (hμs : μ s ≠ ⊤)
    (u : ℕ → α → ℝ)
    (v : ℕ → Lp ℝ 2 (μ.restrict s)) (w : Lp ℝ 2 (μ.restrict s))
    (hrep : ∀ n, (v n : α → ℝ) =ᵐ[μ.restrict s] u n)
    (hweak : ∀ g : Lp ℝ 2 (μ.restrict s),
      Tendsto (fun n => inner ℝ (v n) g) atTop (𝓝 (inner ℝ w g)))
    (r : Set α) (hr : MeasurableSet r) (hrs : r ⊆ s) :
    Tendsto (fun n => ∫ t in r, u n t ∂μ)
      atTop (𝓝 (∫ t in r, w t ∂μ)) := by
  have hfinite : (μ.restrict s) r ≠ ⊤ := by
    rw [Measure.restrict_apply hr, inter_eq_left.mpr hrs]
    exact ne_top_of_le_ne_top hμs (measure_mono hrs)
  have hl := GSTStage79.weak_L2_setIntegral_tendsto
    v w hweak r hr hfinite
  simp only [Measure.restrict_restrict hr, inter_eq_left.mpr hrs] at hl
  have he (n : ℕ) :
      (∫ t in r, v n t ∂μ) = ∫ t in r, u n t ∂μ :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hrs (hrep n))
  exact hl.congr' (Filter.Eventually.of_forall he)


theorem compatible_of_common_setIntegral_limits
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (u : ℕ → α → ℝ) (f g : α → ℝ)
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g t μ)
    (hfl : ∀ r, MeasurableSet r → r ⊆ s →
      Tendsto (fun n => ∫ z in r, u n z ∂μ)
        atTop (𝓝 (∫ z in r, f z ∂μ)))
    (hgl : ∀ r, MeasurableSet r → r ⊆ t →
      Tendsto (fun n => ∫ z in r, u n z ∂μ)
        atTop (𝓝 (∫ z in r, g z ∂μ))) :
    f =ᵐ[μ.restrict (s ∩ t)] g := by
  have hf' : Integrable f (μ.restrict (s ∩ t)) :=
    hf.mono_set inter_subset_left
  have hg' : Integrable g (μ.restrict (s ∩ t)) :=
    hg.mono_set inter_subset_right
  apply Integrable.ae_eq_of_forall_setIntegral_eq f g hf' hg'
  intro r hr _
  have hm : MeasurableSet (r ∩ (s ∩ t)) := hr.inter (hs.inter ht)
  have hsubS : r ∩ (s ∩ t) ⊆ s := fun z hz => hz.2.1
  have hsubT : r ∩ (s ∩ t) ⊆ t := fun z hz => hz.2.2
  have he := tendsto_nhds_unique
    (hfl (r ∩ (s ∩ t)) hm hsubS)
    (hgl (r ∩ (s ∩ t)) hm hsubT)
  simpa only [Measure.restrict_restrict hr] using he

#print axioms GSTStage84.weak_L2_original_setIntegral_tendsto
#print axioms GSTStage84.compatible_of_common_setIntegral_limits

end GSTStage84
