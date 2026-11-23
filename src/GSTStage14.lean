import GSTStage13

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage12 GSTStage13

namespace GSTStage14

-- Bounds are required only almost everywhere on the finite interval.
theorem admissible_control_integrable
    (u : ℝ → ℝ) (U T : ℝ)
    (hT : 0 ≤ T)
    (hmeas : Measurable u)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ u t ∧ u t ≤ U) :
    IntervalIntegrable u volume 0 T := by
  have hconst : IntervalIntegrable
      (fun _ : ℝ => U) volume 0 T := intervalIntegrable_const
  apply hconst.mono_fun' hmeas.aestronglyMeasurable
  rw [uIoc_of_le hT]
  have hb : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      0 ≤ u t ∧ u t ≤ U :=
    hbound.filter_mono
      (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  filter_upwards [hb] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2

-- Existence and uniqueness ON [0,T], not uniqueness of extensions
-- outside the interval.
theorem admissible_resource_exists_unique_on
    (u : ℝ → ℝ) (eta B initial U T : ℝ)
    (hT : 0 ≤ T) (hB : 0 ≤ B) (hi : 0 < initial)
    (hmeas : Measurable u)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ u t ∧ u t ≤ U) :
    ∃ f : ℝ → ℝ,
      f 0 = initial ∧
      AbsolutelyContinuousOnInterval f 0 T ∧
      (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt f (B - eta * u t * f t) t) ∧
      (∀ t ∈ Icc (0 : ℝ) T, 0 < f t) ∧
      (∀ g : ℝ → ℝ,
        g 0 = initial →
        AbsolutelyContinuousOnInterval g 0 T →
        (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
          HasDerivAt g (B - eta * u t * g t) t) →
        EqOn g f (Icc (0 : ℝ) T)) := by
  have hu := admissible_control_integrable u U T hT hmeas hbound
  refine ⟨resource u eta B initial,
    resource_initial u eta B initial,
    resource_ac u eta B initial T hu,
    resource_ode_ae u eta B initial T hu, ?_, ?_⟩
  · intro t ht
    exact resource_positive u eta B initial t hB hi ht.1
  · intro g hg0 hg hgode
    exact resource_representation
      u g eta B initial T hT hu hg hgode hg0

theorem admissible_resource_lower_bound
    (u f : ℝ → ℝ) (eta B initial U T : ℝ)
    (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (hB : 0 ≤ B) (hi : 0 ≤ initial)
    (hmeas : Measurable u)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ u t ∧ u t ≤ U)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hfode : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt f (B - eta * u t * f t) t)
    (hinitial : f 0 = initial) :
    initial * Real.exp (-(eta * U * T)) ≤ f T := by
  have hu := admissible_control_integrable u U T hT hmeas hbound
  have hupper : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), u t ≤ U := by
    filter_upwards [hbound] with t ht
    exact ht.2
  exact any_resource_solution_lower_bound
    u f eta B initial U T hT heta hB hi hu hf hfode hinitial hupper

#print axioms admissible_control_integrable
#print axioms admissible_resource_exists_unique_on
#print axioms admissible_resource_lower_bound

end GSTStage14
