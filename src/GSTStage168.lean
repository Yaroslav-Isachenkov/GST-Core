import GSTStage167
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11

namespace GSTStage168

theorem nonnegative_halfline_integrable_of_budget
    (f : ℝ → ℝ) (C : ℝ)
    (hf : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable f volume 0 T)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hbudget : ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, f t) ≤ C) :
    IntegrableOn f (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), f t) ≤ C := by
  have hlocal : ∀ T : ℝ, IntegrableOn f (Ioc (0 : ℝ) T) := by
    intro T
    by_cases hT : 0 ≤ T
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hf T hT)
    · have hT' : T ≤ 0 := (lt_of_not_ge hT).le
      simp [Ioc_eq_empty (not_lt_of_ge hT')]
  have hnorm : ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, ‖f t‖) =
        ∫ t in (0 : ℝ)..T, f t := by
    intro T hT
    rw [intervalIntegral.integral_of_le hT,
      intervalIntegral.integral_of_le hT]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact Real.norm_of_nonneg (hpos t ht.1.le)
  have hint : IntegrableOn f (Ioi (0 : ℝ)) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
      (b := fun T : ℝ => T) (l := atTop) C 0 hlocal tendsto_id
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    rw [hnorm T hT]
    exact hbudget T hT
  have hlim :
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, f t)
        atTop (𝓝 (∫ t in Ioi (0 : ℝ), f t)) :=
    intervalIntegral_tendsto_integral_Ioi
      (b := fun T : ℝ => T) 0 hint tendsto_id
  refine ⟨hint, ?_⟩
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact hbudget T hT

theorem zero_source_resource_integrable_and_total_le
    (u : ℝ → ℝ) (eta initial : ℝ)
    (heta : 0 < eta) (hi : 0 ≤ initial)
    (hu : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable u volume 0 T)
    (huNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) :
    IntegrableOn
      (fun t => resource u eta 0 initial t * u t) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ), resource u eta 0 initial t * u t) ≤
        initial / eta := by
  apply nonnegative_halfline_integrable_of_budget
    (fun t => resource u eta 0 initial t * u t) (initial / eta)
  · intro T hT
    exact (hu T hT).continuousOn_mul
      (GSTStage11.resource_continuousOn u eta 0 initial T (hu T hT))
  · intro t ht
    exact mul_nonneg
      (GSTStage30.resource_nonneg u eta 0 initial t (by norm_num) hi ht)
      (huNonneg t ht)
  · intro T hT
    exact GSTStage167.zero_source_resource_integral_le
      u eta initial T heta hi hT (hu T hT)

end GSTStage168

#print axioms GSTStage168.nonnegative_halfline_integrable_of_budget
#print axioms GSTStage168.zero_source_resource_integrable_and_total_le
