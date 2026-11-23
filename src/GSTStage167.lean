import GSTStage166

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11

namespace GSTStage167

theorem zero_source_resource_integral_balance
    (u : ℝ → ℝ) (eta initial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    eta * (∫ t in (0 : ℝ)..T, resource u eta 0 initial t * u t) =
      initial - resource u eta 0 initial T := by
  have hFTC := GSTStage08.ac_integral_identity
    (resource u eta 0 initial)
    (fun t => (0 : ℝ) - eta * u t * resource u eta 0 initial t)
    0 T
    (GSTStage12.resource_ac u eta 0 initial T hu)
    (GSTStage12.resource_ode_ae u eta 0 initial T hu)
  have hfun :
      (fun t => (0 : ℝ) - eta * u t * resource u eta 0 initial t) =
      (fun t => (-eta) * (resource u eta 0 initial t * u t)) := by
    funext t
    ring
  rw [hfun, intervalIntegral.integral_const_mul, resource_initial] at hFTC
  nlinarith only [hFTC]

theorem zero_source_resource_integral_le
    (u : ℝ → ℝ) (eta initial T : ℝ)
    (heta : 0 < eta) (hi : 0 ≤ initial) (hT : 0 ≤ T)
    (hu : IntervalIntegrable u volume 0 T) :
    (∫ t in (0 : ℝ)..T, resource u eta 0 initial t * u t) ≤
      initial / eta := by
  have hbalance := zero_source_resource_integral_balance u eta initial T hu
  have hnonneg : 0 ≤ resource u eta 0 initial T :=
    GSTStage30.resource_nonneg u eta 0 initial T (by norm_num) hi hT
  apply (le_div_iff₀ heta).2
  nlinarith only [hbalance, hnonneg]

end GSTStage167

#print axioms GSTStage167.zero_source_resource_integral_balance
#print axioms GSTStage167.zero_source_resource_integral_le
