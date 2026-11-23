import GSTStage168

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29

namespace GSTStage169

theorem omega_integral_balance
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    a * (∫ t in (0 : ℝ)..T,
      omega u eta B phiInitial a c omegaInitial t) =
      omegaInitial +
        c * (∫ t in (0 : ℝ)..T,
          resource u eta B phiInitial t * u t) -
        omega u eta B phiInitial a c omegaInitial T := by
  have hs := omega_solution
    u eta B phiInitial a c omegaInitial T hu
  have hOm : IntervalIntegrable
      (omega u eta B phiInitial a c omegaInitial) volume 0 T :=
    hs.1.continuousOn.intervalIntegrable
  have hforcing : IntervalIntegrable
      (fun t => c * (resource u eta B phiInitial t * u t))
      volume 0 T :=
    resource_forcing_integrable u eta B phiInitial c T hu
  have hFTC := GSTStage08.ac_integral_identity
    (omega u eta B phiInitial a c omegaInitial)
    (fun t => -a * omega u eta B phiInitial a c omegaInitial t +
      c * (resource u eta B phiInitial t * u t))
    0 T hs.1 hs.2
  rw [intervalIntegral.integral_add (hOm.const_mul (-a)) hforcing,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, omega_initial] at hFTC
  nlinarith only [hFTC]

theorem zero_source_omega_integral_le
    (u : ℝ → ℝ)
    (eta phiInitial a c omegaInitial T : ℝ)
    (heta : 0 < eta) (ha : 0 < a)
    (hi : 0 ≤ phiInitial) (hc : 0 ≤ c) (ho : 0 ≤ omegaInitial)
    (hT : 0 ≤ T)
    (hu : IntervalIntegrable u volume 0 T)
    (huNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) :
    (∫ t in (0 : ℝ)..T,
      omega u eta 0 phiInitial a c omegaInitial t) ≤
      (omegaInitial + c * (phiInitial / eta)) / a := by
  have hbalance := omega_integral_balance
    u eta 0 phiInitial a c omegaInitial T hu
  have hresource := GSTStage167.zero_source_resource_integral_le
    u eta phiInitial T heta hi hT hu
  have hscaled := mul_le_mul_of_nonneg_left hresource hc
  have hnonneg := GSTStage30.omega_nonneg
    u eta 0 phiInitial a c omegaInitial T
    (by norm_num) hi hc ho hT huNonneg
  apply (le_div_iff₀ ha).2
  nlinarith only [hbalance, hscaled, hnonneg]

theorem zero_source_omega_integrable_and_total_le
    (u : ℝ → ℝ)
    (eta phiInitial a c omegaInitial : ℝ)
    (heta : 0 < eta) (ha : 0 < a)
    (hi : 0 ≤ phiInitial) (hc : 0 ≤ c) (ho : 0 ≤ omegaInitial)
    (hu : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable u volume 0 T)
    (huNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) :
    IntegrableOn
      (omega u eta 0 phiInitial a c omegaInitial) (Ioi (0 : ℝ)) ∧
      (∫ t in Ioi (0 : ℝ),
        omega u eta 0 phiInitial a c omegaInitial t) ≤
        (omegaInitial + c * (phiInitial / eta)) / a := by
  apply GSTStage168.nonnegative_halfline_integrable_of_budget
    (omega u eta 0 phiInitial a c omegaInitial)
    ((omegaInitial + c * (phiInitial / eta)) / a)
  · intro T hT
    exact (omega_solution
      u eta 0 phiInitial a c omegaInitial T
      (hu T hT)).1.continuousOn.intervalIntegrable
  · intro t ht
    exact GSTStage30.omega_nonneg
      u eta 0 phiInitial a c omegaInitial t
      (by norm_num) hi hc ho ht huNonneg
  · intro T hT
    exact zero_source_omega_integral_le
      u eta phiInitial a c omegaInitial T
      heta ha hi hc ho hT (hu T hT) huNonneg

end GSTStage169

#print axioms GSTStage169.omega_integral_balance
#print axioms GSTStage169.zero_source_omega_integral_le
#print axioms GSTStage169.zero_source_omega_integrable_and_total_le
