import GSTStage169

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29

namespace GSTStage170

theorem zero_source_omega_tendsto_zero
    (u : ℝ → ℝ)
    (eta phiInitial a c omegaInitial : ℝ)
    (heta : 0 < eta) (ha : 0 < a)
    (hi : 0 ≤ phiInitial) (hc : 0 ≤ c) (ho : 0 ≤ omegaInitial)
    (hu : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable u volume 0 T)
    (huNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) :
    Tendsto (omega u eta 0 phiInitial a c omegaInitial)
      atTop (𝓝 (0 : ℝ)) := by
  let F : ℝ → ℝ := fun t => resource u eta 0 phiInitial t * u t
  let O : ℝ → ℝ := omega u eta 0 phiInitial a c omegaInitial
  have hF : IntegrableOn F (Ioi (0 : ℝ)) :=
    (GSTStage168.zero_source_resource_integrable_and_total_le
      u eta phiInitial heta hi hu huNonneg).1
  have hO : IntegrableOn O (Ioi (0 : ℝ)) :=
    (GSTStage169.zero_source_omega_integrable_and_total_le
      u eta phiInitial a c omegaInitial
      heta ha hi hc ho hu huNonneg).1
  have hlimF :
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, F t)
        atTop (𝓝 (∫ t in Ioi (0 : ℝ), F t)) :=
    intervalIntegral_tendsto_integral_Ioi
      (b := fun T : ℝ => T) 0 hF tendsto_id
  have hlimO :
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, O t)
        atTop (𝓝 (∫ t in Ioi (0 : ℝ), O t)) :=
    intervalIntegral_tendsto_integral_Ioi
      (b := fun T : ℝ => T) 0 hO tendsto_id
  let L : ℝ :=
    omegaInitial + c * (∫ t in Ioi (0 : ℝ), F t) -
      a * (∫ t in Ioi (0 : ℝ), O t)
  have hraw :
      Tendsto
        (fun T : ℝ =>
          omegaInitial + c * (∫ t in (0 : ℝ)..T, F t) -
            a * (∫ t in (0 : ℝ)..T, O t))
        atTop (𝓝 L) :=
    ((hlimF.const_mul c).const_add omegaInitial).sub
      (hlimO.const_mul a)
  have hlim : Tendsto O atTop (𝓝 L) := by
    apply hraw.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    have hb := GSTStage169.omega_integral_balance
      u eta 0 phiInitial a c omegaInitial T (hu T hT)
    change a * (∫ t in (0 : ℝ)..T, O t) =
      omegaInitial + c * (∫ t in (0 : ℝ)..T, F t) - O T at hb
    nlinarith only [hb]
  have hfilter : IntegrableAtFilter O atTop volume :=
    ⟨Ioi (0 : ℝ), Ioi_mem_atTop 0, hO⟩
  have hzero : L = 0 := by
    apply hfilter.eq_zero_of_tendsto _ hlim
    intro s hs
    rcases mem_atTop_sets.1 hs with ⟨b, hb⟩
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb
  rw [hzero] at hlim
  exact hlim

end GSTStage170

#print axioms GSTStage170.zero_source_omega_tendsto_zero
