import GSTStage170

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29

namespace GSTStage171

theorem theorem5_zero_source
    (u : ℝ → ℝ)
    (eta phiInitial a c omegaInitial U : ℝ)
    (heta : 0 < eta) (ha : 0 < a)
    (hi : 0 ≤ phiInitial) (hc : 0 ≤ c) (ho : 0 ≤ omegaInitial)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) :
    IntegrableOn
      (fun t => resource u eta 0 phiInitial t * u t) (Ioi (0 : ℝ)) ∧
    ((∫ t in Ioi (0 : ℝ), resource u eta 0 phiInitial t * u t) ≤
      phiInitial / eta) ∧
    IntegrableOn
      (omega u eta 0 phiInitial a c omegaInitial) (Ioi (0 : ℝ)) ∧
    ((∫ t in Ioi (0 : ℝ),
      omega u eta 0 phiInitial a c omegaInitial t) ≤
      (omegaInitial + c * (phiInitial / eta)) / a) ∧
    Tendsto (omega u eta 0 phiInitial a c omegaInitial)
      atTop (𝓝 (0 : ℝ)) ∧
    (∀ h : ℝ, 0 < h →
      ∀ᶠ t in atTop, omega u eta 0 phiInitial a c omegaInitial t < h) ∧
    (∀ h : ℝ, 0 < h →
      ¬ (∀ t : ℝ, 0 ≤ t →
        h ≤ omega u eta 0 phiInitial a c omegaInitial t)) := by
  have hu : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable u volume 0 T := by
    intro T hT
    apply GSTStage14.admissible_control_integrable u U T hT huMeas
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => huBound t ht.1)
  have huNonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t :=
    fun t ht => (huBound t ht).1
  obtain ⟨hRint, hRbound⟩ :=
    GSTStage168.zero_source_resource_integrable_and_total_le
      u eta phiInitial heta hi hu huNonneg
  obtain ⟨hOint, hObound⟩ :=
    GSTStage169.zero_source_omega_integrable_and_total_le
      u eta phiInitial a c omegaInitial
      heta ha hi hc ho hu huNonneg
  have hlim := GSTStage170.zero_source_omega_tendsto_zero
    u eta phiInitial a c omegaInitial
    heta ha hi hc ho hu huNonneg
  have hbelow : ∀ h : ℝ, 0 < h →
      ∀ᶠ t in atTop, omega u eta 0 phiInitial a c omegaInitial t < h := by
    intro h hh
    exact (tendsto_order.1 hlim).2 h hh
  refine ⟨hRint, hRbound, hOint, hObound, hlim, hbelow, ?_⟩
  intro h hh hkeep
  obtain ⟨t, ht, hlt⟩ :=
    ((eventually_ge_atTop (0 : ℝ)).and (hbelow h hh)).exists
  exact (not_le_of_gt hlt) (hkeep t ht)

end GSTStage171

#print axioms GSTStage171.theorem5_zero_source
