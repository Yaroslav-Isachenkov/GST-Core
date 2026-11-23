import GSTStage178

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29

namespace GSTStage179

theorem preserving_region_iff_thresholds
    (eta B a c h s U : ℝ)
    (heta : 0 < eta) (hB : 0 ≤ B)
    (ha : 0 < a) (hc : 0 < c)
    (hh : 0 < h) (hs : 0 < s) :
    (∀ phiInitial omegaInitial : ℝ,
      s ≤ phiInitial → h ≤ omegaInitial →
      ∃ u : ℝ → ℝ,
        Measurable u ∧
        (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) ∧
        (∀ t : ℝ, 0 ≤ t →
          h ≤ omega u eta B phiInitial a c omegaInitial t ∧
          s ≤ resource u eta B phiInitial t)) ↔
    (a * h / (c * s) ≤ U ∧ eta * a * h / c ≤ B) := by
  constructor
  · intro hpreserve
    obtain ⟨u, hmeas, hbound, hkeep⟩ :=
      hpreserve s h le_rfl le_rfl
    have hstate : ∀ t : ℝ, 0 ≤ t →
        h ≤ omega u eta B s a c h t :=
      fun t ht => (hkeep t ht).1
    have hu : ∀ T : ℝ, 0 ≤ T →
        IntervalIntegrable u volume 0 T := by
      intro T hT
      exact GSTStage27.bounded_control_integrable
        u U T hT hmeas hbound
    have heffort :=
      GSTStage178.effort_threshold_necessary_at_corner
        u eta B a c h s U heta.le hB ha hc hs
        hmeas hbound hstate
    have hsource :=
      GSTStage177.source_threshold_necessary_of_state_lower_bound
        u eta B s a c h h heta ha hc hB hs.le hh hu hstate
    exact ⟨heffort, hsource⟩
  · rintro ⟨heffort, hsource⟩
    intro phiInitial omegaInitial hphi homega
    obtain ⟨u, hmeas, _hcont, hbound, hkeep, _hprofiles, _hfeedback⟩ :=
      GSTStage176.exists_preserving_control_of_thresholds
        B eta a h c s U phiInitial omegaInitial
        ha hc hh hs hphi homega hsource heffort
    exact ⟨u, hmeas, hbound, hkeep⟩

end GSTStage179

#print axioms GSTStage179.preserving_region_iff_thresholds
