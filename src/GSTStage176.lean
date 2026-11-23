import GSTStage175

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29 GSTStage173 GSTStage174 GSTStage175

namespace GSTStage176

theorem exists_preserving_control_of_thresholds
    (B eta a h c s U phiInitial omegaInitial : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hh : 0 < h) (hs : 0 < s)
    (hphi : s ≤ phiInitial) (homega : h ≤ omegaInitial)
    (hsource : eta * a * h / c ≤ B)
    (heffort : a * h / (c * s) ≤ U) :
    ∃ u : ℝ → ℝ,
      Measurable u ∧
      ContinuousOn u (Ici (0 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) ∧
      (∀ t : ℝ, 0 ≤ t →
        h ≤ omega u eta B phiInitial a c omegaInitial t ∧
        s ≤ resource u eta B phiInitial t) ∧
      (∀ t : ℝ, 0 ≤ t →
        resource u eta B phiInitial t =
          phiInitial + (B - eta * a * h / c) * t ∧
        omega u eta B phiInitial a c omegaInitial t =
          h + (omegaInitial - h) * Real.exp (-a * t)) ∧
      (∀ t : ℝ, 0 ≤ t →
        u t = a * h / (c * resource u eta B phiInitial t)) := by
  let u := preservingControl B eta a h c phiInitial
  have hEq := preserving_canonical_trajectories_eq
    B eta a h c s U phiInitial omegaInitial
    ha hc hh hs hphi homega hsource heffort
  refine ⟨u,
    preserving_control_measurable B eta a h c phiInitial,
    preserving_control_continuousOn B eta a h c phiInitial
      hc (lt_of_lt_of_le hs hphi) hsource,
    ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (preserving_profiles_bounds
      B eta a h c s U phiInitial omegaInitial t
      ha hc hh hs hphi homega hsource heffort ht).2.2.1
  · intro t ht
    obtain ⟨hF, hO, _hu, _hflow⟩ := preserving_profiles_bounds
      B eta a h c s U phiInitial omegaInitial t
      ha hc hh hs hphi homega hsource heffort ht
    have he := hEq t ht
    change h ≤ omega
      (preservingControl B eta a h c phiInitial)
      eta B phiInitial a c omegaInitial t ∧
      s ≤ resource (preservingControl B eta a h c phiInitial)
        eta B phiInitial t
    rw [he.1, he.2]
    exact ⟨hO, hF⟩
  · intro t ht
    exact hEq t ht
  · intro t ht
    change preservingControl B eta a h c phiInitial t =
      a * h / (c * resource
        (preservingControl B eta a h c phiInitial) eta B phiInitial t)
    rw [(hEq t ht).1]
    rfl

end GSTStage176

#print axioms GSTStage176.exists_preserving_control_of_thresholds
