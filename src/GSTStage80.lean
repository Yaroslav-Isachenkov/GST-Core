import GSTStage79

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage80

theorem admissible_control_weak_subsequence
    (u : ℕ → ℝ → ℝ) (U T : ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ U) :
    ∃ v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
      (∀ n, (v n : ℝ → ℝ) =ᵐ[volume.restrict (Icc (0 : ℝ) T)] u n) ∧
      ∃ w : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
        ‖w‖ ≤ GSTStage78.intervalL2Bound U T ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), 0 ≤ w t ∧ w t ≤ U) ∧
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
            Tendsto (fun n => inner ℝ (v (ψ n)) g)
              atTop (𝓝 (inner ℝ w g)) := by
  obtain ⟨v, hrep, _, w, hwNorm, ψ, hψ, hweak⟩ :=
    GSTStage78.bounded_controls_weak_subsequence u U T huMeas huBound
  have hvBound (n : ℕ) :
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), 0 ≤ v n t ∧ v n t ≤ U := by
    filter_upwards [hrep n, ae_restrict_mem measurableSet_Icc] with t he ht
    rw [he]
    exact huBound n t ht.1
  have hwBound := GSTStage79.weak_L2_preserves_bounds
    (fun n => v (ψ n)) w U (fun n => hvBound (ψ n)) hweak
  exact ⟨v, hrep, w, hwNorm, hwBound, ψ, hψ, hweak⟩

#print axioms GSTStage80.admissible_control_weak_subsequence

end GSTStage80
