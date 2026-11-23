import GSTStage80

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11

namespace GSTStage81

theorem joint_subsequence_on_interval
    (x : StateData) (T : ℝ) (hT : 0 ≤ T)
    (u : ℕ → ℝ → ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ x.U) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
      ∃ v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
      ∃ w : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
      ∃ F G : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ,
      ∃ f g : BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ,
        (∀ n, (v n : ℝ → ℝ) =ᵐ[volume.restrict (Icc (0 : ℝ) T)] u (κ n)) ∧
        ‖w‖ ≤ GSTStage78.intervalL2Bound x.U T ∧
        (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), 0 ≤ w t ∧ w t ≤ x.U) ∧
        (∀ z : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
          Tendsto (fun n => inner ℝ (v n) z) atTop (𝓝 (inner ℝ w z))) ∧
        (∀ n t, F n t = resource (u (κ n)) x.eta x.B x.phiInitial t ∧
          G n t = competitorState x (u (κ n)) t) ∧
        Tendsto (fun n => (F n, G n)) atTop (𝓝 (f, g)) := by

  obtain ⟨v, hrep, w, hwNorm, hwBound, ψ, hψ, hweak⟩ :=
    GSTStage80.admissible_control_weak_subsequence u x.U T huMeas huBound
  obtain ⟨F, G, htraj, f, g, χ, hχ, hconv⟩ :=
    GSTStage72.trajectory_subsequence_on_interval x T hT
      (fun n => u (ψ n))
      (fun n => huMeas (ψ n))
      (fun n t ht => huBound (ψ n) t ht)
  refine ⟨(fun n => ψ (χ n)), hψ.comp hχ,
    (fun n => v (ψ (χ n))), w,
    (fun n => F (χ n)), (fun n => G (χ n)), f, g,
    ?_, hwNorm, hwBound, ?_, ?_, hconv⟩
  · intro n
    exact hrep (ψ (χ n))
  · intro z
    exact (hweak z).comp hχ.tendsto_atTop
  · intro n t
    exact htraj (χ n) t

#print axioms GSTStage81.joint_subsequence_on_interval

end GSTStage81
