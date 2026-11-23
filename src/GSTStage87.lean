import GSTStage86

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage87

theorem global_admissible_control_limit
    (u : ℕ → ℝ → ℝ) (U : ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ U) :
    ∃ a : ℝ → ℝ, Measurable a ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        0 ≤ a t ∧ a t ≤ U) ∧
      ∃ v : ∀ m : ℕ,
        ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ))),
        (∀ (m n : ℕ), (v m n : ℝ → ℝ) =ᵐ[
          volume.restrict (Icc (0 : ℝ) (m : ℝ))] u n) ∧
        ∃ w : ∀ m : ℕ,
          Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ))),
          (∀ m, ‖w m‖ ≤ GSTStage78.intervalL2Bound U (m : ℝ)) ∧
          (∀ m : ℕ, a =ᵐ[
            volume.restrict (Icc (0 : ℝ) (m : ℝ))]
              (w m : ℝ → ℝ)) ∧
          ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
            ∀ (m : ℕ)
              (g : Lp ℝ 2
                (volume.restrict (Icc (0 : ℝ) (m : ℝ)))),
              Tendsto (fun n => inner ℝ (v m (ψ n)) g)
                atTop (𝓝 (inner ℝ (w m) g)) := by
  obtain ⟨v, hrep, w, hwNorm, hwBound, ψ, hψ, hweak, hcompat⟩ :=
    GSTStage85.compatible_control_limits_on_nat_intervals
      u U huMeas huBound
  have hwMeas (m : ℕ) : Measurable (fun t => w m t) :=
    (Lp.stronglyMeasurable (w m)).measurable
  obtain ⟨a, haMeas, haEq⟩ :=
    GSTStage86.glue_ae_compatible_interval_functions
      (fun m t => w m t) hwMeas hcompat
  have haBound (m : ℕ) :
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
        0 ≤ a t ∧ a t ≤ U := by
    filter_upwards [haEq m, hwBound m] with t he hb
    rw [he]
    exact hb
  have haGlobal :=
    GSTStage86.ae_bounds_on_halfline_of_nat_intervals a U haBound
  exact ⟨a, haMeas, haGlobal, v, hrep, w, hwNorm, haEq,
    ψ, hψ, hweak⟩

#print axioms GSTStage87.global_admissible_control_limit

end GSTStage87
