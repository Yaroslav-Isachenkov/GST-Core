import GSTStage84

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage85

theorem compatible_control_limits_on_nat_intervals
    (u : ℕ → ℝ → ℝ) (U : ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ U) :
    ∃ v : ∀ m : ℕ,
      ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ))),
      (∀ (m n : ℕ), (v m n : ℝ → ℝ) =ᵐ[
        volume.restrict (Icc (0 : ℝ) (m : ℝ))] u n) ∧
      ∃ w : ∀ m : ℕ,
        Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ))),
        (∀ m, ‖w m‖ ≤ GSTStage78.intervalL2Bound U (m : ℝ)) ∧
        (∀ m, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
          0 ≤ w m t ∧ w m t ≤ U) ∧
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          (∀ (m : ℕ)
            (g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ)))),
            Tendsto (fun n => inner ℝ (v m (ψ n)) g)
              atTop (𝓝 (inner ℝ (w m) g))) ∧
          ∀ (m k : ℕ),
            (w m : ℝ → ℝ) =ᵐ[volume.restrict
              (Icc (0 : ℝ) (m : ℝ) ∩ Icc (0 : ℝ) (k : ℝ))]
              (w k : ℝ → ℝ) := by

  obtain ⟨v, hrep, w, hwNorm, hwBound, ψ, hψ, hweak⟩ :=
    GSTStage83.admissible_controls_on_nat_intervals u U huMeas huBound
  have hint (m : ℕ) :
      IntegrableOn (fun t => w m t) (Icc (0 : ℝ) (m : ℝ)) volume := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (integrableOn_Lp_of_measure_ne_top (s := Set.univ)
        (w m) (by norm_num) (by finiteness))
  refine ⟨v, hrep, w, hwNorm, hwBound, ψ, hψ, hweak, ?_⟩
  intro m k
  apply GSTStage84.compatible_of_common_setIntegral_limits
    (Icc (0 : ℝ) (m : ℝ)) (Icc (0 : ℝ) (k : ℝ))
    measurableSet_Icc measurableSet_Icc
    (fun n => u (ψ n)) (fun t => w m t) (fun t => w k t)
    (hint m) (hint k)
  · intro r hr hrs
    exact GSTStage84.weak_L2_original_setIntegral_tendsto
      (Icc (0 : ℝ) (m : ℝ)) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (fun n => u (ψ n)) (fun n => v m (ψ n)) (w m)
      (fun n => hrep m (ψ n)) (hweak m) r hr hrs
  · intro r hr hrs
    exact GSTStage84.weak_L2_original_setIntegral_tendsto
      (Icc (0 : ℝ) (k : ℝ)) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (fun n => u (ψ n)) (fun n => v k (ψ n)) (w k)
      (fun n => hrep k (ψ n)) (hweak k) r hr hrs

#print axioms GSTStage85.compatible_control_limits_on_nat_intervals

end GSTStage85
