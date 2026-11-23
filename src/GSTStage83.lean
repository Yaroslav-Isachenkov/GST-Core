import GSTStage82

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage83

theorem admissible_controls_on_nat_intervals
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
          ∀ (m : ℕ)
            (g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ)))),
            Tendsto (fun n => inner ℝ (v m (ψ n)) g)
              atTop (𝓝 (inner ℝ (w m) g)) := by

  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  let hv (m n : ℕ) :
      MemLp (u n) 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ))) :=
    GSTStage78.bounded_control_memLp (u n) U (m : ℝ) (huMeas n)
      (fun t ht => huBound n t ht.1)
  let v : ∀ m : ℕ,
      ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ))) :=
    fun m n => (hv m n).toLp (u n)
  have hrep (m n : ℕ) :
      (v m n : ℝ → ℝ) =ᵐ[
        volume.restrict (Icc (0 : ℝ) (m : ℝ))] u n :=
    (hv m n).coeFn_toLp
  have hnorm (m n : ℕ) :
      ‖v m n‖ ≤ GSTStage78.intervalL2Bound U (m : ℝ) := by
    exact GSTStage78.bounded_control_L2_norm
      (u n) U (m : ℝ) (huMeas n) (fun t ht => huBound n t ht.1)
  obtain ⟨w, hwNorm, ψ, hψ, hweak⟩ :=
    GSTStage82.countable_hilbert_weak_subsequence
      v (fun m => GSTStage78.intervalL2Bound U (m : ℝ)) hnorm
  have hvBound (m n : ℕ) :
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
        0 ≤ v m n t ∧ v m n t ≤ U := by
    filter_upwards [hrep m n, ae_restrict_mem measurableSet_Icc] with t he ht
    rw [he]
    exact huBound n t ht.1
  refine ⟨v, hrep, w, hwNorm, ?_, ψ, hψ, hweak⟩
  intro m
  exact GSTStage79.weak_L2_preserves_bounds
    (fun n => v m (ψ n)) (w m) U
    (fun n => hvBound m (ψ n)) (hweak m)

#print axioms GSTStage83.admissible_controls_on_nat_intervals

end GSTStage83
