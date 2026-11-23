import GSTStage77

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage78

noncomputable def intervalL2Bound (U T : ℝ) : ℝ :=
  (((volume.restrict (Icc (0 : ℝ) T)) Set.univ) ^
    (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal U).toReal

theorem bounded_control_memLp
    (u : ℝ → ℝ) (U T : ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ u t ∧ u t ≤ U) :
    MemLp u 2 (volume.restrict (Icc (0 : ℝ) T)) := by
  have hb : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ‖u t‖ ≤ U := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (huBound t ht).1]
      exact (huBound t ht).2)
  exact MemLp.of_bound huMeas.aestronglyMeasurable U hb

theorem bounded_control_L2_norm
    (u : ℝ → ℝ) (U T : ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ u t ∧ u t ≤ U) :
    ‖(bounded_control_memLp u U T huMeas huBound).toLp u‖ ≤
      intervalL2Bound U T := by
  have hb : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), ‖u t‖ ≤ U := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => by
      rw [Real.norm_eq_abs, abs_of_nonneg (huBound t ht).1]
      exact (huBound t ht).2)
  have he := eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hb
  have hfinite :
      ((volume.restrict (Icc (0 : ℝ) T)) Set.univ) ^
        (2 : ENNReal).toReal⁻¹ * ENNReal.ofReal U ≠ ⊤ := by
    finiteness
  rw [Lp.norm_toLp]
  exact ENNReal.toReal_mono hfinite he

theorem bounded_controls_weak_subsequence
    (u : ℕ → ℝ → ℝ) (U T : ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ U) :
    ∃ v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
      (∀ n, (v n : ℝ → ℝ) =ᵐ[volume.restrict (Icc (0 : ℝ) T)] u n) ∧
      (∀ n, ‖v n‖ ≤ intervalL2Bound U T) ∧
      ∃ w : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
        ‖w‖ ≤ intervalL2Bound U T ∧
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
            Tendsto (fun n => inner ℝ (v (ψ n)) g)
              atTop (𝓝 (inner ℝ w g)) := by
  have hb : ∀ n t, t ∈ Icc (0 : ℝ) T →
      0 ≤ u n t ∧ u n t ≤ U :=
    fun n t ht => huBound n t ht.1
  let hv := fun n => bounded_control_memLp (u n) U T (huMeas n) (hb n)
  let v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)) :=
    fun n => (hv n).toLp (u n)
  have hvNorm : ∀ n, ‖v n‖ ≤ intervalL2Bound U T := by
    intro n
    exact bounded_control_L2_norm (u n) U T (huMeas n) (hb n)
  refine ⟨v, ?_, hvNorm, ?_⟩
  · intro n
    exact (hv n).coeFn_toLp
  · exact GSTStage77.interval_L2_bounded_weak_subsequence
      T v (intervalL2Bound U T) hvNorm

#print axioms GSTStage78.bounded_control_memLp
#print axioms GSTStage78.bounded_control_L2_norm
#print axioms GSTStage78.bounded_controls_weak_subsequence

end GSTStage78
