import GSTStage81

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage82

theorem countable_hilbert_weak_subsequence
    {E : ℕ → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, CompleteSpace (E i)]
    [∀ i, TopologicalSpace.SeparableSpace (E i)]
    (v : ∀ i, ℕ → E i) (C : ℕ → ℝ)
    (hv : ∀ i n, ‖v i n‖ ≤ C i) :
    ∃ w : ∀ i, E i,
      (∀ i, ‖w i‖ ≤ C i) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ i (g : E i),
          Tendsto (fun n => inner ℝ (v i (ψ n)) g)
            atTop (𝓝 (inner ℝ (w i) g)) := by

  let K (i : ℕ) : Set (WeakDual ℝ (E i)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (E i)) (C i)
  have hK (i : ℕ) : IsCompact (K i) :=
    WeakDual.isCompact_closedBall ℝ (0 : StrongDual ℝ (E i)) (C i)
  letI : ∀ i, CompactSpace (K i) :=
    fun i => isCompact_iff_compactSpace.mp (hK i)
  letI : ∀ i, TopologicalSpace.MetrizableSpace (K i) :=
    fun i => WeakDual.metrizable_of_isCompact ℝ (E i) (K i) (hK i)
  let z : ℕ → ∀ i, K i := fun n i =>
    ⟨StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ (E i)) (v i n)), by
      change dist ((InnerProductSpace.toDual ℝ (E i)) (v i n)) 0 ≤ C i
      simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hv i n⟩
  obtain ⟨ell, ψ, hψ, hlim⟩ := CompactSpace.tendsto_subseq z
  let w : ∀ i, E i := fun i =>
    (InnerProductSpace.toDual ℝ (E i)).symm
      (WeakDual.toStrongDual (ell i).val)
  have hwNorm (i : ℕ) : ‖w i‖ ≤ C i := by
    have hb := (ell i).property
    change dist (WeakDual.toStrongDual (ell i).val) 0 ≤ C i at hb
    have hn : ‖w i‖ = ‖WeakDual.toStrongDual (ell i).val‖ :=
      (InnerProductSpace.toDual ℝ (E i)).symm.norm_map _
    rw [hn]
    simpa only [dist_zero_right] using hb
  refine ⟨w, hwNorm, ψ, hψ, ?_⟩
  intro i g
  have heval : Continuous (fun a : ∀ j, K j => (a i).val g) :=
    ((WeakDual.eval_continuous g).comp continuous_subtype_val).comp
      (continuous_apply i)
  have hevalAt : Tendsto (fun a : ∀ j, K j => (a i).val g)
      (𝓝 ell) (𝓝 ((ell i).val g)) := heval.continuousAt
  have hscalar : Tendsto (fun n => (z (ψ n) i).val g)
      atTop (𝓝 ((ell i).val g)) := hevalAt.comp hlim
  have hw : inner ℝ (w i) g = (ell i).val g := by
    exact InnerProductSpace.toDual_symm_apply
  rw [← hw] at hscalar
  exact hscalar

#print axioms GSTStage82.countable_hilbert_weak_subsequence

end GSTStage82
