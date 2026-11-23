import GSTStage72
import Mathlib.Topology.Compactness.Compact

open Set Filter
open scoped Topology

namespace GSTStage73

theorem countable_compact_subsequence
    {X : ℕ → Type*}
    [∀ i, TopologicalSpace (X i)]
    [∀ i, FirstCountableTopology (X i)]
    (C : ∀ i, Set (X i)) (hC : ∀ i, IsCompact (C i))
    (v : ℕ → ∀ i, X i)
    (hv : ∀ n i, v n i ∈ C i) :
    ∃ f : ∀ i, X i, (∀ i, f i ∈ C i) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ i, Tendsto (fun n => v (ψ n) i) atTop (𝓝 (f i)) := by
  have hc : IsCompact {f : ∀ i, X i | ∀ i, f i ∈ C i} :=
    isCompact_pi_infinite hC
  obtain ⟨f, hf, ψ, hψ, hlim⟩ :=
    hc.tendsto_subseq (fun n => hv n)
  refine ⟨f, hf, ψ, hψ, ?_⟩
  intro i
  have heval : Tendsto (fun g : ∀ j, X j => g i)
      (𝓝 f) (𝓝 (f i)) :=
    (continuous_apply i).continuousAt
  exact heval.comp hlim

theorem countable_paired_function_subsequence
    {α : ℕ → Type*}
    [∀ i, PseudoMetricSpace (α i)]
    [∀ i, CompactSpace (α i)]
    (F G : ∀ i, ℕ → BoundedContinuousFunction (α i) ℝ)
    (K H : ℕ → NNReal) (R W : ℕ → ℝ)
    (hFLip : ∀ i n, LipschitzWith (K i) (F i n))
    (hGLip : ∀ i n, LipschitzWith (H i) (G i n))
    (hFBound : ∀ i n t, F i n t ∈ Icc (0 : ℝ) (R i))
    (hGBound : ∀ i n t, G i n t ∈ Icc (0 : ℝ) (W i)) :
    ∃ f g : ∀ i, BoundedContinuousFunction (α i) ℝ,
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ i, Tendsto (fun n => (F i (ψ n), G i (ψ n)))
          atTop (𝓝 (f i, g i)) := by
  let C := fun i =>
    (closure (range (F i))) ×ˢ (closure (range (G i)))
  have hC : ∀ i, IsCompact (C i) := by
    intro i
    exact (GSTStage71.compact_closure_of_uniform_bounds
      (F i) (K i) (R i) (hFLip i) (hFBound i)).prod
      (GSTStage71.compact_closure_of_uniform_bounds
        (G i) (H i) (W i) (hGLip i) (hGBound i))
  have hv : ∀ n i, (F i n, G i n) ∈ C i :=
    fun n i => ⟨subset_closure (mem_range_self n),
      subset_closure (mem_range_self n)⟩
  obtain ⟨p, _hp, ψ, hψ, hlim⟩ :=
    countable_compact_subsequence C hC
      (fun n i => (F i n, G i n)) hv
  exact ⟨(fun i => (p i).1), (fun i => (p i).2), ψ, hψ, hlim⟩

#print axioms GSTStage73.countable_compact_subsequence
#print axioms GSTStage73.countable_paired_function_subsequence

end GSTStage73
