import GSTStage70
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

open Set Filter
open scoped Topology

namespace GSTStage71

theorem compact_closure_of_uniform_bounds
    {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    (F : ℕ → BoundedContinuousFunction α ℝ) (K : NNReal) (R : ℝ)
    (hLip : ∀ n, LipschitzWith K (F n))
    (hBound : ∀ n t, F n t ∈ Icc (0 : ℝ) R) :
    IsCompact (closure (range F)) := by
  have hfamily :
      ∀ f : range F, LipschitzWith K
        (fun t : α => (f.val : BoundedContinuousFunction α ℝ) t) := by
    intro f
    obtain ⟨n, hn⟩ := f.property
    simpa only [← hn] using hLip n
  have hequi :
      Equicontinuous
        (fun f : range F => fun t : α => (f.val : BoundedContinuousFunction α ℝ) t) :=
    (LipschitzWith.uniformEquicontinuous
      (fun f : range F => fun t : α => (f.val : BoundedContinuousFunction α ℝ) t)
      K hfamily).equicontinuous
  apply BoundedContinuousFunction.arzela_ascoli
    (Icc (0 : ℝ) R) isCompact_Icc (range F)
  · intro f t hf
    obtain ⟨n, rfl⟩ := hf
    exact hBound n t
  · exact hequi

theorem paired_subsequence_of_uniform_bounds
    {α : Type*} [PseudoMetricSpace α] [CompactSpace α]
    (F G : ℕ → BoundedContinuousFunction α ℝ)
    (K H : NNReal) (R W : ℝ)
    (hFLip : ∀ n, LipschitzWith K (F n))
    (hGLip : ∀ n, LipschitzWith H (G n))
    (hFBound : ∀ n t, F n t ∈ Icc (0 : ℝ) R)
    (hGBound : ∀ n t, G n t ∈ Icc (0 : ℝ) W) :
    ∃ f g : BoundedContinuousFunction α ℝ,
      f ∈ closure (range F) ∧
      g ∈ closure (range G) ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        Tendsto (fun n => (F (ψ n), G (ψ n)))
          atTop (𝓝 (f, g)) := by
  have hF := compact_closure_of_uniform_bounds F K R hFLip hFBound
  have hG := compact_closure_of_uniform_bounds G H W hGLip hGBound
  have hmem : ∀ n : ℕ,
      (F n, G n) ∈ (closure (range F)) ×ˢ (closure (range G)) :=
    fun n => ⟨subset_closure (mem_range_self n),
      subset_closure (mem_range_self n)⟩
  obtain ⟨p, hp, ψ, hψ, hlim⟩ :=
    (hF.prod hG).tendsto_subseq hmem
  exact ⟨p.1, p.2, hp.1, hp.2, ψ, hψ, hlim⟩

#print axioms GSTStage71.compact_closure_of_uniform_bounds
#print axioms GSTStage71.paired_subsequence_of_uniform_bounds

end GSTStage71
