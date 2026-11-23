import GSTStage76
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage77

theorem hilbert_bounded_weak_subsequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (v : ℕ → E) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ w : E, ‖w‖ ≤ C ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ g : E, Tendsto (fun n => inner ℝ (v (ψ n)) g)
          atTop (𝓝 (inner ℝ w g)) := by
  let vWeak : ℕ → WeakDual ℝ E :=
    fun n => StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ E) (v n))
  have hvWeak : ∀ n, vWeak n ∈
      WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℝ E) C := by
    intro n
    change dist ((InnerProductSpace.toDual ℝ E) (v n)) 0 ≤ C
    simpa only [dist_zero_right, LinearIsometryEquiv.norm_map] using hv n
  obtain ⟨phi, hphi, ψ, hψ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ E
      (0 : StrongDual ℝ E) C).subseq_of_frequently_in
        (Filter.Eventually.of_forall hvWeak).frequently
  let w : E := (InnerProductSpace.toDual ℝ E).symm
    (WeakDual.toStrongDual phi)
  have hphiNorm : ‖WeakDual.toStrongDual phi‖ ≤ C := by
    change dist (WeakDual.toStrongDual phi) 0 ≤ C at hphi
    simpa only [dist_zero_right] using hphi
  have hwNorm : ‖w‖ = ‖WeakDual.toStrongDual phi‖ :=
    (InnerProductSpace.toDual ℝ E).symm.norm_map _
  refine ⟨w, hwNorm.le.trans hphiNorm, ψ, hψ, ?_⟩
  intro g
  have heval : Tendsto (fun ell : WeakDual ℝ E => ell g)
      (𝓝 phi) (𝓝 (phi g)) :=
    (WeakDual.eval_continuous g).continuousAt
  have hscalar : Tendsto (fun n => vWeak (ψ n) g)
      atTop (𝓝 (phi g)) :=
    heval.comp hlim
  have hw : inner ℝ w g = phi g := by
    exact InnerProductSpace.toDual_symm_apply
  rw [← hw] at hscalar
  exact hscalar

theorem interval_L2_bounded_weak_subsequence
    (T : ℝ)
    (v : ℕ → Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)))
    (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) :
    ∃ w : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
      ‖w‖ ≤ C ∧
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
        ∀ g : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) T)),
          Tendsto (fun n => inner ℝ (v (ψ n)) g)
            atTop (𝓝 (inner ℝ w g)) := by
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  exact hilbert_bounded_weak_subsequence v C hv

#print axioms GSTStage77.hilbert_bounded_weak_subsequence
#print axioms GSTStage77.interval_L2_bounded_weak_subsequence

end GSTStage77
