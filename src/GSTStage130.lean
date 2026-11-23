import GSTStage129
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34 GSTStage37 GSTStage128

namespace GSTStage130

theorem halfline_continuous_eq_of_ae
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Ici (0 : ℝ)))
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (h : f =ᵐ[volume.restrict (Ioi (0 : ℝ))] g) :
    ∀ t : ℝ, 0 ≤ t → f t = g t := by
  have ha : ∀ᵐ s : ℝ, s ∈ Ioi (0 : ℝ) → f s = g s := by
    have h' : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)), f s = g s := h
    exact (ae_restrict_iff' measurableSet_Ioi).mp h'
  have hz : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
    simp [ae_iff, measure_singleton]
  intro t ht
  have hT : (0 : ℝ) < t + 1 := by linarith
  have hI : f =ᵐ[volume.restrict (Icc (0 : ℝ) (t + 1))] g := by
    change ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t + 1)), f s = g s
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [ha, hz] with s hs hs0
    intro hmem
    have hspos : 0 < s := lt_of_le_of_ne hmem.1 (Ne.symm hs0)
    exact hs hspos
  have hsub : Icc (0 : ℝ) (t + 1) ⊆ Ici (0 : ℝ) :=
    fun _ hs => hs.1
  have heq := MeasureTheory.Measure.eqOn_Icc_of_ae_eq
    (μ := volume) (ne_of_lt hT) hI (hf.mono hsub) (hg.mono hsub)
  exact heq ⟨ht, by linarith⟩

theorem continuous_optimal_control_clipping
    (x : StateData) (r : ℝ) (hr : 0 < r)
    (huCont : ContinuousOn x.u (Ici (0 : ℝ)))
    (hoptimal : ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r x.u) :
    ∀ t : ℝ, 0 ≤ t →
      x.u t = max 0 (min x.U
        ((resource x.u x.eta x.B x.phiInitial t * d x t) / (2 * r))) := by
  have ha := optimal_control_clipping_ae x r hr hoptimal
  have heq : x.u =ᵐ[volume.restrict (Ioi (0 : ℝ))] clippedControl x r := by
    filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with t ht hmem
    have ht0 : 0 ≤ t := le_of_lt (show 0 < t from hmem)
    exact ht.trans (clipped_control_eq x r t ht0).symm
  have hp := halfline_continuous_eq_of_ae
    x.u (clippedControl x r) huCont
    (clipped_control_continuous x r).continuousOn heq
  intro t ht
  exact (hp t ht).trans (clipped_control_eq x r t ht)

end GSTStage130

#print axioms GSTStage130.halfline_continuous_eq_of_ae
#print axioms GSTStage130.continuous_optimal_control_clipping
