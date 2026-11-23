import GSTStage60
open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage60

namespace GSTStage61

theorem clipping_eq_input_of_interior
    (U y v : ℝ)
    (hv : v = max 0 (min U y))
    (hv0 : 0 < v) (hvU : v < U) :
    v = y := by
  have hU : 0 < U := lt_trans hv0 hvU
  by_cases hy0 : y ≤ 0
  · have hm : min U y ≤ 0 := le_trans (min_le_right _ _) hy0
    rw [max_eq_left hm] at hv
    exact False.elim ((ne_of_gt hv0) hv)
  · have hypos : 0 < y := lt_of_not_ge hy0
    by_cases hyU : U ≤ y
    · rw [min_eq_left hyU, max_eq_right hU.le] at hv
      exact False.elim ((ne_of_lt hvU) hv)
    · have hylt : y < U := lt_of_not_ge hyU
      simpa only [min_eq_right hylt.le, max_eq_right hypos.le] using hv

theorem candidate_control_eq_near_interior
    (x : StateData) (r t : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hu0 : 0 < x.u t) (huU : x.u t < x.U) :
    ∀ᶠ s in 𝓝 t, x.u s = w x s / (2 * r) := by
  have hT : 0 ≤ t + 1 := by linarith
  have hcont : ContinuousOn x.u (Icc (0 : ℝ) (t + 1)) := by
    simpa only [uIcc_of_le hT] using
      GSTStage44.candidate_control_continuousOn x r (t + 1) hT hclip
  have hmem : Icc (0 : ℝ) (t + 1) ∈ 𝓝 t :=
    Icc_mem_nhds ht (by linarith)
  have huc : ContinuousAt x.u t := hcont.continuousAt hmem
  have hinterior : ∀ᶠ s in 𝓝 t, x.u s ∈ Ioo (0 : ℝ) x.U :=
    huc.eventually (Ioo_mem_nhds hu0 huU)
  filter_upwards [hinterior, Ioi_mem_nhds ht] with s hs hspos
  have hs0 : 0 ≤ s := (show 0 < s from hspos).le
  exact clipping_eq_input_of_interior
    x.U (w x s / (2 * r)) (x.u s) (hclip s hs0) hs.1 hs.2

theorem candidate_control_hasDerivAt_interior
    (x : StateData) (r t : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hu0 : 0 < x.u t) (huU : x.u t < x.U) :
    HasDerivAt x.u
      ((x.rho * w x t + x.B * d x t +
        x.c * resource x.u x.eta x.B x.phiInitial t * S x t) /
          (2 * r)) t := by
  have hw := GSTStage60.w_hasDerivAt x r hclip t ht
  have hquot := hw.div_const (2 * r)
  apply hquot.congr_of_eventuallyEq
  exact candidate_control_eq_near_interior x r t hclip ht hu0 huU

#print axioms clipping_eq_input_of_interior
#print axioms candidate_control_eq_near_interior
#print axioms candidate_control_hasDerivAt_interior
end GSTStage61
