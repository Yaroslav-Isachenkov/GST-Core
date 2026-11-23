import GSTStage141
import Mathlib.Analysis.Calculus.Deriv.Slope

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage60

namespace GSTStage142

theorem eventually_gt_right_of_hasDerivAt_pos
    (f : ℝ → ℝ) (t v : ℝ)
    (hf : HasDerivAt f v t) (hv : 0 < v) :
    ∀ᶠ s in 𝓝[>] t, f t < f s := by
  have hslope : Tendsto (slope f t) (𝓝[>] t) (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hf).2
  have hpositive : ∀ᶠ s in 𝓝[>] t, 0 < slope f t s :=
    (tendsto_order.1 hslope).1 0 hv
  filter_upwards [hpositive, self_mem_nhdsWithin] with s hs hst
  have hst' : t < s := hst
  have hinv : 0 ≤ (s - t)⁻¹ :=
    (inv_pos.mpr (sub_pos.mpr hst')).le
  have hmul : 0 < (s - t)⁻¹ * (f s - f t) := by
    simpa only [slope, smul_eq_mul] using hs
  by_contra hnot
  have hdiff : f s - f t ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
  have hnonpos := mul_nonpos_of_nonneg_of_nonpos hinv hdiff
  exact (not_lt_of_ge hnonpos) hmul

theorem candidate_saturated_right_neighborhood
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hF : 0 < resource x.u x.eta x.B x.phiInitial t)
    (hS : 0 < S x t)
    (hu : x.u t = x.U) :
    ∀ᶠ s in 𝓝[>] t, x.u s = x.U := by
  have hclipped := hclip t ht.le
  rw [hu] at hclipped
  have hbound := GSTStage59.clipping_saturation_lower_bound
    r x.U
    (resource x.u x.eta x.B x.phiInitial t * d x t)
    hr hU hclipped
  have hW : 0 < w x t := by
    change 0 < resource x.u x.eta x.B x.phiInitial t * d x t
    exact lt_of_lt_of_le (by positivity) hbound
  have hD : 0 < d x t := by
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      hF.le (le_of_not_gt hn)
    exact (not_lt_of_ge hnonpos) hW
  have hrate :
      0 < x.rho * w x t + x.B * d x t +
        x.c * resource x.u x.eta x.B x.phiInitial t * S x t := by
    have hfirst : 0 < x.rho * w x t := mul_pos x.hrho hW
    have hsecond : 0 ≤ x.B * d x t := mul_nonneg x.hB hD.le
    have hthird :
        0 ≤ x.c * resource x.u x.eta x.B x.phiInitial t * S x t :=
      mul_nonneg (mul_nonneg x.hc hF.le) hS.le
    linarith
  have hgrow := eventually_gt_right_of_hasDerivAt_pos
    (w x) t
    (x.rho * w x t + x.B * d x t +
      x.c * resource x.u x.eta x.B x.phiInitial t * S x t)
    (GSTStage60.w_hasDerivAt x r hclip t ht) hrate
  filter_upwards [hgrow, self_mem_nhdsWithin] with s hs hst
  have hst' : t < s := hst
  have hs0 : 0 ≤ s := (lt_trans ht hst').le
  have hbound' : 2 * r * x.U ≤ w x s := by
    change 2 * r * x.U ≤ w x t at hbound
    exact hbound.trans hs.le
  have hdiv : x.U ≤ w x s / (2 * r) := by
    apply (le_div_iff₀ (show 0 < 2 * r by positivity)).2
    nlinarith only [hbound']
  have hcs := hclip s hs0
  change x.u s = max 0 (min x.U (w x s / (2 * r))) at hcs
  rw [min_eq_left hdiv, max_eq_right hU.le] at hcs
  exact hcs

theorem candidate_control_hasDerivWithinAt_zero_right
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hF : 0 < resource x.u x.eta x.B x.phiInitial t)
    (hS : 0 < S x t)
    (hu : x.u t = x.U) :
    HasDerivWithinAt x.u 0 (Ioi t) t := by
  have hnear := candidate_saturated_right_neighborhood
    x r t hr hU hclip ht hF hS hu
  have hconst :
      HasDerivWithinAt (fun _ : ℝ => x.U) 0 (Ioi t) t :=
    (hasDerivAt_const t x.U).hasDerivWithinAt
  exact hconst.congr_of_eventuallyEq hnear hu

end GSTStage142

#print axioms GSTStage142.eventually_gt_right_of_hasDerivAt_pos
#print axioms GSTStage142.candidate_saturated_right_neighborhood
#print axioms GSTStage142.candidate_control_hasDerivWithinAt_zero_right
