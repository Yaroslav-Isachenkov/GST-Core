import GSTStage143
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage57 GSTStage143

namespace GSTStage144

theorem right_second_derivative_nonpos_at_local_maximum
    (f g : ℝ → ℝ) (t v : ℝ)
    (hf : ∀ᶠ s in 𝓝 t, HasDerivAt f (g s) s)
    (hg : HasDerivWithinAt g v (Ioi t) t)
    (hzero : g t = 0)
    (hmax : ∀ᶠ s in 𝓝 t, f s ≤ f t) :
    v ≤ 0 := by
  by_contra hn
  have hv : 0 < v := lt_of_not_ge hn
  have hslope : Tendsto (slope g t) (𝓝[>] t) (𝓝 v) :=
    (hasDerivWithinAt_iff_tendsto_slope'
      (show t ∉ Ioi t by simp)).mp hg
  have hsl : ∀ᶠ s in 𝓝[>] t, 0 < slope g t s :=
    (tendsto_order.1 hslope).1 0 hv
  have hpos : ∀ᶠ s in 𝓝[>] t, 0 < g s := by
    filter_upwards [hsl, self_mem_nhdsWithin] with s hs hst
    have hst' : t < s := hst
    have hinv : 0 ≤ (s - t)⁻¹ :=
      (inv_pos.mpr (sub_pos.mpr hst')).le
    have hmul : 0 < (s - t)⁻¹ * g s := by
      simpa only [slope, vsub_eq_sub, smul_eq_mul, hzero, sub_zero] using hs
    by_contra hnot
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      hinv (le_of_not_gt hnot)
    exact (not_lt_of_ge hnonpos) hmul
  have hboth : ∀ᶠ s in 𝓝 t,
      HasDerivAt f (g s) s ∧ f s ≤ f t := by
    filter_upwards [hf, hmax] with s hs hm
    exact ⟨hs, hm⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hboth
  obtain ⟨ε, hε, hright⟩ := Metric.mem_nhdsWithin_iff.mp hpos
  let b : ℝ := t + min δ ε / 2
  have hab : t < b := by
    dsimp [b]
    have hm : 0 < min δ ε := lt_min hδ hε
    linarith
  have hdist : ∀ y ∈ Icc t b,
      dist y t < δ ∧ dist y t < ε := by
    intro y hy
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hy.1)]
    have hupper := hy.2
    change y ≤ t + min δ ε / 2 at hupper
    have hd := min_le_left δ ε
    have he := min_le_right δ ε
    constructor <;> linarith
  have hcont : ContinuousOn f (Icc t b) := by
    intro y hy
    have hd : HasDerivAt f (g y) y :=
      (hball (hdist y hy).1).1
    exact hd.continuousAt.continuousWithinAt
  have hderiv : ∀ y ∈ Ioo t b, HasDerivAt f (g y) y := by
    intro y hy
    exact (hball (hdist y ⟨hy.1.le, hy.2.le⟩).1).1
  have hmvt : ∃ c ∈ Ioo t b,
      g c = (f b - f t) / (b - t) := by
    apply exists_hasDerivAt_eq_slope <;> assumption
  obtain ⟨c, hc, heq⟩ := hmvt
  have hgc : 0 < g c :=
    hright ⟨(hdist c ⟨hc.1.le, hc.2.le⟩).2, hc.1⟩
  have hfb : f b ≤ f t :=
    (hball (hdist b ⟨hab.le, le_rfl⟩).1).2
  have hquot : (f b - f t) / (b - t) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr hfb) (sub_nonneg.mpr hab.le)
  rw [← heq] at hquot
  exact (not_lt_of_ge hquot) hgc

theorem candidate_saturated_second_rate_nonpos
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hF : 0 < resource x.u x.eta x.B x.phiInitial t)
    (hS : 0 < S x t)
    (hu : x.u t = x.U)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    saturatedSecondRate x t ≤ 0 := by
  have hfirst : ∀ᶠ s in 𝓝 t,
      HasDerivAt (S x) (sRate x s) s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact GSTStage57.s_hasDerivAt x r hclip s
      (show 0 < s from hs)
  have hsecond := GSTStage143.sRate_hasDerivWithinAt_saturated_right
    x r t hr hU hclip ht hF hS hu
  have hzero := GSTStage58.s_rate_zero_at_local_maximum
    x r t hclip ht hlocal
  exact right_second_derivative_nonpos_at_local_maximum
    (S x) (sRate x) t (saturatedSecondRate x t)
    hfirst hsecond hzero hlocal

end GSTStage144

#print axioms GSTStage144.right_second_derivative_nonpos_at_local_maximum
#print axioms GSTStage144.candidate_saturated_second_rate_nonpos
