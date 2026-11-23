import GSTStage157

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage60 GSTStage147 GSTStage151

namespace GSTStage158

theorem fixed_control_saturated_of_threshold
    (x : StateData) (t : ℝ)
    (hU : x.U = 1)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (ht : 0 ≤ t) (hw : 1 / 5 ≤ w x t) :
    x.u t = 1 := by
  have hh := hclip t ht
  have hinput :
      1 ≤ resource x.u x.eta x.B x.phiInitial t * d x t /
        (2 * (1 / 10 : ℝ)) := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2 * (1 / 10))).2
    change 1 / 5 ≤
      resource x.u x.eta x.B x.phiInitial t * d x t at hw
    nlinarith only [hw]
  rw [hU, min_eq_left hinput, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)] at hh
  exact hh

theorem candidate_saturation_persists_from_prefix
    (x : StateData) (a b T : ℝ)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (hU : x.U = 1) (htarget : x.target = 1)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (haPos : 0 < a) (hab : a < b) (hbT : b ≤ T)
    (hP : 12 / 5 ≤ p x a) (hM : 0 ≤ S x a)
    (hFnonneg : 0 ≤ resource x.u x.eta x.B x.phiInitial a)
    (hFupper : resource x.u x.eta x.B x.phiInitial a ≤ 41 / 500)
    (hF : resource x.u x.eta x.B x.phiInitial a =
      1 / 10 - 3 * p x a / 400)
    (hsat : 1 / 5 ≤ resource x.u x.eta x.B x.phiInitial a *
      (p x a - z x a / 20))
    (hclock : ∀ t ∈ Ioc a T, satClock a t ≤ 2)
    (hprefix : ∀ t ∈ Ioc a b, 1 / 5 < w x t) :
    (∀ t ∈ Ioc a T, 1 / 5 < w x t) ∧
    (∀ t ∈ Ioc a T, x.u t = 1) := by
  have hcont : ContinuousOn (w x) (Icc b T) := by
    intro t ht
    exact (GSTStage60.w_hasDerivAt x (1 / 10) hclip t
      (lt_of_lt_of_le (lt_trans haPos hab) ht.1)).continuousAt.continuousWithinAt

  have hstep : ∀ t ∈ Ioc a T,
      (∀ s ∈ Ioo a t, 1 / 5 < w x s) → 1 / 5 < w x t := by
    intro t ht hbefore
    have hu : ∀ s ∈ Ioo a t, x.u s = 1 := by
      intro s hs
      exact fixed_control_saturated_of_threshold x s hU hclip
        (lt_trans haPos hs.1).le (hbefore s hs).le
    have heq := GSTStage152.candidate_saturated_eq_profiles
      x a t ha hc heta hrho hq htarget hclip haPos hu hF
    have hmem : t ∈ Icc a t := ⟨ht.1.le, le_rfl⟩
    have hX : 1 < satClock a t := by
      have harg : 0 < (t - a) / 20 := by linarith only [ht.1]
      have he := Real.exp_lt_exp.mpr harg
      simpa only [Real.exp_zero, satClock] using he
    have hbound := GSTStage156.saturated_product_strictly_above_threshold
      (p x a) (S x a) (resource x.u x.eta x.B x.phiInitial a)
      (z x a) x.B (satClock a t)
      hP hM hFnonneg hFupper x.hB hF hsat hX (hclock t ht)
    have hd : d x t = p x t - z x t / 20 := by
      change x.c * p x t - x.eta * z x t = p x t - z x t / 20
      rw [hc, heta]
      ring
    change 1 / 5 <
      resource x.u x.eta x.B x.phiInitial t * d x t
    rw [hd, heq.1 hmem, heq.2.2.1 hmem, heq.2.2.2 hmem]
    exact hbound

  have hstrict := GSTStage157.strict_threshold_persistence
    (w x) a b T (1 / 5) hab hbT hcont hprefix hstep
  refine ⟨hstrict, ?_⟩
  intro t ht
  exact fixed_control_saturated_of_threshold x t hU hclip
    (lt_trans haPos ht.1).le (hstrict t ht).le

end GSTStage158

#print axioms GSTStage158.fixed_control_saturated_of_threshold
#print axioms GSTStage158.candidate_saturation_persists_from_prefix
