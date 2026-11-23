import GSTStage159

open Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage60 GSTStage159

namespace GSTStage160

theorem candidate_strict_threshold_right
    (x : StateData) (a : ℝ)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (ha : 0 < a)
    (hF : 0 < resource x.u x.eta x.B x.phiInitial a)
    (hS : 0 < S x a)
    (hw : 1 / 5 ≤ w x a) :
    ∀ᶠ t in 𝓝[>] a, 1 / 5 < w x t := by
  have hwpos : 0 < w x a := by
    linarith only [hw]
  have hdpos : 0 < d x a := by
    by_contra hn
    have hdnonpos : d x a ≤ 0 := le_of_not_gt hn
    have hprod :=
      mul_nonpos_of_nonneg_of_nonpos hF.le hdnonpos
    change w x a ≤ 0 at hprod
    exact (not_le_of_gt hwpos) hprod
  have hrate :
      0 < x.rho * w x a + x.B * d x a +
        x.c * resource x.u x.eta x.B x.phiInitial a * S x a := by
    exact add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg
        (mul_pos x.hrho hwpos)
        (mul_nonneg x.hB hdpos.le))
      (mul_nonneg (mul_nonneg x.hc hF.le) hS.le)
  have hg := GSTStage142.eventually_gt_right_of_hasDerivAt_pos
    (w x) a
    (x.rho * w x a + x.B * d x a +
      x.c * resource x.u x.eta x.B x.phiInitial a * S x a)
    (GSTStage60.w_hasDerivAt x (1 / 10) hclip a ha) hrate
  filter_upwards [hg] with t ht
  exact lt_of_le_of_lt hw ht

theorem candidate_strict_prefix_until_saturationEnd
    (x : StateData) (a : ℝ)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (ha : 0 < a)
    (hF : 0 < resource x.u x.eta x.B x.phiInitial a)
    (hS : 0 < S x a)
    (hw : 1 / 5 ≤ w x a) :
    ∃ b : ℝ, a < b ∧ b ≤ saturationEnd a ∧
      ∀ t ∈ Ioc a b, 1 / 5 < w x t := by
  exact strict_prefix_of_eventually_right
    (w x) a (saturationEnd a) (1 / 5)
    (saturationEnd_gt a)
    (candidate_strict_threshold_right x a hclip ha hF hS hw)

end GSTStage160

#print axioms GSTStage160.candidate_strict_threshold_right
#print axioms GSTStage160.candidate_strict_prefix_until_saturationEnd
