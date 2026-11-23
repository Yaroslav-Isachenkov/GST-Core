import GSTStage161

open Set
open GSTStage11 GSTStage31 GSTStage159

namespace GSTStage162

theorem candidate_saturated_maximum_bounds_impossible
    (x : StateData) (a : ℝ)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (hU : x.U = 1) (htarget : x.target = 1)
    (hi : 0 < x.phiInitial)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (haPos : 0 < a)
    (hP : 12 / 5 < p x a)
    (hS : 0 < S x a)
    (hFpos : 0 < resource x.u x.eta x.B x.phiInitial a)
    (hFupper : resource x.u x.eta x.B x.phiInitial a ≤ 41 / 500)
    (hF : resource x.u x.eta x.B x.phiInitial a =
      1 / 10 - 3 * p x a / 400)
    (hZ : z x a ≤ 8 * p x a)
    (hsat : 1 / 5 ≤ resource x.u x.eta x.B x.phiInitial a *
      (p x a - z x a / 20)) :
    False := by
  have hpersist := GSTStage161.candidate_saturation_until_clock_two
    x a ha hc heta hrho hq hU htarget hclip
    haPos hP.le hS hFpos hFupper hF hsat
  have hu : ∀ t ∈ Ioo a (saturationEnd a), x.u t = 1 := by
    intro t ht
    exact hpersist.2 t ⟨ht.1, ht.2.le⟩
  have heq := GSTStage152.candidate_saturated_eq_profiles
    x a (saturationEnd a)
    ha hc heta hrho hq htarget hclip haPos hu hF
  have hmem : saturationEnd a ∈ Icc a (saturationEnd a) :=
    ⟨(saturationEnd_gt a).le, le_rfl⟩
  have hzEq := heq.2.2.2 hmem
  change z x (saturationEnd a) =
    GSTStage147.satZ (p x a) (S x a)
      (resource x.u x.eta x.B x.phiInitial a)
      (z x a) x.B
      (GSTStage151.satClock a (saturationEnd a)) at hzEq
  rw [satClock_at_saturationEnd] at hzEq
  have hzNegative : z x (saturationEnd a) < -82 / 15 := by
    rw [hzEq]
    exact GSTStage153.saturated_z_at_two_negative
      (p x a) (S x a)
      (resource x.u x.eta x.B x.phiInitial a)
      (z x a) x.B hP hS x.hB hZ hF
  have hzNonneg : 0 ≤ z x (saturationEnd a) :=
    GSTStage44.candidate_z_nonneg
      x (1 / 10) (by norm_num) hi hclip
      (saturationEnd a) (lt_trans haPos (saturationEnd_gt a)).le
  linarith only [hzNegative, hzNonneg]

end GSTStage162

#print axioms GSTStage162.candidate_saturated_maximum_bounds_impossible
