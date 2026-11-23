import GSTStage160

open Set
open GSTStage11 GSTStage31 GSTStage60 GSTStage159

namespace GSTStage161

theorem candidate_saturation_until_clock_two
    (x : StateData) (a : ℝ)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (hU : x.U = 1) (htarget : x.target = 1)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (haPos : 0 < a)
    (hP : 12 / 5 ≤ p x a)
    (hS : 0 < S x a)
    (hFpos : 0 < resource x.u x.eta x.B x.phiInitial a)
    (hFupper : resource x.u x.eta x.B x.phiInitial a ≤ 41 / 500)
    (hF : resource x.u x.eta x.B x.phiInitial a =
      1 / 10 - 3 * p x a / 400)
    (hsat : 1 / 5 ≤ resource x.u x.eta x.B x.phiInitial a *
      (p x a - z x a / 20)) :
    (∀ t ∈ Ioc a (saturationEnd a), 1 / 5 < w x t) ∧
    (∀ t ∈ Ioc a (saturationEnd a), x.u t = 1) := by
  have hd : d x a = p x a - z x a / 20 := by
    change x.c * p x a - x.eta * z x a =
      p x a - z x a / 20
    rw [hc, heta]
    ring
  have hw : 1 / 5 ≤ w x a := by
    unfold w
    rw [hd]
    exact hsat
  obtain ⟨b, hab, hbT, hprefix⟩ :=
    GSTStage160.candidate_strict_prefix_until_saturationEnd
      x a hclip haPos hFpos hS hw
  exact GSTStage158.candidate_saturation_persists_from_prefix
    x a b (saturationEnd a)
    ha hc heta hrho hq hU htarget hclip
    haPos hab hbT hP hS.le hFpos.le hFupper hF hsat
    (fun t ht => (satClock_bounds_until_end a t ht).2)
    hprefix

end GSTStage161

#print axioms GSTStage161.candidate_saturation_until_clock_two
