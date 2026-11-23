import GSTStage162

open GSTStage11 GSTStage31

namespace GSTStage163

theorem fixed_candidate_S_nonpos
    (x : StateData)
    (ha : x.a = 1 / 10) (hc : x.c = 1)
    (heta : x.eta = 1 / 20) (hrho : x.rho = 1 / 20)
    (hq : x.q = 1) (hU : x.U = 1) (htarget : x.target = 1)
    (hphi : x.phiInitial = 1 / 2)
    (homega : x.omegaInitial = 1 / 5)
    (hclip : GSTStage44.Clipping x (1 / 10)) :
    ∀ s : ℝ, 0 ≤ s → S x s ≤ 0 := by
  intro s hs
  by_contra hn
  have hpositive : 0 < S x s := lt_of_not_ge hn
  obtain ⟨t, ht, hSt, _hstationary, _hlocal, hbounds⟩ :=
    GSTStage146.fixed_positive_saturated_maximum_with_bounds
      x ha hc heta hrho hq hU htarget hphi homega hclip
      s hs hpositive
  rcases hbounds with
    ⟨hu, hF, _hsecond, ⟨hP, _hPupper⟩,
      ⟨_hFlower, hFupper⟩, _hFP, ⟨_hZnonneg, hZ⟩⟩
  have hi : 0 < x.phiInitial := by
    rw [hphi]
    norm_num
  have hFpos : 0 < resource x.u x.eta x.B x.phiInitial t :=
    GSTStage11.resource_positive
      x.u x.eta x.B x.phiInitial t x.hB hi ht.le
  have hcl :
      (1 : ℝ) = max 0 (min 1
        ((resource x.u x.eta x.B x.phiInitial t * d x t) /
          (2 * (1 / 10)))) := by
    have hh := hclip t ht.le
    rw [hu, hU] at hh
    exact hh
  have hsaturation := GSTStage59.clipping_saturation_lower_bound
    (1 / 10) 1
    (resource x.u x.eta x.B x.phiInitial t * d x t)
    (by norm_num) (by norm_num) hcl
  have hd : d x t = p x t - z x t / 20 := by
    change x.c * p x t - x.eta * z x t =
      p x t - z x t / 20
    rw [hc, heta]
    ring
  rw [hd] at hsaturation
  have hsat :
      1 / 5 ≤ resource x.u x.eta x.B x.phiInitial t *
        (p x t - z x t / 20) := by
    nlinarith only [hsaturation]
  exact GSTStage162.candidate_saturated_maximum_bounds_impossible
    x t ha hc heta hrho hq hU htarget hi hclip
    ht hP hSt hFpos hFupper.le hF hZ hsat

end GSTStage163

#print axioms GSTStage163.fixed_candidate_S_nonpos
