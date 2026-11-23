import GSTStage144

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage57 GSTStage143

namespace GSTStage145

theorem fixed_positive_local_maximum_bounds
    (x : StateData) (t : ℝ)
    (ha : x.a = 1 / 10)
    (hc : x.c = 1)
    (heta : x.eta = 1 / 20)
    (hrho : x.rho = 1 / 20)
    (hq : x.q = 1)
    (hU : x.U = 1)
    (htarget : x.target = 1)
    (hi : 0 < x.phiInitial)
    (ho : 0 < x.omegaInitial)
    (hoTarget : x.omegaInitial < x.target)
    (hclip : GSTStage44.Clipping x (1 / 10))
    (ht : 0 < t)
    (hFpos : 0 < resource x.u x.eta x.B x.phiInitial t)
    (hS : 0 < S x t)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    let F := resource x.u x.eta x.B x.phiInitial t
    x.u t = 1 ∧
    F = 1 / 10 - 3 * p x t / 400 ∧
    (3 / 200 * S x t + 3 / 2000 * p x t -
      1 / 100 + 2 * x.B ≤ 0) ∧
    ((12 / 5 < p x t ∧ p x t < 20 / 3) ∧
      (1 / 20 < F ∧ F < 41 / 500) ∧
      (1 / 5 ≤ F * p x t ∧ F * p x t ≤ 1 / 3) ∧
      (0 ≤ z x t ∧ z x t ≤ 8 * p x t)) := by
  have hr : (0 : ℝ) < 1 / 10 := by norm_num
  have haPos : 0 < x.a := by rw [ha]; norm_num
  have hqPos : 0 < x.q := by rw [hq]; norm_num
  have hUPos : 0 < x.U := by rw [hU]; norm_num
  have hdiscount : x.eta * x.U ≤ x.rho := by
    rw [heta, hU, hrho]
    norm_num
  have hu := GSTStage141.positive_local_maximum_is_saturated
    x (1 / 10) t hr hi haPos hqPos ho hoTarget hdiscount
    hclip ht hS hlocal
  have hstationary := GSTStage58.s_rate_zero_at_local_maximum
    x (1 / 10) t hclip ht hlocal
  have hbalance := GSTStage57.stationary_balance x t hstationary
  rw [hu, hU, ha, hq, hc, htarget, hrho] at hbalance
  have hFeq :
      resource x.u x.eta x.B x.phiInitial t =
        1 / 10 - 3 * p x t / 400 := by
    nlinarith only [hbalance]
  have hsecond := GSTStage144.candidate_saturated_second_rate_nonpos
    x (1 / 10) t hr hUPos hclip ht hFpos hS hu hlocal
  have hsecondEq :
      saturatedSecondRate x t =
        3 / 200 * S x t + 3 / 2000 * p x t -
          1 / 100 + 2 * x.B := by
    dsimp only [saturatedSecondRate]
    rw [ha, hrho, hq, hc, heta, hU]
    simpa only [heta, one_mul, mul_one] using
      (GSTStage143.fixed_saturated_second_rate_identity
        (p x t) (S x t)
        (resource x.u x.eta x.B x.phiInitial t) x.B hFeq)
  rw [hsecondEq] at hsecond
  have hsigns := GSTStage56.canonical_signs
    x (1 / 10) hr hi haPos hqPos ho hoTarget hclip t ht.le
  have hclipped := hclip t ht.le
  rw [hu] at hclipped
  have hsat := GSTStage59.clipping_saturation_lower_bound
    (1 / 10) x.U
    (resource x.u x.eta x.B x.phiInitial t * d x t)
    hr hUPos hclipped
  have hd : d x t = p x t - z x t / 20 := by
    change x.c * p x t - x.eta * z x t = p x t - z x t / 20
    rw [hc, heta]
    ring
  rw [hU, hd] at hsat
  have hsaturation :
      1 / 5 ≤ resource x.u x.eta x.B x.phiInitial t *
        (p x t - z x t / 20) := by
    nlinarith only [hsat]
  have hbounds := GSTStage140.fixed_saturation_stationary_bounds
    (p x t) (S x t)
    (resource x.u x.eta x.B x.phiInitial t) (z x t) x.B
    hsigns.2.1 hS hFpos.le hsigns.1 x.hB hFeq hsecond hsaturation
  exact ⟨by simpa only [hU] using hu, hFeq, hsecond, hbounds⟩

end GSTStage145

#print axioms GSTStage145.fixed_positive_local_maximum_bounds
