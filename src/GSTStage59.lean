import GSTStage58
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage57

namespace GSTStage59

theorem clipping_saturation_lower_bound
    (r U w : ℝ)
    (hr : 0 < r) (hU : 0 < U)
    (hclip : U = max 0 (min U (w / (2 * r)))) :
    2 * r * U ≤ w := by
  have hden : 0 < 2 * r := by positivity
  have hle : U ≤ w / (2 * r) := by
    by_contra hn
    have hsmall : max 0 (min U (w / (2 * r))) < U :=
      max_lt hU
        (lt_of_le_of_lt (min_le_right _ _) (lt_of_not_ge hn))
    rw [← hclip] at hsmall
    exact (lt_irrefl U) hsmall
  have h := (le_div_iff₀ hden).mp hle
  nlinarith

theorem saturation_algebra_impossible
    (a q k target r U F P : ℝ)
    (ha : 0 < a) (hq : 0 < q)
    (hk : 0 < k) (hU : 0 < U)
    (hrThreshold : a * q * target ^ 2 / (4 * U ^ 2 * k) < r)
    (hcontrol : 2 * r * U ≤ F * P)
    (hstationary :
      2 * q * F * U = 2 * a * q * target - a * k * P) :
    False := by
  have hden : 0 < 4 * U ^ 2 * k := by positivity
  have hthreshold :=
    (div_lt_iff₀ hden).mp hrThreshold
  have hthresholdQ := mul_lt_mul_of_pos_left hthreshold hq
  have hfactor : 0 ≤ 2 * q * U * k := by positivity
  have hcontrolScaled :=
    mul_le_mul_of_nonneg_left hcontrol hfactor
  have hbalance :=
    congrArg (fun y : ℝ => y * (P * k)) hstationary
  have hsquare :
      0 ≤ a * (k * P - q * target) ^ 2 :=
    mul_nonneg ha.le (sq_nonneg _)
  nlinarith [hcontrolScaled, hbalance, hsquare, hthresholdQ]

theorem candidate_no_stationary_saturation
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hrThreshold :
      x.a * x.q * x.target ^ 2 /
        (4 * x.U ^ 2 * (x.rho + x.a)) < r)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 ≤ t)
    (hu : x.u t = x.U)
    (hstationary : sRate x t = 0) :
    False := by
  have hz : 0 ≤ z x t :=
    GSTStage44.candidate_z_nonneg x r hr hi hclip t ht
  have hphi : 0 ≤ resource x.u x.eta x.B x.phiInitial t :=
    (GSTStage11.resource_positive
      x.u x.eta x.B x.phiInitial t x.hB hi ht).le
  have hd : d x t ≤ x.c * p x t := by
    change x.c * p x t - x.eta * z x t ≤ x.c * p x t
    exact sub_le_self _ (mul_nonneg x.heta.le hz)
  have hclipAt := hclip t ht
  rw [hu] at hclipAt
  have hw := clipping_saturation_lower_bound
    r x.U
    (resource x.u x.eta x.B x.phiInitial t * d x t)
    hr hU hclipAt
  have hupper := mul_le_mul_of_nonneg_left hd hphi
  have hcontrol :
      2 * r * x.U ≤
        (x.c * resource x.u x.eta x.B x.phiInitial t) * p x t := by
    nlinarith [hw, hupper]
  have hbalance := GSTStage57.stationary_balance x t hstationary
  rw [hu] at hbalance
  have hstationary' :
      2 * x.q * (x.c * resource x.u x.eta x.B x.phiInitial t) * x.U =
        2 * x.a * x.q * x.target -
          x.a * (x.rho + x.a) * p x t := by
    nlinarith [hbalance]
  exact saturation_algebra_impossible
    x.a x.q (x.rho + x.a) x.target r x.U
    (x.c * resource x.u x.eta x.B x.phiInitial t) (p x t)
    ha hq (toCostateData x).hdecay hU
    hrThreshold hcontrol hstationary'

theorem candidate_no_local_maximum_at_saturation
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hrThreshold :
      x.a * x.q * x.target ^ 2 /
        (4 * x.U ^ 2 * (x.rho + x.a)) < r)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hu : x.u t = x.U)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    False := by
  exact candidate_no_stationary_saturation
    x r t hr hU hi ha hq hrThreshold hclip ht.le hu
    (GSTStage58.s_rate_zero_at_local_maximum x r t hclip ht hlocal)

#print axioms clipping_saturation_lower_bound
#print axioms saturation_algebra_impossible
#print axioms candidate_no_stationary_saturation
#print axioms candidate_no_local_maximum_at_saturation

end GSTStage59
