import GSTStage62
open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage57 GSTStage62

namespace GSTStage63

theorem stationary_second_rate_positive
    (a rho q c B eta r F P target u s : ℝ)
    (ha : 0 < a) (hrho : 0 < rho) (hq : 0 < q)
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hr : 0 < r)
    (hF : 0 ≤ F) (hP : 0 < P) (hu : 0 ≤ u)
    (hs : 0 < s) (hdiscount : eta * u ≤ rho)
    (hstationary :
      2 * q * c * F * u = 2 * a * q * target - a * (rho + a) * P) :
    0 <
      (a * (rho + a) + q * c ^ 2 * F ^ 2 / r) * s +
      2 * a * q * rho * target - 2 * q * c * eta * F * u ^ 2 +
      4 * q * c * B * u := by
  have hk : 0 < rho + a := add_pos hrho ha
  have hPterm : 0 < a * (rho + a) * P :=
    mul_pos (mul_pos ha hk) hP
  have hflux : c * F * u < a * target := by
    nlinarith [hstationary, hPterm]
  have hflux0 : 0 ≤ c * F * u :=
    mul_nonneg (mul_nonneg hc hF) hu
  have hscaled := mul_lt_mul_of_pos_left hflux hrho
  have hcontrolled :=
    mul_le_mul_of_nonneg_right hdiscount hflux0
  have hmain : 0 < a * rho * target - c * eta * F * u ^ 2 := by
    nlinarith [hscaled, hcontrolled]
  have hq2 : 0 < 2 * q := by positivity
  have htail := mul_pos hq2 hmain
  have hextra : 0 ≤ q * c ^ 2 * F ^ 2 / r := by positivity
  have hcoefficient : 0 < a * (rho + a) + q * c ^ 2 * F ^ 2 / r :=
    add_pos_of_pos_of_nonneg (mul_pos ha hk) hextra
  have hfirst := mul_pos hcoefficient hs
  have hlast : 0 ≤ 4 * q * c * B * u := by positivity
  nlinarith [hfirst, htail, hlast]

theorem candidate_secondRate_positive
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hoTarget : x.omegaInitial < x.target)
    (hdiscount : x.eta * x.U ≤ x.rho)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 ≤ t) (hS : 0 < S x t)
    (hstationary : sRate x t = 0) :
    0 < secondRate x r t := by
  have hp : 0 < p x t :=
    GSTStage52.candidate_p_positive
      x r hr hi ha hq hoTarget hclip t ht
  have hF : 0 ≤ resource x.u x.eta x.B x.phiInitial t :=
    GSTStage30.resource_nonneg
      x.u x.eta x.B x.phiInitial t x.hB x.hphiInitial ht
  have hbound := x.hu t ht
  have hdiscountAt : x.eta * x.u t ≤ x.rho :=
    le_trans (mul_le_mul_of_nonneg_left hbound.2 x.heta.le) hdiscount
  have hbalance := GSTStage57.stationary_balance x t hstationary
  have hpositive := stationary_second_rate_positive
    x.a x.rho x.q x.c x.B x.eta r
    (resource x.u x.eta x.B x.phiInitial t)
    (p x t) x.target (x.u t) (S x t)
    ha x.hrho hq x.hc x.hB hr hF hp hbound.1 hS hdiscountAt hbalance
  simpa only [secondRate, hstationary, mul_zero, zero_add] using hpositive

theorem candidate_sRate_derivative_positive_interior
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hoTarget : x.omegaInitial < x.target)
    (hdiscount : x.eta * x.U ≤ x.rho)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t) (hu0 : 0 < x.u t) (huU : x.u t < x.U)
    (hS : 0 < S x t) (hstationary : sRate x t = 0) :
    HasDerivAt (sRate x) (secondRate x r t) t ∧
      0 < secondRate x r t := by
  exact ⟨GSTStage62.sRate_hasDerivAt_interior
    x r t hr hclip ht hu0 huU,
    candidate_secondRate_positive
      x r t hr hi ha hq hoTarget hdiscount hclip ht.le hS hstationary⟩

#print axioms stationary_second_rate_positive
#print axioms candidate_secondRate_positive
#print axioms candidate_sRate_derivative_positive_interior
end GSTStage63
