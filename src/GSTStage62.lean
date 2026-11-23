import GSTStage61
import Mathlib.Tactic.FieldSimp
open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage57 GSTStage60

namespace GSTStage62

theorem interior_balance
    (x : StateData) (r t : ℝ) (hr : 0 < r)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 ≤ t) (hu0 : 0 < x.u t) (huU : x.u t < x.U) :
    resource x.u x.eta x.B x.phiInitial t * d x t = 2 * r * x.u t := by
  have heq := GSTStage61.clipping_eq_input_of_interior
    x.U (w x t / (2 * r)) (x.u t) (hclip t ht) hu0 huU
  have hden : (2 : ℝ) * r ≠ 0 := ne_of_gt (by positivity)
  have h := (eq_div_iff hden).mp heq
  change x.u t * (2 * r) =
    resource x.u x.eta x.B x.phiInitial t * d x t at h
  nlinarith

theorem second_rate_algebra
    (a rho q c B eta r F D P O target u : ℝ)
    (hr : 0 < r) (hbalance : F * D = 2 * r * u) :
    a * (rho + a) * ((rho + a) * P + 2 * q * (O - target)) +
      2 * q * c * ((B - eta * u * F) * u +
        F * ((rho * (F * D) + B * D +
          c * F * (a * P + 2 * q * (O - target))) / (2 * r))) =
    rho * (a * (rho + a) * P - 2 * a * q * target + 2 * q * c * F * u) +
      (a * (rho + a) + q * c ^ 2 * F ^ 2 / r) *
        (a * P + 2 * q * (O - target)) +
      2 * a * q * rho * target - 2 * q * c * eta * F * u ^ 2 +
      4 * q * c * B * u := by
  have hcross := congrArg
    (fun y : ℝ => (q * c * (B + rho * F)) * y) hbalance
  field_simp [ne_of_gt hr]
  nlinarith [hcross]

noncomputable def secondRate (x : StateData) (r t : ℝ) : ℝ :=
  x.rho * sRate x t +
    (x.a * (x.rho + x.a) +
      x.q * x.c ^ 2 * (resource x.u x.eta x.B x.phiInitial t) ^ 2 / r) *
      S x t +
    2 * x.a * x.q * x.rho * x.target -
    2 * x.q * x.c * x.eta *
      resource x.u x.eta x.B x.phiInitial t * (x.u t) ^ 2 +
    4 * x.q * x.c * x.B * x.u t

theorem sRate_hasDerivAt_interior
    (x : StateData) (r t : ℝ) (hr : 0 < r)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t) (hu0 : 0 < x.u t) (huU : x.u t < x.U) :
    HasDerivAt (sRate x) (secondRate x r t) t := by
  let F := resource x.u x.eta x.B x.phiInitial
  have hp := GSTStage47.p_ode_at x t ht
  have hF := GSTStage60.resource_ode_at x r hclip t ht
  have hu := GSTStage61.candidate_control_hasDerivAt_interior
    x r t hclip ht hu0 huU
  have hraw :=
    ((hp.const_mul (x.a * (x.rho + x.a))).sub_const
      (2 * x.a * x.q * x.target)).add
      ((hF.mul hu).const_mul (2 * x.q * x.c))
  have hd : HasDerivAt (sRate x)
      (x.a * (x.rho + x.a) *
        ((x.rho + x.a) * p x t + 2 * x.q * (state x t - x.target)) +
      2 * x.q * x.c * ((x.B - x.eta * x.u t * F t) * x.u t +
        F t * ((x.rho * (F t * d x t) + x.B * d x t +
          x.c * F t * S x t) / (2 * r)))) t := by
    have hfun : sRate x =
        ((fun s => x.a * (x.rho + x.a) * p x s -
          2 * x.a * x.q * x.target) +
        (fun s => 2 * x.q * x.c *
          (resource x.u x.eta x.B x.phiInitial * x.u) s)) := by
      funext s
      simp only [sRate, Pi.add_apply, Pi.mul_apply]
      ring
    rw [hfun]
    exact hraw
  have heq := second_rate_algebra
    x.a x.rho x.q x.c x.B x.eta r (F t) (d x t)
    (p x t) (state x t) x.target (x.u t) hr
    (interior_balance x r t hr hclip ht.le hu0 huU)
  have heq' :
      x.a * (x.rho + x.a) *
        ((x.rho + x.a) * p x t + 2 * x.q * (state x t - x.target)) +
      2 * x.q * x.c * ((x.B - x.eta * x.u t * F t) * x.u t +
        F t * ((x.rho * (F t * d x t) + x.B * d x t +
          x.c * F t * S x t) / (2 * r))) = secondRate x r t := by
    simpa only [secondRate, sRate, GSTStage31.S,
      GSTStage18.canonicalS, F] using heq
  rw [heq'] at hd
  exact hd

#print axioms interior_balance
#print axioms second_rate_algebra
#print axioms sRate_hasDerivAt_interior
end GSTStage62
