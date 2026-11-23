import GSTStage142

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage57

namespace GSTStage143

noncomputable def saturatedSecondRate (x : StateData) (t : ℝ) : ℝ :=
  x.a * (x.rho + x.a) * (x.rho * p x t + S x t) +
    2 * x.q * x.c *
      (x.B - x.eta * x.U *
        resource x.u x.eta x.B x.phiInitial t) * x.U

theorem sRate_hasDerivWithinAt_saturated_right
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t)
    (hF : 0 < resource x.u x.eta x.B x.phiInitial t)
    (hS : 0 < S x t)
    (hu : x.u t = x.U) :
    HasDerivWithinAt (sRate x) (saturatedSecondRate x t) (Ioi t) t := by
  have hp : HasDerivWithinAt (p x)
      ((x.rho + x.a) * p x t +
        2 * x.q * (state x t - x.target)) (Ioi t) t :=
    (GSTStage47.p_ode_at x t ht).hasDerivWithinAt
  have hres : HasDerivWithinAt
      (resource x.u x.eta x.B x.phiInitial)
      (x.B - x.eta * x.u t *
        resource x.u x.eta x.B x.phiInitial t) (Ioi t) t :=
    (GSTStage60.resource_ode_at x r hclip t ht).hasDerivWithinAt
  have hcontrol := GSTStage142.candidate_control_hasDerivWithinAt_zero_right
    x r t hr hU hclip ht hF hS hu
  have hraw :=
    ((hp.const_mul (x.a * (x.rho + x.a))).sub_const
      (2 * x.a * x.q * x.target)).add
      ((hres.mul hcontrol).const_mul (2 * x.q * x.c))
  have hfun : sRate x =
      ((fun s => x.a * (x.rho + x.a) * p x s -
        2 * x.a * x.q * x.target) +
      (fun s => 2 * x.q * x.c *
        (resource x.u x.eta x.B x.phiInitial * x.u) s)) := by
    funext s
    simp only [sRate, Pi.add_apply, Pi.mul_apply]
    ring
  have hd : HasDerivWithinAt (sRate x)
      (x.a * (x.rho + x.a) *
        ((x.rho + x.a) * p x t +
          2 * x.q * (state x t - x.target)) +
        2 * x.q * x.c *
          ((x.B - x.eta * x.u t *
            resource x.u x.eta x.B x.phiInitial t) * x.u t +
            resource x.u x.eta x.B x.phiInitial t * 0))
      (Ioi t) t := by
    rw [hfun]
    exact hraw
  have heq :
      x.a * (x.rho + x.a) *
        ((x.rho + x.a) * p x t +
          2 * x.q * (state x t - x.target)) +
        2 * x.q * x.c *
          ((x.B - x.eta * x.u t *
            resource x.u x.eta x.B x.phiInitial t) * x.u t +
            resource x.u x.eta x.B x.phiInitial t * 0) =
      saturatedSecondRate x t := by
    rw [hu]
    dsimp only [saturatedSecondRate, GSTStage31.S,
      GSTStage18.canonicalS]
    ring
  rw [heq] at hd
  exact hd

theorem fixed_saturated_second_rate_identity
    (P M F B : ℝ)
    (hF : F = 1 / 10 - 3 * P / 400) :
    (1 / 10 : ℝ) * (1 / 20 + 1 / 10) * (1 / 20 * P + M) +
        2 * (B - 1 / 20 * F) =
      3 / 200 * M + 3 / 2000 * P - 1 / 100 + 2 * B := by
  rw [hF]
  ring

end GSTStage143

#print axioms GSTStage143.sRate_hasDerivWithinAt_saturated_right
#print axioms GSTStage143.fixed_saturated_second_rate_identity
