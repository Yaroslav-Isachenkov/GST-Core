import GSTStage56

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage57

-- Right-hand side of equation (20) in the source document.
noncomputable def sRate (x : StateData) (t : ℝ) : ℝ :=
  x.a * (x.rho + x.a) * p x t -
    2 * x.a * x.q * x.target +
    2 * x.q * x.c *
      resource x.u x.eta x.B x.phiInitial t * x.u t

theorem s_hasDerivAt
    (x : StateData) (r : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (S x) (sRate x t) t := by
  have hp := GSTStage47.p_ode_at x t ht
  have ho := GSTStage47.state_ode_at x r hclip t ht
  have h :=
    (hp.const_mul x.a).add
      ((ho.sub_const x.target).const_mul (2 * x.q))
  convert h using 1
  dsimp [GSTStage31.S, GSTStage18.canonicalS, sRate]
  ring

-- An algebraic form without division by q.
theorem stationary_balance
    (x : StateData) (t : ℝ)
    (hstationary : sRate x t = 0) :
    2 * x.q * x.c *
        resource x.u x.eta x.B x.phiInitial t * x.u t =
      2 * x.a * x.q * x.target -
        x.a * (x.rho + x.a) * p x t := by
  dsimp [sRate] at hstationary
  linarith

-- The strict upper bound on p excludes a zero rate at u = 0.
-- This estimate itself does not require clipping.
theorem s_rate_negative_of_control_zero
    (x : StateData)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (t : ℝ) (ht : 0 ≤ t)
    (hu : x.u t = 0) :
    sRate x t < 0 := by
  have hk : 0 < x.rho + x.a := (toCostateData x).hdecay
  have hp := GSTStage45.p_strict_upper x hq ho t ht
  have hscaled :
      p x t * (x.rho + x.a) < 2 * x.q * x.target :=
    (lt_div_iff₀ hk).mp hp
  have hmul := mul_lt_mul_of_pos_left hscaled ha
  dsimp [sRate]
  rw [hu]
  nlinarith

#print axioms s_hasDerivAt
#print axioms stationary_balance
#print axioms s_rate_negative_of_control_zero

end GSTStage57
