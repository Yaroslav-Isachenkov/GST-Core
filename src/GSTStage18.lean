import GSTStage17
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage16 GSTStage17

namespace GSTStage18

noncomputable def canonicalD
    (p z : ℝ → ℝ) (c eta t : ℝ) : ℝ :=
  c * p t - eta * z t

noncomputable def canonicalS
    (p omega : ℝ → ℝ) (a q target t : ℝ) : ℝ :=
  a * p t + 2 * q * (omega t - target)

theorem canonicalD_ac
    (p z : ℝ → ℝ) (c eta T : ℝ)
    (hp : AbsolutelyContinuousOnInterval p 0 T)
    (hz : AbsolutelyContinuousOnInterval z 0 T) :
    AbsolutelyContinuousOnInterval (canonicalD p z c eta) 0 T := by
  exact (hp.const_mul c).fun_sub (hz.const_mul eta)

theorem canonicalS_continuous
    (p omega : ℝ → ℝ) (a q target T : ℝ)
    (hp : ContinuousOn p (uIcc (0 : ℝ) T))
    (ho : ContinuousOn omega (uIcc (0 : ℝ) T)) :
    ContinuousOn (canonicalS p omega a q target)
      (uIcc (0 : ℝ) T) := by
  have hleft : ContinuousOn (fun t => a * p t)
      (uIcc (0 : ℝ) T) :=
    continuousOn_const.mul hp
  have hright : ContinuousOn (fun t => 2 * q * (omega t - target))
      (uIcc (0 : ℝ) T) :=
    continuousOn_const.mul (ho.sub continuousOn_const)
  exact hleft.add hright

theorem canonicalD_ode_ae
    (p z omega v : ℝ → ℝ) (a c eta rho q target T : ℝ)
    (hpODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt p
        ((rho + a) * p t + 2 * q * (omega t - target)) t)
    (hzODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt z
        ((rho + eta * v t) * z t - c * v t * p t) t) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (canonicalD p z c eta)
        ((rho + eta * v t) * canonicalD p z c eta t
          + c * canonicalS p omega a q target t) t := by
  filter_upwards [hpODE, hzODE] with t hp hz
  intro ht
  have h := ((hp ht).const_mul c).sub ((hz ht).const_mul eta)
  convert h using 1
  dsimp [canonicalD, canonicalS]
  ring

-- Finite-interval inequality expressed in canonical variables.
-- The signs of D and S remain explicit hypotheses.
theorem canonical_finite_mixed_nonpos
    (u v p z omega : ℝ → ℝ)
    (a c eta rho q target B initial T : ℝ)
    (hT : 0 ≤ T) (heta : 0 < eta)
    (hB : 0 ≤ B) (hi : 0 < initial) (hc : 0 ≤ c)
    (hu : IntervalIntegrable u volume 0 T)
    (hv : IntervalIntegrable v volume 0 T)
    (hpAC : AbsolutelyContinuousOnInterval p 0 T)
    (hzAC : AbsolutelyContinuousOnInterval z 0 T)
    (ho : ContinuousOn omega (uIcc (0 : ℝ) T))
    (hpODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt p
        ((rho + a) * p t + 2 * q * (omega t - target)) t)
    (hzODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt z
        ((rho + eta * v t) * z t - c * v t * p t) t)
    (hD : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ canonicalD p z c eta t)
    (hS : ∀ t ∈ Icc (0 : ℝ) T,
      canonicalS p omega a q target t ≤ 0) :
    (∫ t in (0 : ℝ)..T,
      mixed (resource u eta B initial)
        (resource v eta B initial)
        (canonicalD p z c eta) u v rho t) ≤ 0 := by
  exact finite_mixed_nonpos
    u v (canonicalD p z c eta)
    (canonicalS p omega a q target)
    eta B initial rho c T
    hT heta hB hi hc hu hv
    (canonicalD_ac p z c eta T hpAC hzAC)
    (canonicalS_continuous p omega a q target T hpAC.continuousOn ho)
    (canonicalD_ode_ae p z omega v a c eta rho q target T hpODE hzODE)
    hD hS

#print axioms canonicalD_ac
#print axioms canonicalS_continuous
#print axioms canonicalD_ode_ae
#print axioms canonical_finite_mixed_nonpos

end GSTStage18
