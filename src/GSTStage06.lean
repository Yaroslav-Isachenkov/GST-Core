import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring

namespace GSTStage06

def runningCost (q r target omega u : ℝ) : ℝ :=
  q * (omega - target)^2 + r * u^2

-- Exact discounted boundary derivative.
-- o,f: competing trajectory; oc,fs: candidate trajectory.
-- u,v: corresponding control values at the point t.
-- p,z: candidate costates.
--
-- This is a pointwise identity, not yet an infinite-horizon theorem.
theorem objective_boundary_identity
    (o oc f fs p z : ℝ → ℝ)
    (t a c eta B rho q r target u v : ℝ)
    (ho : HasDerivAt o (-a * o t + c * f t * u) t)
    (hoc : HasDerivAt oc (-a * oc t + c * fs t * v) t)
    (hf : HasDerivAt f (B - eta * f t * u) t)
    (hfs : HasDerivAt fs (B - eta * fs t * v) t)
    (hp : HasDerivAt p
      ((rho + a) * p t + 2 * q * (oc t - target)) t)
    (hz : HasDerivAt z
      ((rho + eta * v) * z t - c * v * p t) t) :
    HasDerivAt
      (fun s => Real.exp (-rho * s) *
        (p s * (o s - oc s) + z s * (f s - fs s)))
      (Real.exp (-rho * t) *
        (runningCost q r target (o t) u
          - runningCost q r target (oc t) v
          - q * (o t - oc t)^2
          - r * (u - v)^2
          + (-2 * r * v + fs t * (c * p t - eta * z t)) * (u - v)
          + (c * p t - eta * z t) * (f t - fs t) * (u - v))) t := by
  have he := ((hasDerivAt_id t).const_mul (-rho)).exp
  have hb := (hp.mul (ho.sub hoc)).add (hz.mul (hf.sub hfs))
  convert he.mul hb using 1
  all_goals
    dsimp [runningCost]
    ring

-- The variational sign in the three control regimes.
-- Derivation of these regimes from the clipping rule remains separate.
theorem stationarity_from_regimes
    (r U w u v : ℝ)
    (hu0 : 0 ≤ u) (huU : u ≤ U)
    (hreg :
      (v = 0 ∧ w ≤ 0) ∨
      (w = 2 * r * v) ∨
      (v = U ∧ 2 * r * U ≤ w)) :
    (-2 * r * v + w) * (u - v) ≤ 0 := by
  rcases hreg with hzero | hmiddle | hupper
  · rcases hzero with ⟨hv, hw⟩
    subst v
    simpa using mul_nonpos_of_nonpos_of_nonneg hw hu0
  · rw [hmiddle]
    ring_nf
    exact le_refl 0
  · rcases hupper with ⟨hv, hw⟩
    subst v
    have hw0 : 0 ≤ -2 * r * U + w := by
      have h := sub_nonneg.mpr hw
      convert h using 1
      ring
    exact mul_nonpos_of_nonneg_of_nonpos hw0 (sub_nonpos.mpr huU)

#print axioms objective_boundary_identity
#print axioms stationarity_from_regimes

end GSTStage06
