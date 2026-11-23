import GSTStage16

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage12 GSTStage15 GSTStage16

namespace GSTStage17

theorem remainder_continuous
    (phi psi d S : ℝ → ℝ) (rho c B T : ℝ)
    (hp : ContinuousOn phi (uIcc (0 : ℝ) T))
    (hq : ContinuousOn psi (uIcc (0 : ℝ) T))
    (hd : ContinuousOn d (uIcc (0 : ℝ) T))
    (hS : ContinuousOn S (uIcc (0 : ℝ) T))
    (hpp : ∀ t ∈ uIcc (0 : ℝ) T, 0 < phi t)
    (hqp : ∀ t ∈ uIcc (0 : ℝ) T, 0 < psi t) :
    ContinuousOn (remainder phi psi d S rho c B)
      (uIcc (0 : ℝ) T) := by
  have hr : ContinuousOn (fun t => phi t / psi t)
      (uIcc (0 : ℝ) T) :=
    hp.div hq (fun t ht => ne_of_gt (hqp t ht))
  have hn : ∀ t ∈ uIcc (0 : ℝ) T, phi t / psi t ≠ 0 := by
    intro t ht
    exact ne_of_gt (div_pos (hpp t ht) (hqp t ht))
  have hl := hr.log hn
  have hi := hr.inv₀ hn
  have hF : ContinuousOn
      (fun t => phi t / psi t - 1 - Real.log (phi t / psi t))
      (uIcc (0 : ℝ) T) :=
    (hr.sub continuousOn_const).sub hl
  have hG : ContinuousOn
      (fun t => Real.log (phi t / psi t) + (phi t / psi t)⁻¹ - 1)
      (uIcc (0 : ℝ) T) :=
    (hl.add hi).sub continuousOn_const
  have hleft : ContinuousOn
      (fun t => c * psi t * S t *
        (phi t / psi t - 1 - Real.log (phi t / psi t)))
      (uIcc (0 : ℝ) T) :=
    ((continuousOn_const.mul hq).mul hS).mul hF
  have hright : ContinuousOn
      (fun t => B * d t *
        (Real.log (phi t / psi t) + (phi t / psi t)⁻¹ - 1))
      (uIcc (0 : ℝ) T) :=
    (continuousOn_const.mul hd).mul hG
  exact (discount_ac rho T).continuousOn.mul (hleft.sub hright)

theorem mixed_integrable
    (phi psi d u v : ℝ → ℝ) (rho T : ℝ)
    (hp : ContinuousOn phi (uIcc (0 : ℝ) T))
    (hq : ContinuousOn psi (uIcc (0 : ℝ) T))
    (hd : ContinuousOn d (uIcc (0 : ℝ) T))
    (hu : IntervalIntegrable u volume 0 T)
    (hv : IntervalIntegrable v volume 0 T) :
    IntervalIntegrable (mixed phi psi d u v rho) volume 0 T := by
  have hweight : ContinuousOn
      (fun t => Real.exp (-rho * t) * d t * (phi t - psi t))
      (uIcc (0 : ℝ) T) :=
    ((discount_ac rho T).continuousOn.mul hd).mul (hp.sub hq)
  have hint := (hu.sub hv).continuousOn_mul hweight
  simpa only [mixed, Pi.sub_apply] using hint

-- The two integrability hypotheses from stage16 are now derived.
-- Continuity of S and the hypotheses concerning d remain explicit.
theorem finite_mixed_nonpos
    (u v d S : ℝ → ℝ) (eta B initial rho c T : ℝ)
    (hT : 0 ≤ T) (heta : 0 < eta)
    (hB : 0 ≤ B) (hi : 0 < initial) (hc : 0 ≤ c)
    (hu : IntervalIntegrable u volume 0 T)
    (hv : IntervalIntegrable v volume 0 T)
    (hdAC : AbsolutelyContinuousOnInterval d 0 T)
    (hScont : ContinuousOn S (uIcc (0 : ℝ) T))
    (hdODE : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt d ((rho + eta * v t) * d t + c * S t) t)
    (hdpos : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ d t)
    (hS : ∀ t ∈ Icc (0 : ℝ) T, S t ≤ 0) :
    (∫ t in (0 : ℝ)..T,
      mixed (resource u eta B initial)
        (resource v eta B initial) d u v rho t) ≤ 0 := by
  have hp := resource_continuousOn u eta B initial T hu
  have hq := resource_continuousOn v eta B initial T hv
  have hpp : ∀ t ∈ uIcc (0 : ℝ) T,
      0 < resource u eta B initial t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact resource_positive u eta B initial t hB hi ht.1
  have hqp : ∀ t ∈ uIcc (0 : ℝ) T,
      0 < resource v eta B initial t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact resource_positive v eta B initial t hB hi ht.1
  have hR := remainder_continuous
    (resource u eta B initial) (resource v eta B initial)
    d S rho c B T hp hq hdAC.continuousOn hScont hpp hqp
  have hm := mixed_integrable
    (resource u eta B initial) (resource v eta B initial)
    d u v rho T hp hq hdAC.continuousOn hu hv
  exact resource_mixed_integral_nonpos
    u v d S eta B initial rho c T
    hT heta hB hi hc hu hv hdAC hdODE hdpos hS
    hR.intervalIntegrable hm

#print axioms remainder_continuous
#print axioms mixed_integrable
#print axioms finite_mixed_nonpos

end GSTStage17
