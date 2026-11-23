import GSTStage95

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11

namespace GSTStage96

theorem resource_integral_balance
    (u : ℝ → ℝ) (eta B initial T : ℝ)
    (hT : 0 ≤ T)
    (hu : IntervalIntegrable u volume 0 T) :
    resource u eta B initial T =
      initial + B * T -
        eta * ∫ s in Icc (0 : ℝ) T,
          resource u eta B initial s * u s := by
  have hAC := GSTStage12.resource_ac u eta B initial T hu
  have hODE := GSTStage12.resource_ode_ae u eta B initial T hu
  have hp : IntervalIntegrable
      (fun s => resource u eta B initial s * u s) volume 0 T :=
    hu.continuousOn_mul (resource_continuousOn u eta B initial T hu)
  have hD : ∀ᵐ s : ℝ, s ∈ uIcc (0 : ℝ) T →
      HasDerivAt (resource u eta B initial)
        (B - eta * (resource u eta B initial s * u s)) s := by
    filter_upwards [hODE] with s hs
    intro hmem
    convert hs hmem using 1; ring
  have hFTC := GSTStage08.ac_integral_identity
    (resource u eta B initial)
    (fun s => B - eta * (resource u eta B initial s * u s))
    0 T hAC hD
  rw [intervalIntegral.integral_sub
        (intervalIntegrable_const) (hp.const_mul eta),
      intervalIntegral.integral_const_mul,
      resource_initial] at hFTC
  have hset :
      (∫ s in (0 : ℝ)..T, resource u eta B initial s * u s) =
        ∫ s in Icc (0 : ℝ) T, resource u eta B initial s * u s := by
    rw [intervalIntegral.integral_of_le hT,
        integral_Icc_eq_integral_Ioc]
  rw [hset] at hFTC
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hFTC
  nlinarith

theorem resource_limit_integral_balance
    (u : ℕ → ℝ → ℝ) (eta B initial : ℝ)
    (a Phi : ℝ → ℝ)
    (hu : ∀ n T, 0 ≤ T → IntervalIntegrable (u n) volume 0 T)
    (hstate : ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun n => resource (u n) eta B initial t)
        atTop (𝓝 (Phi t)))
    (hproduct : ∀ t : ℝ, 0 ≤ t →
      Tendsto
        (fun n => ∫ s in Icc (0 : ℝ) t,
          resource (u n) eta B initial s * u n s)
        atTop (𝓝 (∫ s in Icc (0 : ℝ) t, Phi s * a s))) :
    ∀ t : ℝ, 0 ≤ t →
      Phi t = initial + B * t -
        eta * ∫ s in Icc (0 : ℝ) t, Phi s * a s := by
  intro t ht
  have hright :
      Tendsto
        (fun n => initial + B * t -
          eta * ∫ s in Icc (0 : ℝ) t,
            resource (u n) eta B initial s * u n s)
        atTop
        (𝓝 (initial + B * t -
          eta * ∫ s in Icc (0 : ℝ) t, Phi s * a s)) :=
    (show Tendsto (fun _ : ℕ => initial + B * t)
      atTop (𝓝 (initial + B * t)) from tendsto_const_nhds).sub
      ((show Tendsto (fun _ : ℕ => eta)
        atTop (𝓝 eta) from tendsto_const_nhds).mul (hproduct t ht))
  have he (n : ℕ) :
      resource (u n) eta B initial t =
        initial + B * t -
          eta * ∫ s in Icc (0 : ℝ) t,
            resource (u n) eta B initial s * u n s :=
    resource_integral_balance (u n) eta B initial t ht (hu n t ht)
  have hleft := (hstate t ht).congr' (Filter.Eventually.of_forall he)
  exact tendsto_nhds_unique hleft hright

end GSTStage96

#print axioms GSTStage96.resource_integral_balance
#print axioms GSTStage96.resource_limit_integral_balance
