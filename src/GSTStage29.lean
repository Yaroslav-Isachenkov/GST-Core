import GSTStage14
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage29

noncomputable def weightedInput
    (f : ℝ → ℝ) (a t : ℝ) : ℝ :=
  Real.exp (a * t) * f t

noncomputable def linearState
    (f : ℝ → ℝ) (a initial t : ℝ) : ℝ :=
  Real.exp (-a * t) *
    (initial + ∫ s in (0 : ℝ)..t, weightedInput f a s)

theorem weighted_input_integrable
    (f : ℝ → ℝ) (a T : ℝ)
    (hf : IntervalIntegrable f volume 0 T) :
    IntervalIntegrable (weightedInput f a) volume 0 T := by
  have he : ContinuousOn (fun t : ℝ => Real.exp (a * t))
      (uIcc (0 : ℝ) T) :=
    (continuous_const.mul continuous_id).rexp.continuousOn
  exact hf.continuousOn_mul he

theorem linear_state_initial
    (f : ℝ → ℝ) (a initial : ℝ) :
    linearState f a initial 0 = initial := by
  simp [linearState]

theorem linear_state_ac
    (f : ℝ → ℝ) (a initial T : ℝ)
    (hf : IntervalIntegrable f volume 0 T) :
    AbsolutelyContinuousOnInterval (linearState f a initial) 0 T := by
  have hlin : AbsolutelyContinuousOnInterval
      (fun t : ℝ => -a * t) 0 T := by
    have h :=
      GSTStage11.cumulative_ac (fun _ : ℝ => (1 : ℝ)) (-a) T
        intervalIntegrable_const
    change AbsolutelyContinuousOnInterval
      (fun t : ℝ => -a * ∫ s in (0 : ℝ)..t, (1 : ℝ)) 0 T at h
    simpa using h
  have he : AbsolutelyContinuousOnInterval
      (fun t : ℝ => Real.exp (-a * t)) 0 T :=
    GSTStage12.exp_ac (fun t : ℝ => -a * t) 0 T hlin
  have hi : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in (0 : ℝ)..t, weightedInput f a s) 0 T :=
    (weighted_input_integrable f a T hf).absolutelyContinuousOnInterval_intervalIntegral
      left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => initial) 0 T := by
    simp only [AbsolutelyContinuousOnInterval,
      dist_self, Finset.sum_const_zero]
    exact tendsto_const_nhds
  exact he.mul (hc.fun_add hi)

theorem linear_state_ode_ae
    (f : ℝ → ℝ) (a initial T : ℝ)
    (hf : IntervalIntegrable f volume 0 T) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (linearState f a initial)
        (-a * linearState f a initial t + f t) t := by
  have hi := weighted_input_integrable f a T hf
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht
  intro hmem
  have hp := ht hmem 0 left_mem_uIcc
  have he := ((hasDerivAt_id t).const_mul (-a)).exp
  have hd :
      HasDerivAt (linearState f a initial)
        (Real.exp (-a * t) * (-a) *
            (initial + ∫ s in (0 : ℝ)..t, weightedInput f a s)
          + Real.exp (-a * t) * (Real.exp (a * t) * f t)) t := by
    simpa only [linearState, weightedInput, Pi.mul_apply,
      id_eq, mul_one] using he.mul (hp.const_add initial)
  have hexp : Real.exp (-a * t) * Real.exp (a * t) = 1 := by
    rw [← Real.exp_add]
    have hz : -a * t + a * t = 0 := by ring
    rw [hz, Real.exp_zero]
  have hcancel :
      Real.exp (-a * t) * (Real.exp (a * t) * f t) = f t := by
    rw [← mul_assoc, hexp, one_mul]
  convert hd using 1
  dsimp only [linearState]
  nlinarith only [hcancel]

noncomputable def resourceForcing
    (u : ℝ → ℝ) (eta B phiInitial c t : ℝ) : ℝ :=
  c * (GSTStage11.resource u eta B phiInitial t * u t)

noncomputable def omega
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial t : ℝ) : ℝ :=
  linearState (resourceForcing u eta B phiInitial c) a omegaInitial t

theorem resource_forcing_integrable
    (u : ℝ → ℝ) (eta B phiInitial c T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    IntervalIntegrable (resourceForcing u eta B phiInitial c)
      volume 0 T := by
  have hr := GSTStage11.resource_continuousOn
    u eta B phiInitial T hu
  exact (hu.continuousOn_mul hr).const_mul c

theorem omega_initial
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial : ℝ) :
    omega u eta B phiInitial a c omegaInitial 0 = omegaInitial := by
  exact linear_state_initial
    (resourceForcing u eta B phiInitial c) a omegaInitial

theorem omega_solution
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    AbsolutelyContinuousOnInterval
        (omega u eta B phiInitial a c omegaInitial) 0 T ∧
      (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt (omega u eta B phiInitial a c omegaInitial)
          (-a * omega u eta B phiInitial a c omegaInitial t
            + c * (GSTStage11.resource u eta B phiInitial t * u t)) t) := by
  have hf := resource_forcing_integrable u eta B phiInitial c T hu
  exact ⟨
    linear_state_ac (resourceForcing u eta B phiInitial c)
      a omegaInitial T hf,
    linear_state_ode_ae (resourceForcing u eta B phiInitial c)
      a omegaInitial T hf
  ⟩

-- Uses the same measurable, a.e.-bounded control class as stage14.
theorem admissible_omega_solution
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial U T : ℝ)
    (hT : 0 ≤ T)
    (hmeas : Measurable u)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      0 ≤ u t ∧ u t ≤ U) :
    omega u eta B phiInitial a c omegaInitial 0 = omegaInitial ∧
      AbsolutelyContinuousOnInterval
        (omega u eta B phiInitial a c omegaInitial) 0 T ∧
      (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt (omega u eta B phiInitial a c omegaInitial)
          (-a * omega u eta B phiInitial a c omegaInitial t
            + c * (GSTStage11.resource u eta B phiInitial t * u t)) t) := by
  have hu := GSTStage14.admissible_control_integrable
    u U T hT hmeas hbound
  exact ⟨omega_initial u eta B phiInitial a c omegaInitial,
    omega_solution u eta B phiInitial a c omegaInitial T hu⟩

#print axioms weighted_input_integrable
#print axioms linear_state_initial
#print axioms linear_state_ac
#print axioms linear_state_ode_ae
#print axioms resource_forcing_integrable
#print axioms omega_initial
#print axioms omega_solution
#print axioms admissible_omega_solution

end GSTStage29
