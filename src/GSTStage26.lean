import GSTStage12
import GSTStage22
import GSTStage25
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage22 GSTStage25

namespace GSTStage26

noncomputable def pInput
    (omega : ℝ → ℝ) (rho a target s : ℝ) : ℝ :=
  Real.exp (-(rho + a) * s) * (target - omega s)

-- Integrability follows from the already proved estimate in stage22.
theorem p_input_integrable
    (omega : ℝ → ℝ) (rho a q target M : ℝ)
    (hdecay : 0 < rho + a) (hM : 0 ≤ M)
    (hcont : ContinuousOn omega (Ici (0 : ℝ)))
    (hOmega : ∀ t : ℝ, 0 ≤ t → |omega t| ≤ M * (1 + t)) :
    IntegrableOn (pInput omega rho a target) (Ioi (0 : ℝ)) := by
  simpa only [pInput, sub_zero] using
    (p_integrable_and_bound omega rho a q target M 0
      hdecay hM (le_refl 0) hcont hOmega).1

-- Exact identity for the original integral definition of p.
theorem p_weighted_tail
    (omega : ℝ → ℝ) (rho a q target t : ℝ) :
    pCostate omega rho a q target t =
      2 * q * (Real.exp ((rho + a) * t) *
        tail (pInput omega rho a target) t) := by
  have hfactor : ∀ s : ℝ,
      Real.exp (-(rho + a) * (s - t)) * (target - omega s) =
        Real.exp ((rho + a) * t) * pInput omega rho a target s := by
    intro s
    unfold pInput
    rw [show -(rho + a) * (s - t) =
      (rho + a) * t + (-(rho + a) * s) by ring, Real.exp_add]
    ring
  unfold pCostate tail
  simp_rw [hfactor]
  rw [integral_const_mul]

theorem p_ac_of_input_integrable
    (omega : ℝ → ℝ) (rho a q target T : ℝ)
    (hT : 0 ≤ T)
    (hg : IntegrableOn (pInput omega rho a target) (Ioi (0 : ℝ))) :
    AbsolutelyContinuousOnInterval
      (pCostate omega rho a q target) 0 T := by
  have hconstInt :
      IntervalIntegrable (fun _ : ℝ => rho + a) volume 0 T :=
    intervalIntegrable_const
  have hlinear :
      AbsolutelyContinuousOnInterval
        (fun t : ℝ => (rho + a) * t) 0 T := by
    have h := hconstInt.absolutelyContinuousOnInterval_intervalIntegral
      (show (0 : ℝ) ∈ uIcc (0 : ℝ) T by simp)
    simpa only [
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm
    ] using h
  have hexp :
      AbsolutelyContinuousOnInterval
        (fun t : ℝ => Real.exp ((rho + a) * t)) 0 T := by
    apply GSTStage12.exp_ac
    exact hlinear
  have htail := tail_ac (pInput omega rho a target) T hg hT
  have hproduct := (hexp.fun_mul htail).const_mul (2 * q)
  have heq : pCostate omega rho a q target =
      (fun t : ℝ => 2 * q * (Real.exp ((rho + a) * t) *
        tail (pInput omega rho a target) t)) :=
    funext (fun t => p_weighted_tail omega rho a q target t)
  rw [heq]
  exact hproduct

-- The costate ODE is derived, not assumed.
theorem p_ode_ae_of_input_integrable
    (omega : ℝ → ℝ) (rho a q target T : ℝ)
    (hT : 0 ≤ T)
    (hg : IntegrableOn (pInput omega rho a target) (Ioi (0 : ℝ))) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (pCostate omega rho a q target)
        ((rho + a) * pCostate omega rho a q target t +
          2 * q * (omega t - target)) t := by
  have heq : pCostate omega rho a q target =
      (fun t : ℝ => 2 * q * (Real.exp ((rho + a) * t) *
        tail (pInput omega rho a target) t)) :=
    funext (fun t => p_weighted_tail omega rho a q target t)
  filter_upwards [
    tail_derivative_ae (pInput omega rho a target) T hg hT
  ] with t hd
  intro ht
  have he :
      HasDerivAt (fun x : ℝ => Real.exp ((rho + a) * x))
        (Real.exp ((rho + a) * t) * (rho + a)) t := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id t).const_mul (rho + a)).exp
  have hcancel :
      Real.exp ((rho + a) * t) * pInput omega rho a target t =
        target - omega t := by
    unfold pInput
    rw [← mul_assoc, ← Real.exp_add]
    have hz : (rho + a) * t + (-(rho + a) * t) = 0 := by ring
    simp only [hz, Real.exp_zero, one_mul]
  have hproduct := (he.mul (hd ht)).const_mul (2 * q)
  rw [heq]
  convert hproduct using 1
  dsimp only [Pi.mul_apply]
  rw [mul_neg, hcancel]
  ring

-- Combined statement under the same state assumptions used in stage22.
theorem p_is_costate_solution
    (omega : ℝ → ℝ) (rho a q target M T : ℝ)
    (hdecay : 0 < rho + a) (hM : 0 ≤ M) (hT : 0 ≤ T)
    (hcont : ContinuousOn omega (Ici (0 : ℝ)))
    (hOmega : ∀ t : ℝ, 0 ≤ t → |omega t| ≤ M * (1 + t)) :
    AbsolutelyContinuousOnInterval
      (pCostate omega rho a q target) 0 T ∧
    (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (pCostate omega rho a q target)
        ((rho + a) * pCostate omega rho a q target t +
          2 * q * (omega t - target)) t) := by
  have hg := p_input_integrable omega rho a q target M
    hdecay hM hcont hOmega
  exact ⟨
    p_ac_of_input_integrable omega rho a q target T hT hg,
    p_ode_ae_of_input_integrable omega rho a q target T hT hg
  ⟩

#print axioms p_input_integrable
#print axioms p_weighted_tail
#print axioms p_ac_of_input_integrable
#print axioms p_ode_ae_of_input_integrable
#print axioms p_is_costate_solution

end GSTStage26
