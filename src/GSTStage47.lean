import GSTStage46
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage47

-- Local AC and an a.e. ODE with continuous RHS give the ODE at t > 0.
theorem hasDerivAt_of_local_ac_ae
    (f D : ℝ → ℝ)
    (hf : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval f 0 T)
    (hode : ∀ T : ℝ, 0 ≤ T →
      ∀ᵐ s : ℝ, s ∈ uIcc (0 : ℝ) T → HasDerivAt f (D s) s)
    (hcont : ∀ T : ℝ, 0 ≤ T →
      ContinuousOn D (uIcc (0 : ℝ) T))
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt f (D t) t := by
  have hT : 0 ≤ t + 1 := by linarith
  have hlocal : ContinuousOn D (Icc (0 : ℝ) (t + 1)) := by
    simpa only [uIcc_of_le hT] using hcont (t + 1) hT
  have hmem : Icc (0 : ℝ) (t + 1) ∈ 𝓝 t :=
    Icc_mem_nhds ht (by linarith)
  have hmeas : StronglyMeasurableAtFilter D (𝓝 t) volume := by
    exact ⟨Icc (0 : ℝ) (t + 1), hmem,
      hlocal.aestronglyMeasurable measurableSet_Icc⟩
  have hDc : ContinuousAt D t := hlocal.continuousAt hmem
  have hI : HasDerivAt (fun s => ∫ v in (0 : ℝ)..s, D v) (D t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((hcont t ht.le).intervalIntegrable) hmeas hDc
  have hsum := hI.add_const (f 0)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have hs0 : 0 ≤ s := (show 0 < s from hs).le
  have hid := GSTStage08.ac_integral_identity
    f D 0 s (hf s hs0) (hode s hs0)
  linarith

theorem p_ode_at
    (x : StateData) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (p x)
      ((x.rho + x.a) * p x t +
        2 * x.q * (state x t - x.target)) t := by
  apply hasDerivAt_of_local_ac_ae
    (p x)
    (fun s => (x.rho + x.a) * p x s +
      2 * x.q * (state x s - x.target))
    ?_ ?_ ?_ t ht
  · intro T hT
    exact (GSTStage28.p_solution (toCostateData x) T hT).1
  · intro T hT
    exact (GSTStage28.p_solution (toCostateData x) T hT).2
  · intro T hT
    have hp : ContinuousOn (p x) (uIcc (0 : ℝ) T) :=
      (GSTStage28.p_solution (toCostateData x) T hT).1.continuousOn
    have ho : ContinuousOn (state x) (uIcc (0 : ℝ) T) := by
      apply (state_continuousOn x).mono
      intro s hs
      rw [uIcc_of_le hT] at hs
      exact hs.1
    exact (continuousOn_const.mul hp).add
      (continuousOn_const.mul (ho.sub continuousOn_const))

theorem state_ode_at
    (x : StateData) (r : ℝ)
    (hclip : GSTStage44.Clipping x r)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (state x)
      (-x.a * state x t +
        x.c * (resource x.u x.eta x.B x.phiInitial t * x.u t)) t := by
  have hu : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable x.u volume 0 T := by
    intro T hT
    exact GSTStage27.bounded_control_integrable
      x.u x.U T hT x.huMeas x.hu
  have hsol : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval (state x) 0 T ∧
        (∀ᵐ s : ℝ, s ∈ uIcc (0 : ℝ) T →
          HasDerivAt (state x)
            (-x.a * state x s +
              x.c * (resource x.u x.eta x.B x.phiInitial s * x.u s)) s) := by
    intro T hT
    exact GSTStage29.omega_solution
      x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial T (hu T hT)
  apply hasDerivAt_of_local_ac_ae
    (state x)
    (fun s => -x.a * state x s +
      x.c * (resource x.u x.eta x.B x.phiInitial s * x.u s))
    ?_ ?_ ?_ t ht
  · intro T hT
    exact (hsol T hT).1
  · intro T hT
    exact (hsol T hT).2
  · intro T hT
    have ho := (hsol T hT).1.continuousOn
    have hres := resource_continuousOn
      x.u x.eta x.B x.phiInitial T (hu T hT)
    have huc := GSTStage44.candidate_control_continuousOn x r T hT hclip
    exact (continuousOn_const.mul ho).add
      (continuousOn_const.mul (hres.mul huc))

#print axioms hasDerivAt_of_local_ac_ae
#print axioms p_ode_at
#print axioms state_ode_at

end GSTStage47
