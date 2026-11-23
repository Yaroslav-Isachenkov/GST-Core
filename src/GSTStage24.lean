import GSTStage23
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
open scoped Topology
open GSTStage22 GSTStage23

namespace GSTStage24

-- Measurability of the interval integral as its upper endpoint varies.
-- Convergence is a separate issue; this lemma concerns measurability.
theorem interval_primitive_measurable
    (u : ℝ → ℝ) (t : ℝ) (hu : Measurable u) :
    Measurable (fun s : ℝ => ∫ r in t..s, u r) := by
  let A : Set (ℝ × ℝ) := {x | t < x.2 ∧ x.2 ≤ x.1}
  let B : Set (ℝ × ℝ) := {x | x.1 < x.2 ∧ x.2 ≤ t}
  have hA : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hB : MeasurableSet B :=
    (measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hFA : Measurable (A.indicator (fun x : ℝ × ℝ => u x.2)) :=
    (hu.comp measurable_snd).indicator hA
  have hFB : Measurable (B.indicator (fun x : ℝ × ℝ => u x.2)) :=
    (hu.comp measurable_snd).indicator hB
  have hIA : Measurable
      (fun s : ℝ => ∫ r : ℝ,
        A.indicator (fun x : ℝ × ℝ => u x.2) (s, r)) :=
    (hFA.stronglyMeasurable.integral_prod_right').measurable
  have hIB : Measurable
      (fun s : ℝ => ∫ r : ℝ,
        B.indicator (fun x : ℝ × ℝ => u x.2) (s, r)) :=
    (hFB.stronglyMeasurable.integral_prod_right').measurable
  have eA :
      (fun s : ℝ => ∫ r : ℝ,
        A.indicator (fun x : ℝ × ℝ => u x.2) (s, r)) =
      (fun s : ℝ => ∫ r in Ioc t s, u r) := by
    funext s
    change (∫ r : ℝ, (Ioc t s).indicator u r) =
      ∫ r in Ioc t s, u r
    exact integral_indicator measurableSet_Ioc
  have eB :
      (fun s : ℝ => ∫ r : ℝ,
        B.indicator (fun x : ℝ × ℝ => u x.2) (s, r)) =
      (fun s : ℝ => ∫ r in Ioc s t, u r) := by
    funext s
    change (∫ r : ℝ, (Ioc s t).indicator u r) =
      ∫ r in Ioc s t, u r
    exact integral_indicator measurableSet_Ioc
  rw [eA] at hIA
  rw [eB] at hIB
  change Measurable
    (fun s : ℝ => (∫ r in Ioc t s, u r) - ∫ r in Ioc s t, u r)
  exact hIA.sub hIB

-- Measurability of p is derived from its integral definition.
theorem p_measurable
    (omega : ℝ → ℝ) (rho a q target : ℝ)
    (hOmega : Measurable omega) :
    Measurable (pCostate omega rho a q target) := by
  have hExp : Measurable
      (fun x : ℝ × ℝ => Real.exp (-(rho + a) * x.2)) :=
    Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_snd)
  have hJoint : Measurable
      (fun x : ℝ × ℝ =>
        Real.exp (-(rho + a) * x.2) *
          (target - omega (x.1 + x.2))) :=
    hExp.mul
      (measurable_const.sub
        (hOmega.comp (measurable_fst.add measurable_snd)))
  have hIntegral : Measurable
      (fun t : ℝ => ∫ s in Ioi (0 : ℝ),
        Real.exp (-(rho + a) * s) * (target - omega (t + s))) :=
    (hJoint.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioi (0 : ℝ)))).measurable
  have heq : pCostate omega rho a q target =
      (fun t : ℝ => 2 * q * ∫ s in Ioi (0 : ℝ),
        Real.exp (-(rho + a) * s) * (target - omega (t + s))) :=
    funext (fun t => p_shifted omega rho a q target t)
  rw [heq]
  exact measurable_const.mul hIntegral

theorem z_kernel_measurable
    (u : ℝ → ℝ) (eta rho t : ℝ) (hu : Measurable u) :
    Measurable (zKernel u eta rho t) := by
  change Measurable
    (fun s : ℝ => Real.exp
      (-rho * (s - t) - eta * ∫ r in t..s, u r))
  exact Real.continuous_exp.measurable.comp
    ((measurable_const.mul (measurable_id.sub measurable_const)).sub
      (measurable_const.mul (interval_primitive_measurable u t hu)))

theorem z_integrand_aestronglyMeasurable
    (u p : ℝ → ℝ) (eta rho t : ℝ)
    (hu : Measurable u) (hp : Measurable p) :
    AEStronglyMeasurable
      (fun s => zKernel u eta rho t (t + s) *
        (u (t + s) * p (t + s)))
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hAdd : Measurable (fun s : ℝ => t + s) :=
    measurable_const.add measurable_id
  have h :
      Measurable (fun s => zKernel u eta rho t (t + s) *
        (u (t + s) * p (t + s))) :=
    ((z_kernel_measurable u eta rho t hu).comp hAdd).mul
      ((hu.comp hAdd).mul (hp.comp hAdd))
  exact h.stronglyMeasurable.aestronglyMeasurable

-- Stage23 without the special integrand-measurability hypothesis.
-- Ordinary measurability of u and omega is explicit.
theorem d_linear_growth_of_measurable_data
    (u omega : ℝ → ℝ) (eta rho a c q target U M : ℝ)
    (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hdecay : 0 < rho + a)
    (hU : 0 ≤ U) (hM : 0 ≤ M)
    (huMeas : Measurable u) (hOmegaMeas : Measurable omega)
    (hu : ∀ r : ℝ, 0 ≤ r → 0 ≤ u r ∧ u r ≤ U)
    (hcont : ContinuousOn omega (Ici (0 : ℝ)))
    (hOmega : ∀ r : ℝ, 0 ≤ r → |omega r| ≤ M * (1 + r)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 ≤ t →
      |c * pCostate omega rho a q target t -
        eta * zCostate u (pCostate omega rho a q target) eta rho c t|
        ≤ D * (1 + t) := by
  apply integral_costates_d_linear_growth
    u omega eta rho a c q target U M
    heta hrho hdecay hU hM hu hcont hOmega
  intro t _ht
  exact z_integrand_aestronglyMeasurable
    u (pCostate omega rho a q target) eta rho t huMeas
    (p_measurable omega rho a q target hOmegaMeas)

#print axioms interval_primitive_measurable
#print axioms p_measurable
#print axioms z_kernel_measurable
#print axioms z_integrand_aestronglyMeasurable
#print axioms d_linear_growth_of_measurable_data

end GSTStage24
