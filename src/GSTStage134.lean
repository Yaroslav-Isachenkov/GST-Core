import GSTStage133

open MeasureTheory Set Filter
open scoped Topology
open GSTStage28

namespace GSTStage134

theorem p_unique_of_polynomial_growth
    (x : CostateData) (f : ℝ → ℝ) (C : ℝ) (n : ℕ)
    (hfAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval f 0 T)
    (hfODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt f
        ((x.rho + x.a) * f t +
          2 * x.q * (x.omega t - x.target)) t)
    (hfBound : ∀ t : ℝ, 0 ≤ t →
      |f t| ≤ C * (1 + t ^ n)) :
    ∀ t : ℝ, 0 ≤ t → f t = pOf x t := by
  obtain ⟨P, _hP, hp⟩ := GSTStage22.p_linear_growth
    x.omega x.rho x.a x.q x.target x.M
    x.hdecay x.hM x.hcont x.hOmega
  have hpBound : ∀ t : ℝ, 0 ≤ t →
      |pOf x t| ≤ P * (1 + t ^ (1 : ℕ)) := by
    intro t ht
    simpa only [pOf, pow_one] using hp t ht
  have hpODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt (pOf x)
        ((x.rho + x.a) * pOf x t +
          2 * x.q * (x.omega t - x.target)) t :=
    ae_nonnegative_of_ae_on_intervals
      (fun t => HasDerivAt (pOf x)
        ((x.rho + x.a) * pOf x t +
          2 * x.q * (x.omega t - x.target)) t)
      (fun T hT => (p_solution x T hT).2)
  have hfODE' : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt f
        ((x.rho + x.a + 0 * (0 : ℝ)) * f t +
          2 * x.q * (x.omega t - x.target)) t := by
    simpa only [mul_zero, add_zero] using hfODE
  have hpODE' : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt (pOf x)
        ((x.rho + x.a + 0 * (0 : ℝ)) * pOf x t +
          2 * x.q * (x.omega t - x.target)) t := by
    simpa only [mul_zero, add_zero] using hpODE
  exact GSTStage133.linear_costate_unique_of_polynomial_growth
    (fun _ : ℝ => 0) f (pOf x)
    (fun t => 2 * x.q * (x.omega t - x.target))
    0 (x.rho + x.a) C P n 1
    le_rfl x.hdecay
    (Filter.Eventually.of_forall (fun _ _ => le_rfl))
    (fun _ _ => intervalIntegrable_const)
    hfAC (fun T hT => (p_solution x T hT).1)
    hfODE' hpODE' hfBound hpBound

theorem z_unique_of_polynomial_growth
    (x : CostateData) (f : ℝ → ℝ) (C : ℝ) (n : ℕ)
    (hfAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval f 0 T)
    (hfODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt f
        ((x.rho + x.eta * x.u t) * f t -
          x.c * x.u t * pOf x t) t)
    (hfBound : ∀ t : ℝ, 0 ≤ t →
      |f t| ≤ C * (1 + t ^ n)) :
    ∀ t : ℝ, 0 ≤ t → f t = zOf x t := by
  obtain ⟨P, hP, hp⟩ := GSTStage22.p_linear_growth
    x.omega x.rho x.a x.q x.target x.M
    x.hdecay x.hM x.hcont x.hOmega
  have hpBound : ∀ t : ℝ, 0 ≤ t →
      |pOf x t| ≤ P * (1 + t) := hp
  have hpMeas : Measurable (pOf x) :=
    GSTStage24.p_measurable
      x.omega x.rho x.a x.q x.target x.hOmegaMeas
  have hmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun s => GSTStage23.zKernel x.u x.eta x.rho t (t + s) *
          (x.u (t + s) * pOf x (t + s)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    intro t _
    exact GSTStage24.z_integrand_aestronglyMeasurable
      x.u (pOf x) x.eta x.rho t x.huMeas hpMeas
  obtain ⟨Z, _hZ, hz⟩ := GSTStage23.z_linear_growth
    x.u (pOf x) x.eta x.rho x.c x.U P
    x.heta x.hrho x.hU hP x.hu hpBound hmeas
  have hzBound : ∀ t : ℝ, 0 ≤ t →
      |zOf x t| ≤ Z * (1 + t ^ (1 : ℕ)) := by
    intro t ht
    simpa only [zOf, pow_one] using hz t ht
  have hzODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt (zOf x)
        ((x.rho + x.eta * x.u t) * zOf x t -
          x.c * x.u t * pOf x t) t :=
    ae_nonnegative_of_ae_on_intervals
      (fun t => HasDerivAt (zOf x)
        ((x.rho + x.eta * x.u t) * zOf x t -
          x.c * x.u t * pOf x t) t)
      (fun T hT => (z_solution x T hT).2)
  have hfODE' : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt f
        ((x.rho + x.eta * x.u t) * f t +
          -(x.c * x.u t * pOf x t)) t := by
    simpa only [sub_eq_add_neg] using hfODE
  have hzODE' : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt (zOf x)
        ((x.rho + x.eta * x.u t) * zOf x t +
          -(x.c * x.u t * pOf x t)) t := by
    simpa only [sub_eq_add_neg] using hzODE
  exact GSTStage133.linear_costate_unique_of_polynomial_growth
    x.u f (zOf x) (fun t => -(x.c * x.u t * pOf x t))
    x.eta x.rho C Z n 1 x.heta x.hrho
    (Filter.Eventually.of_forall (fun t ht => (x.hu t ht).1))
    (fun T hT => GSTStage27.bounded_control_integrable
      x.u x.U T hT x.huMeas x.hu)
    hfAC (fun T hT => (z_solution x T hT).1)
    hfODE' hzODE' hfBound hzBound

end GSTStage134

#print axioms GSTStage134.p_unique_of_polynomial_growth
#print axioms GSTStage134.z_unique_of_polynomial_growth
