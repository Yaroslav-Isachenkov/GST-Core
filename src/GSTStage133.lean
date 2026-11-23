import GSTStage132

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage133

theorem homogeneous_zero_of_weighted_limit
    (v h : ℝ → ℝ) (eta rho : ℝ)
    (hv : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable v volume 0 T)
    (hAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval h 0 T)
    (hODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt h ((rho + eta * v t) * h t) t)
    (htail : Tendsto
      (fun t => GSTStage19.weight v eta rho t * h t)
      atTop (𝓝 0)) :
    ∀ t : ℝ, 0 ≤ t → h t = 0 := by
  let H : ℝ → ℝ := fun t =>
    GSTStage19.weight v eta rho t * h t
  have hconstant : ∀ T : ℝ, 0 ≤ T → H T = H 0 := by
    intro T hT
    have hlocal : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt h
          ((rho + eta * v t) * h t + 0 * (0 : ℝ)) t := by
      filter_upwards [hODE] with t ht hmem
      rw [uIcc_of_le hT] at hmem
      simpa only [mul_zero, add_zero] using ht hmem.1
    have hderiv := GSTStage19.weighted_d_derivative_ae
      v h (fun _ : ℝ => 0) eta rho 0 T (hv T hT) hlocal
    have hzero : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
        HasDerivAt H 0 t := by
      filter_upwards [hderiv] with t ht hmem
      simpa only [H, mul_zero] using ht hmem
    have hH : AbsolutelyContinuousOnInterval H 0 T :=
      (GSTStage19.weight_ac v eta rho T (hv T hT)).fun_mul (hAC T hT)
    obtain ⟨C, hC⟩ := hH.const_of_ae_hasDerivAt_zero hzero
    exact (hC T right_mem_uIcc).trans (hC 0 left_mem_uIcc).symm
  have hlimit : Tendsto H atTop (𝓝 (H 0)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hconstant t ht).symm
  have hH0 : H 0 = 0 := tendsto_nhds_unique hlimit htail
  intro t ht
  have hz : GSTStage19.weight v eta rho t * h t = 0 :=
    (hconstant t ht).trans hH0
  exact (mul_eq_zero.mp hz).resolve_left
    (ne_of_gt (GSTStage19.weight_positive v eta rho t))

theorem linear_costate_unique_of_polynomial_growth
    (v f g forcing : ℝ → ℝ)
    (eta rho Cf Cg : ℝ) (nf ng : ℕ)
    (heta : 0 ≤ eta) (hrho : 0 < rho)
    (hvNonneg : ∀ᵐ t : ℝ, 0 ≤ t → 0 ≤ v t)
    (hv : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable v volume 0 T)
    (hfAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval f 0 T)
    (hgAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval g 0 T)
    (hfODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt f ((rho + eta * v t) * f t + forcing t) t)
    (hgODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt g ((rho + eta * v t) * g t + forcing t) t)
    (hfBound : ∀ t : ℝ, 0 ≤ t →
      |f t| ≤ Cf * (1 + t ^ nf))
    (hgBound : ∀ t : ℝ, 0 ≤ t →
      |g t| ≤ Cg * (1 + t ^ ng)) :
    ∀ t : ℝ, 0 ≤ t → f t = g t := by
  have hfTail := GSTStage20.weighted_tail_from_polynomial_bound
    v f eta rho Cf nf heta hrho hvNonneg hfBound
  have hgTail := GSTStage20.weighted_tail_from_polynomial_bound
    v g eta rho Cg ng heta hrho hvNonneg hgBound
  have htail : Tendsto
      (fun t => GSTStage19.weight v eta rho t * (f t - g t))
      atTop (𝓝 0) := by
    simpa only [mul_sub, sub_self] using hfTail.sub hgTail
  have hAC : ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval (fun t => f t - g t) 0 T :=
    fun T hT => (hfAC T hT).fun_sub (hgAC T hT)
  have hODE : ∀ᵐ t : ℝ, 0 ≤ t →
      HasDerivAt (fun s => f s - g s)
        ((rho + eta * v t) * (f t - g t)) t := by
    filter_upwards [hfODE, hgODE] with t hft hgt ht
    convert (hft ht).sub (hgt ht) using 1; ring
  have hz := homogeneous_zero_of_weighted_limit
    v (fun t => f t - g t) eta rho hv hAC hODE htail
  intro t ht
  exact sub_eq_zero.mp (hz t ht)

end GSTStage133

#print axioms GSTStage133.homogeneous_zero_of_weighted_limit
#print axioms GSTStage133.linear_costate_unique_of_polynomial_growth
