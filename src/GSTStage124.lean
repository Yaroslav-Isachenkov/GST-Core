import GSTStage123

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage32 GSTStage34 GSTStage118 GSTStage122 GSTStage123

namespace GSTStage124

theorem integral_bound_of_quadratic_envelope
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f E : α → ℝ) (ε : ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hE : Integrable E μ)
    (hb : ∀ᵐ t ∂μ, |f t| ≤ ε ^ 2 * E t) :
    Integrable f μ ∧
      |∫ t, f t ∂μ| ≤ ε ^ 2 * ∫ t, E t ∂μ := by
  have hn : ∀ᵐ t ∂μ, ‖f t‖ ≤ ε ^ 2 * E t := by
    simpa only [Real.norm_eq_abs] using hb
  have hi : Integrable (fun t => ε ^ 2 * E t) μ :=
    hE.const_mul (ε ^ 2)
  refine ⟨hi.mono' hf hn, ?_⟩
  have h := norm_integral_le_of_norm_le hi hn
  simpa only [Real.norm_eq_abs, integral_const_mul] using h

theorem convex_remainder_integral_bounds
    (x : StateData) (r : ℝ) (v : ℝ → ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U) :
    ∃ Cm Cg : ℝ, 0 ≤ Cm ∧ 0 ≤ Cg ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        IntegrableOn (comparisonIntegrand x (convexControl x.u v ε))
          (Ioi (0 : ℝ)) ∧
        IntegrableOn (gap x r (convexControl x.u v ε))
          (Ioi (0 : ℝ)) ∧
        |∫ t in Ioi (0 : ℝ),
          comparisonIntegrand x (convexControl x.u v ε) t| ≤ ε ^ 2 * Cm ∧
        |∫ t in Ioi (0 : ℝ),
          gap x r (convexControl x.u v ε) t| ≤ ε ^ 2 * Cg := by
  obtain ⟨D, hD, hmBound⟩ :=
    mixed_convex_quadratic_bound x v hvMeas hvBound
  let Em : ℝ → ℝ := fun t =>
    Real.exp (-x.rho * t) * (D * (1 + t)) *
      resourceVariationBound x t * x.U
  let Eg : ℝ → ℝ := fun t =>
    Real.exp (-x.rho * t) *
      (|x.q| * (stateVariationBound x t) ^ 2 + |r| * x.U ^ 2)
  have hEm : IntegrableOn Em (Ioi (0 : ℝ)) :=
    mixed_envelope_integrable x D
  have hEg : IntegrableOn Eg (Ioi (0 : ℝ)) :=
    gap_envelope_integrable x r
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2

  have hEm0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ Em t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    have hR : 0 ≤ resourceVariationBound x t := by
      unfold resourceVariationBound
      exact mul_nonneg
        (mul_nonneg (mul_nonneg x.heta.le hU) ht0)
        (add_nonneg x.hphiInitial (mul_nonneg x.hB ht0))
    have htime : 0 ≤ 1 + t := by linarith
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.exp_pos _).le (mul_nonneg hD htime)) hR) hU
  have hEg0 : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ Eg t := by
    apply Filter.Eventually.of_forall
    intro t
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg
        (mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (mul_nonneg (abs_nonneg _) (sq_nonneg _)))

  refine ⟨∫ t in Ioi (0 : ℝ), Em t,
    ∫ t in Ioi (0 : ℝ), Eg t,
    integral_nonneg_of_ae hEm0, integral_nonneg_of_ae hEg0, ?_⟩
  intro ε hε0 hε1
  have hadm := convex_control_admissible
    x.u v x.U ε x.huMeas hvMeas x.hu hvBound hε0 hε1
  have hmMeas := GSTStage33.mixed_aestronglyMeasurable
    x (convexControl x.u v ε) hadm.1

  have hO : Measurable
      (fun t => competitorState x (convexControl x.u v ε) t - state x t) :=
    (omega_measurable (convexControl x.u v ε)
      x.eta x.B x.phiInitial x.a x.c x.omegaInitial hadm.1).sub
    (omega_measurable x.u
      x.eta x.B x.phiInitial x.a x.c x.omegaInitial x.huMeas)
  have hdu : Measurable (fun t => convexControl x.u v ε t - x.u t) :=
    hadm.1.sub x.huMeas
  have heMeas : Measurable (fun t : ℝ => Real.exp (-x.rho * t)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)
  have hgMeas : Measurable (gap x r (convexControl x.u v ε)) := by
    unfold gap
    simp only [pow_two]
    exact heMeas.mul
      ((measurable_const.mul (hO.mul hO)).add
        (measurable_const.mul (hdu.mul hdu)))

  have hm := integral_bound_of_quadratic_envelope
    (volume.restrict (Ioi (0 : ℝ)))
    (comparisonIntegrand x (convexControl x.u v ε)) Em ε
    hmMeas hEm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hmBound ε hε0 hε1 t (le_of_lt ht))
  have hg := integral_bound_of_quadratic_envelope
    (volume.restrict (Ioi (0 : ℝ)))
    (gap x r (convexControl x.u v ε)) Eg ε
    hgMeas.stronglyMeasurable.aestronglyMeasurable hEg (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact gap_convex_quadratic_bound
        x r v hvMeas hvBound ε t hε0 hε1 (le_of_lt ht))
  exact ⟨hm.1, hg.1, hm.2, hg.2⟩

end GSTStage124

#print axioms GSTStage124.integral_bound_of_quadratic_envelope
#print axioms GSTStage124.convex_remainder_integral_bounds
