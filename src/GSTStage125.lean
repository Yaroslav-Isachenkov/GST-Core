import GSTStage124

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage32 GSTStage34 GSTStage37 GSTStage118

namespace GSTStage125

theorem objective_convex_quotient_error_bound
    (x : StateData) (r : ℝ) (v : ℝ → ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        |(objective x r (convexControl x.u v ε) -
            objective x r x.u) / ε -
          (∫ t in Ioi (0 : ℝ), stationarity x r v t)| ≤ ε * C := by
  obtain ⟨Cm, Cg, hCm, hCg, hb⟩ :=
    GSTStage124.convex_remainder_integral_bounds x r v hvMeas hvBound
  refine ⟨Cm + Cg, add_nonneg hCm hCg, ?_⟩
  intro ε hε hε1
  obtain ⟨_hmInt, _hgInt, hm, hg⟩ := hb ε hε.le hε1
  have hid := objective_convex_control_identity
    x r v ε hvMeas hvBound hε.le hε1
  have hne : ε ≠ 0 := ne_of_gt hε
  have he :
      (objective x r (convexControl x.u v ε) -
          objective x r x.u) / ε -
        (∫ t in Ioi (0 : ℝ), stationarity x r v t) =
      ((∫ t in Ioi (0 : ℝ),
          comparisonIntegrand x (convexControl x.u v ε) t) -
        (∫ t in Ioi (0 : ℝ),
          gap x r (convexControl x.u v ε) t)) / ε := by
    rw [hid]
    (field_simp [hne]; ring)
  have hsum :
      |(∫ t in Ioi (0 : ℝ),
          comparisonIntegrand x (convexControl x.u v ε) t) -
        (∫ t in Ioi (0 : ℝ),
          gap x r (convexControl x.u v ε) t)| ≤ ε ^ 2 * (Cm + Cg) := by
    calc
      |(∫ t in Ioi (0 : ℝ),
          comparisonIntegrand x (convexControl x.u v ε) t) -
        (∫ t in Ioi (0 : ℝ),
          gap x r (convexControl x.u v ε) t)|
        ≤ |∫ t in Ioi (0 : ℝ),
            comparisonIntegrand x (convexControl x.u v ε) t| +
          |∫ t in Ioi (0 : ℝ),
            gap x r (convexControl x.u v ε) t| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le
              (∫ t in Ioi (0 : ℝ),
                comparisonIntegrand x (convexControl x.u v ε) t)
              (-(∫ t in Ioi (0 : ℝ),
                gap x r (convexControl x.u v ε) t))
      _ ≤ ε ^ 2 * Cm + ε ^ 2 * Cg := add_le_add hm hg
      _ = ε ^ 2 * (Cm + Cg) := by ring
  rw [he, abs_div, abs_of_pos hε]
  calc
    |(∫ t in Ioi (0 : ℝ),
        comparisonIntegrand x (convexControl x.u v ε) t) -
      (∫ t in Ioi (0 : ℝ),
        gap x r (convexControl x.u v ε) t)| / ε
      ≤ (ε ^ 2 * (Cm + Cg)) / ε :=
        div_le_div_of_nonneg_right hsum hε.le
    _ = ε * (Cm + Cg) := by
      field_simp [hne]

theorem objective_convex_right_derivative
    (x : StateData) (r : ℝ) (v : ℝ → ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U) :
    Tendsto
      (fun ε : ℝ =>
        (objective x r (convexControl x.u v ε) -
          objective x r x.u) / ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in Ioi (0 : ℝ), stationarity x r v t)) := by
  obtain ⟨C, _hC, hb⟩ :=
    objective_convex_quotient_error_bound x r v hvMeas hvBound
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hzero : Tendsto (fun ε : ℝ => ε * C)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [zero_mul] using hid.mul_const C
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    (show ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun ε => dist_nonneg)) ?_ hzero
  filter_upwards [hpositive, hsmall] with ε hε hε1
  simpa only [Real.dist_eq] using hb ε hε hε1.le

end GSTStage125

#print axioms GSTStage125.objective_convex_quotient_error_bound
#print axioms GSTStage125.objective_convex_right_derivative
