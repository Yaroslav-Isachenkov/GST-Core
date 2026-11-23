import GSTStage67

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage36

namespace GSTStage68

theorem integrable_tail_tendsto_zero
    (g : ℝ → ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ))) :
    Tendsto (GSTStage25.tail g) atTop (𝓝 0) := by
  have hi :
      Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T, g t)
        atTop (𝓝 (∫ t in Ioi (0 : ℝ), g t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hg tendsto_id
  have hsub :
      Tendsto
        (fun T : ℝ =>
          GSTStage25.tail g 0 - ∫ t in (0 : ℝ)..T, g t)
        atTop (𝓝 0) := by
    simpa only [GSTStage25.tail, sub_self] using
      (tendsto_const_nhds.sub hi :
        Tendsto
          (fun T : ℝ =>
            GSTStage25.tail g 0 - ∫ t in (0 : ℝ)..T, g t)
          atTop
          (𝓝 (GSTStage25.tail g 0 - ∫ t in Ioi (0 : ℝ), g t)))
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (GSTStage25.tail_representation g T hg hT).symm

theorem uniform_cost_tail_small
    (x : StateData) (r : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 ≤ r) :
    ∀ ε : ℝ, 0 < ε →
      ∃ T₀ : ℝ, 0 ≤ T₀ ∧
        ∀ T : ℝ, T₀ ≤ T →
          ∀ u : ℝ → ℝ, Measurable u →
            (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
            IntegrableOn (discountedCost x r u) (Ioi T) ∧
            0 ≤ (∫ t in Ioi T, discountedCost x r u t) ∧
            (∫ t in Ioi T, discountedCost x r u t) < ε := by
  obtain ⟨C, _hC, hE, hbound⟩ :=
    GSTStage67.uniform_cost_integrable_envelope x r hq hr
  let E : ℝ → ℝ :=
    fun t => C * (1 + t ^ 2) * Real.exp (-x.rho * t)
  have hEint : IntegrableOn E (Ioi (0 : ℝ)) := hE
  have hlimit := integrable_tail_tendsto_zero E hEint
  intro ε hε
  have hevent :
      ∀ᶠ T : ℝ in atTop, GSTStage25.tail E T < ε :=
    (tendsto_order.1 hlimit).2 ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.1 hevent
  refine ⟨max 0 R, le_max_left _ _, ?_⟩
  intro T hT u huMeas huBound
  have hT0 : 0 ≤ T := le_trans (le_max_left _ _) hT
  have hRT : R ≤ T := le_trans (le_max_right _ _) hT
  have hsubset : Ioi T ⊆ Ioi (0 : ℝ) :=
    fun _ ht => lt_of_le_of_lt hT0 ht
  have hcostInt : IntegrableOn (discountedCost x r u) (Ioi T) :=
    (GSTStage36.discounted_cost_integrable x r u huMeas huBound).mono_set
      hsubset
  have hEtInt : IntegrableOn E (Ioi T) :=
    hEint.mono_set hsubset
  have hsign :
      ∀ᵐ t ∂volume.restrict (Ioi T), 0 ≤ discountedCost x r u t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hbound u huMeas huBound t
      (le_trans hT0 (le_of_lt ht))).1
  have hdom :
      ∀ᵐ t ∂volume.restrict (Ioi T),
        discountedCost x r u t ≤ E t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hbound u huMeas huBound t
      (le_trans hT0 (le_of_lt ht))).2
  have hle :
      (∫ t in Ioi T, discountedCost x r u t) ≤
        ∫ t in Ioi T, E t :=
    integral_mono_ae hcostInt hEtInt hdom
  refine ⟨hcostInt, integral_nonneg_of_ae hsign, ?_⟩
  exact lt_of_le_of_lt hle (hR T hRT)

#print axioms GSTStage68.integrable_tail_tendsto_zero
#print axioms GSTStage68.uniform_cost_tail_small

end GSTStage68
