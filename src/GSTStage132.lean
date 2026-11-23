import GSTStage131

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage36 GSTStage37

namespace GSTStage132

theorem optimality_extends_to_aemeasurable
    (x : StateData) (r : ℝ) (uStar : ℝ → ℝ)
    (hoptimal : ∀ v : ℝ → ℝ, Measurable v →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U) →
      objective x r v ≤ objective x r uStar) :
    ∀ v : ℝ → ℝ,
      AEMeasurable v (volume.restrict (Ioi (0 : ℝ))) →
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        0 ≤ v t ∧ v t ≤ x.U) →
      IntegrableOn (discountedCost x r v) (Ioi (0 : ℝ)) ∧
      objective x r v ≤ objective x r uStar := by
  intro v hvMeas hvBound
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  obtain ⟨w, hwMeas, hwAll, heq⟩ :=
    GSTStage42.measurable_bounded_representative
      x.U v hU hvMeas hvBound
  have hwBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t ∧ w t ≤ x.U :=
    fun t _ => hwAll t
  have hInt : IntegrableOn (discountedCost x r v) (Ioi (0 : ℝ)) :=
    (GSTStage36.discounted_cost_integrable x r w hwMeas hwBound).congr
      (GSTStage40.discounted_cost_ae_eq x r w v heq)
  have hJ : objective x r w = objective x r v :=
    GSTStage40.objective_eq_of_ae x r w v heq
  have hle := hoptimal w hwMeas hwBound
  rw [hJ] at hle
  exact ⟨hInt, hle⟩

theorem exists_optimal_control_aemeasurable
    (x : StateData) (r : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 ≤ r) :
    ∃ uStar : ℝ → ℝ, Measurable uStar ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ uStar t ∧ uStar t ≤ x.U) ∧
      IntegrableOn (discountedCost x r uStar) (Ioi (0 : ℝ)) ∧
      (∀ v : ℝ → ℝ,
        AEMeasurable v (volume.restrict (Ioi (0 : ℝ))) →
        (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
          0 ≤ v t ∧ v t ≤ x.U) →
        IntegrableOn (discountedCost x r v) (Ioi (0 : ℝ)) ∧
        objective x r v ≤ objective x r uStar) := by
  obtain ⟨uStar, huMeas, huBound, huInt, huOptimal⟩ :=
    GSTStage115.exists_optimal_control_ae x r hq hr
  have hpointwise : ∀ v : ℝ → ℝ, Measurable v →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U) →
      objective x r v ≤ objective x r uStar := by
    intro v hvMeas hvBound
    apply huOptimal v hvMeas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hvBound t (le_of_lt (show 0 < t from ht))
  exact ⟨uStar, huMeas, huBound, huInt,
    optimality_extends_to_aemeasurable x r uStar hpointwise⟩

end GSTStage132

#print axioms GSTStage132.optimality_extends_to_aemeasurable
#print axioms GSTStage132.exists_optimal_control_aemeasurable
