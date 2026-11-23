import GSTStage185

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29 GSTStage31 GSTStage36 GSTStage37 GSTStage115

namespace GSTStage186

theorem zero_source_zero_resource_omega
    (u : ℝ → ℝ) (eta a c omegaInitial t : ℝ) :
    omega u eta 0 0 a c omegaInitial t =
      Real.exp (-a * t) * omegaInitial := by
  simp [omega, linearState, weightedInput, resourceForcing, resource]

theorem zero_control_omega
    (eta B phiInitial a c omegaInitial t : ℝ) :
    omega (fun _ => 0) eta B phiInitial a c omegaInitial t =
      Real.exp (-a * t) * omegaInitial := by
  simp [omega, linearState, weightedInput, resourceForcing]

theorem zero_control_optimal_of_zero_source_zero_resource
    (x : StateData) (r : ℝ)
    (hB : x.B = 0) (hi : x.phiInitial = 0) (hr : 0 ≤ r)
    (u : ℝ → ℝ) (hmeas : Measurable u)
    (hbound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    objective x r u ≤ objective x r (fun _ => 0) := by
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  have hzeroBound :
      ∀ t : ℝ, 0 ≤ t → 0 ≤ (0 : ℝ) ∧ 0 ≤ x.U := by
    intro _ _
    exact ⟨le_rfl, hU⟩
  have hCzero := discounted_cost_integrable
    x r (fun _ => 0) measurable_const hzeroBound
  have hCu := discounted_cost_integrable x r u hmeas hbound
  have hpoint : ∀ t : ℝ,
      discountedCost x r (fun _ => 0) t ≤ discountedCost x r u t := by
    intro t
    unfold discountedCost GSTStage34.competitorState
    rw [zero_control_omega, hB, hi, zero_source_zero_resource_omega]
    dsimp only [GSTStage06.runningCost]
    have hterm : 0 ≤ r * (u t) ^ 2 := mul_nonneg hr (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    nlinarith only [hterm]
  have hcost :
      (∫ t in Ioi (0 : ℝ), discountedCost x r (fun _ => 0) t) ≤
        ∫ t in Ioi (0 : ℝ), discountedCost x r u t :=
    integral_mono_ae hCzero hCu (Filter.Eventually.of_forall hpoint)
  exact neg_le_neg hcost

theorem zero_control_objective_independent_source
    (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n) :
    objective (k.toStateData n hn) k.r (fun _ => 0) =
      objective (k.toStateData 0 le_rfl) k.r (fun _ => 0) := by
  simp only [objective, discountedCost, GSTStage34.competitorState,
    CoreParameters.toStateData, zero_control_omega]

end GSTStage186

#print axioms GSTStage186.zero_source_zero_resource_omega
#print axioms GSTStage186.zero_control_omega
#print axioms GSTStage186.zero_control_optimal_of_zero_source_zero_resource
#print axioms GSTStage186.zero_control_objective_independent_source
