import GSTStage112

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage37

namespace GSTStage113

theorem halfline_admissible_representative
    (x : StateData) (a : ℝ → ℝ)
    (haMeas : Measurable a)
    (haBound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ a t ∧ a t ≤ x.U) :
    ∃ b : ℝ → ℝ, Measurable b ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ b t ∧ b t ≤ x.U) ∧
      (b =ᵐ[volume.restrict (Ioi (0 : ℝ))] a) ∧
      (∀ r : ℝ, objective x r b = objective x r a) := by
  let b : ℝ → ℝ := GSTStage39.boundedRepresentative x.U a
  have hU : 0 ≤ x.U :=
    le_trans (x.hu 0 le_rfl).1 (x.hu 0 le_rfl).2
  have hbMeas : Measurable b :=
    GSTStage39.representative_measurable x.U a haMeas
  have hbBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ b t ∧ b t ≤ x.U := by
    intro t _
    exact GSTStage39.representative_bounds x.U a hU t
  have hbEq : b =ᵐ[volume.restrict (Ioi (0 : ℝ))] a := by
    filter_upwards [haBound] with t ht
    exact GSTStage39.representative_eq_of_bounds x.U a t ht.1 ht.2
  refine ⟨b, hbMeas, hbBound, hbEq, ?_⟩
  intro r
  exact GSTStage40.objective_eq_of_ae x r b a hbEq

theorem objective_subsequence_upper
    (x : StateData) (r : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 ≤ r)
    (u : ℕ → ℝ → ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ x.U) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
    ∃ b : ℝ → ℝ, Measurable b ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ b t ∧ b t ≤ x.U) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          objective x r (u (κ n)) ≤ objective x r b + ε) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont,
      hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
      haInt, hPhiEq, hOmegaEq, haIntervals, hcontrol, hstateCost, hcost,
      hlimInt, hseqInt, hfull⟩ :=
    GSTStage112.joint_global_limit_infinite_cost_lower x u huMeas huBound
  obtain ⟨b, hbMeas, hbBound, hbEq, hbObj⟩ :=
    halfline_admissible_representative x a haMeas haBound
  refine ⟨κ, hκ, b, hbMeas, hbBound, ?_⟩
  intro ε hε
  filter_upwards [hfull r hq hr ε hε] with n hn
  rw [hbObj r]
  dsimp only [objective]
  linarith

end GSTStage113

#print axioms GSTStage113.halfline_admissible_representative
#print axioms GSTStage113.objective_subsequence_upper
