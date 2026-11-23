import GSTStage113
import Mathlib.Topology.Order.IsLUB

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage36 GSTStage37

namespace GSTStage114

theorem objective_nonpos
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (hq : 0 ≤ x.q) (hr : 0 ≤ r) :
    objective x r u ≤ 0 := by
  have hi : 0 ≤ ∫ t in Ioi (0 : ℝ), discountedCost x r u t :=
    integral_nonneg (fun t =>
      GSTStage111.discounted_cost_nonneg x r u hq hr t)
  unfold objective
  linarith

theorem exists_optimal_control
    (x : StateData) (r : ℝ)
    (hq : 0 ≤ x.q) (hr : 0 ≤ r) :
    ∃ b : ℝ → ℝ, Measurable b ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ b t ∧ b t ≤ x.U) ∧
      IntegrableOn (discountedCost x r b) (Ioi (0 : ℝ)) ∧
      (∀ u : ℝ → ℝ, Measurable u →
        (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
        objective x r u ≤ objective x r b) := by
  classical
  let S : Set ℝ := {y | ∃ u : ℝ → ℝ,
    Measurable u ∧
    (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) ∧
    objective x r u = y}

  have hnonempty : S.Nonempty := by
    refine ⟨objective x r x.u, ?_⟩
    exact ⟨x.u, x.huMeas, x.hu, rfl⟩

  have hbounded : BddAbove S := by
    refine ⟨0, ?_⟩
    intro y hy
    obtain ⟨u, huMeas, huBound, huEq⟩ := hy
    rw [← huEq]
    exact objective_nonpos x r u hq hr

  obtain ⟨y, hyMono, hyConv, hyMem⟩ :=
    exists_seq_tendsto_sSup hnonempty hbounded

  have hchoose : ∀ n : ℕ, ∃ u : ℝ → ℝ,
      Measurable u ∧
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) ∧
      objective x r u = y n := by
    intro n
    exact hyMem n
  choose u huMeas huBound huVal using hchoose

  have hseq :
      Tendsto (fun n => objective x r (u n))
        atTop (𝓝 (sSup S)) := by
    have he : (fun n => objective x r (u n)) = y :=
      funext huVal
    rw [he]
    exact hyConv

  obtain ⟨κ, hκ, b, hbMeas, hbBound, hbUpper⟩ :=
    GSTStage113.objective_subsequence_upper x r hq hr u huMeas huBound

  have hsub :
      Tendsto (fun n => objective x r (u (κ n)))
        atTop (𝓝 (sSup S)) := by
    simpa only [Function.comp_def] using
      hseq.comp hκ.tendsto_atTop

  have hSupLe : sSup S ≤ objective x r b := by
    by_contra hnot
    have hgap : 0 < sSup S - objective x r b :=
      sub_pos.mpr (lt_of_not_ge hnot)
    have hevent := hbUpper
      ((sSup S - objective x r b) / 2) (half_pos hgap)
    have hconst :
        Tendsto
          (fun _ : ℕ => objective x r b +
            (sSup S - objective x r b) / 2)
          atTop
          (𝓝 (objective x r b +
            (sSup S - objective x r b) / 2)) :=
      tendsto_const_nhds
    have hle := le_of_tendsto_of_tendsto hsub hconst hevent
    linarith

  have hbAE : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ b t ∧ b t ≤ x.U := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (0 : ℝ) < t at ht
    exact hbBound t ht.le
  have hbInt : IntegrableOn (discountedCost x r b) (Ioi (0 : ℝ)) :=
    GSTStage111.halfline_ae_cost_integrable x r b hbMeas hbAE

  refine ⟨b, hbMeas, hbBound, hbInt, ?_⟩
  intro v hvMeas hvBound
  have hvMem : objective x r v ∈ S :=
    ⟨v, hvMeas, hvBound, rfl⟩
  exact le_trans (le_csSup hbounded hvMem) hSupLe

end GSTStage114

#print axioms GSTStage114.objective_nonpos
#print axioms GSTStage114.exists_optimal_control
