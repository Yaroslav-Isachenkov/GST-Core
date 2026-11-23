import GSTStage35
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34

namespace GSTStage36

-- Positive running-cost convention.
-- The maximized objective J will be minus its integral.
noncomputable def discountedCost
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-x.rho * t) *
    GSTStage06.runningCost x.q r x.target
      (competitorState x u t) (u t)

theorem shifted_linear_growth
    (f : ℝ → ℝ) (b : ℝ)
    (hf : ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, 0 ≤ t → |f t| ≤ M * (1 + t)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ t : ℝ, 0 ≤ t → |f t - b| ≤ K * (1 + t) := by
  obtain ⟨M, hM, hm⟩ := hf
  refine ⟨M + |b|, add_nonneg hM (abs_nonneg b), ?_⟩
  intro t ht
  have hb : |b| ≤ |b| * (1 + t) := by
    nlinarith [mul_nonneg (abs_nonneg b) ht]
  calc
    |f t - b| ≤ |f t| + |b| := abs_sub _ _
    _ ≤ M * (1 + t) + |b| * (1 + t) := add_le_add (hm t ht) hb
    _ = (M + |b|) * (1 + t) := by ring

theorem discounted_square_integrable
    (f : ℝ → ℝ) (rho : ℝ)
    (hrho : 0 < rho) (hfMeas : Measurable f)
    (hfGrowth : ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, 0 ≤ t → |f t| ≤ M * (1 + t)) :
    IntegrableOn
      (fun t : ℝ => Real.exp (-rho * t) * (f t) ^ 2)
      (Ioi (0 : ℝ)) := by
  obtain ⟨M, hM, hm⟩ := hfGrowth
  have heMeas : Measurable (fun t : ℝ => Real.exp (-rho * t)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable
  apply GSTStage04.dominated_integrable
    (fun t : ℝ => Real.exp (-rho * t) * (f t) ^ 2)
    rho (2 * M ^ 2) 2 hrho
    ((heMeas.mul (hfMeas.pow_const 2)).aestronglyMeasurable)
  intro t ht
  have ht1 : 0 ≤ 1 + t := by linarith
  have hb := hm t ht.le
  have hs : (f t) ^ 2 ≤ M ^ 2 * (1 + t) ^ 2 := by
    calc
      (f t) ^ 2 = |f t| * |f t| := by
        rw [← pow_two, sq_abs]
      _ ≤ (M * (1 + t)) * (M * (1 + t)) :=
        mul_le_mul hb hb (abs_nonneg _) (mul_nonneg hM ht1)
      _ = M ^ 2 * (1 + t) ^ 2 := by ring
  have htSquare : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (t - 1)]
  have hsBound : (f t) ^ 2 ≤ (2 * M ^ 2) * (1 + t ^ 2) := by
    calc
      (f t) ^ 2 ≤ M ^ 2 * (1 + t) ^ 2 := hs
      _ ≤ M ^ 2 * (2 * (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left htSquare (sq_nonneg M)
      _ = (2 * M ^ 2) * (1 + t ^ 2) := by ring
  calc
    |Real.exp (-rho * t) * (f t) ^ 2| =
        Real.exp (-rho * t) * (f t) ^ 2 :=
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
    _ ≤ Real.exp (-rho * t) * ((2 * M ^ 2) * (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hsBound (Real.exp_pos _).le
    _ = (2 * M ^ 2) * (1 + t ^ 2) * Real.exp (-rho * t) := by ring

theorem control_linear_growth
    (x : StateData) (u : ℝ → ℝ)
    (hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ t : ℝ, 0 ≤ t → |u t| ≤ M * (1 + t) := by
  have hU : 0 ≤ x.U := (toCostateData x).hU
  refine ⟨x.U, hU, ?_⟩
  intro t ht
  rw [abs_of_nonneg (hu t ht).1]
  have h := (hu t ht).2
  nlinarith [mul_nonneg hU ht]

theorem discounted_cost_integrable
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    IntegrableOn (discountedCost x r u) (Ioi (0 : ℝ)) := by
  have hoMeas : Measurable (competitorState x u) :=
    GSTStage31.omega_measurable
      u x.eta x.B x.phiInitial x.a x.c x.omegaInitial huMeas
  have hoGrowth : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
      |competitorState x u t| ≤ M * (1 + t) :=
    GSTStage30.admissible_omega_linear_growth
      u x.eta x.B x.phiInitial x.a x.c x.omegaInitial x.U
      x.heta x.ha x.hB x.hphiInitial x.hc x.homegaInitial huMeas huBound
  have hoInt := discounted_square_integrable
    (fun t => competitorState x u t - x.target)
    x.rho x.hrho (hoMeas.sub measurable_const)
    (shifted_linear_growth (competitorState x u) x.target hoGrowth)
  have huInt := discounted_square_integrable
    u x.rho x.hrho huMeas (control_linear_growth x u huBound)
  have heq : discountedCost x r u =
      (fun t => x.q * (Real.exp (-x.rho * t) *
          (competitorState x u t - x.target) ^ 2) +
        r * (Real.exp (-x.rho * t) * (u t) ^ 2)) := by
    funext t
    dsimp [discountedCost, GSTStage06.runningCost]
    ring
  rw [heq]
  exact (hoInt.const_mul x.q).add (huInt.const_mul r)

theorem gap_integrable
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    IntegrableOn (gap x r u) (Ioi (0 : ℝ)) := by
  have hoMeas : Measurable (competitorState x u) :=
    GSTStage31.omega_measurable
      u x.eta x.B x.phiInitial x.a x.c x.omegaInitial huMeas
  have hsMeas : Measurable (state x) :=
    GSTStage31.omega_measurable
      x.u x.eta x.B x.phiInitial x.a x.c x.omegaInitial x.huMeas
  have hoInt := discounted_square_integrable
    (fun t => competitorState x u t - state x t)
    x.rho x.hrho (hoMeas.sub hsMeas)
    (GSTStage35.competitor_difference_growth x u huMeas huBound)
  have hU : 0 ≤ x.U := (toCostateData x).hU
  have huGrowth : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
      |u t - x.u t| ≤ M * (1 + t) := by
    refine ⟨x.U, hU, ?_⟩
    intro t ht
    have hb : |u t - x.u t| ≤ x.U :=
      GSTStage33.abs_sub_le_common_upper (u t) (x.u t) x.U
        (huBound t ht).1 (huBound t ht).2
        (x.hu t ht).1 (x.hu t ht).2
    have hupper : x.U ≤ x.U * (1 + t) := by
      nlinarith [mul_nonneg hU ht]
    exact hb.trans hupper
  have huInt := discounted_square_integrable
    (fun t => u t - x.u t) x.rho x.hrho
    (huMeas.sub x.huMeas) huGrowth
  have heq : gap x r u =
      (fun t => x.q * (Real.exp (-x.rho * t) *
          (competitorState x u t - state x t) ^ 2) +
        r * (Real.exp (-x.rho * t) * (u t - x.u t) ^ 2)) := by
    funext t
    dsimp [gap]
    ring
  rw [heq]
  exact (hoInt.const_mul x.q).add (huInt.const_mul r)

theorem cost_difference_integrable
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    IntegrableOn (costDifference x r u) (Ioi (0 : ℝ)) := by
  have huInt := discounted_cost_integrable x r u huMeas huBound
  have hvInt := discounted_cost_integrable x r x.u x.huMeas x.hu
  have heq : costDifference x r u =
      (fun t => discountedCost x r u t - discountedCost x r x.u t) := by
    funext t
    dsimp [costDifference, discountedCost, competitorState, state]
    ring
  rw [heq]
  exact huInt.sub hvInt

theorem partial_integrals_converge
    (x : StateData) (r : ℝ) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, discountedCost x r u t)
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), discountedCost x r u t)) ∧
    Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, gap x r u t)
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), gap x r u t)) ∧
    Tendsto
      (fun T : ℝ => ∫ t in (0 : ℝ)..T, costDifference x r u t)
      atTop (𝓝 (∫ t in Ioi (0 : ℝ), costDifference x r u t)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact intervalIntegral_tendsto_integral_Ioi 0
      (discounted_cost_integrable x r u huMeas huBound) tendsto_id
  · exact intervalIntegral_tendsto_integral_Ioi 0
      (gap_integrable x r u huMeas huBound) tendsto_id
  · exact intervalIntegral_tendsto_integral_Ioi 0
      (cost_difference_integrable x r u huMeas huBound) tendsto_id

#print axioms shifted_linear_growth
#print axioms discounted_square_integrable
#print axioms control_linear_growth
#print axioms discounted_cost_integrable
#print axioms gap_integrable
#print axioms cost_difference_integrable
#print axioms partial_integrals_converge

end GSTStage36
