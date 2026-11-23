import GSTStage66
open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage36

namespace GSTStage67

theorem uniform_state_growth (x : StateData) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      ∀ t : ℝ, 0 ≤ t → |competitorState x u t| ≤ M * (1 + t) := by
  let A := x.eta * x.omegaInitial + x.c * x.phiInitial
  let D := x.c * x.B
  have hA : 0 ≤ A :=
    add_nonneg (mul_nonneg x.heta.le x.homegaInitial)
      (mul_nonneg x.hc x.hphiInitial)
  have hD : 0 ≤ D := mul_nonneg x.hc x.hB
  refine ⟨(A + D) / x.eta,
    div_nonneg (add_nonneg hA hD) x.heta.le, ?_⟩
  intro u hmeas hbound t ht
  have hui := GSTStage27.bounded_control_integrable
    u x.U t ht hmeas hbound
  have hu0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ u s :=
    fun s hs => (hbound s hs).1
  have hnonneg : 0 ≤ competitorState x u t :=
    GSTStage30.omega_nonneg
      u x.eta x.B x.phiInitial x.a x.c x.omegaInitial t
      x.hB x.hphiInitial x.hc x.homegaInitial ht hu0
  rw [abs_of_nonneg hnonneg]
  calc
    competitorState x u t ≤ (A + D * t) / x.eta := by
      exact GSTStage30.omega_upper
        u x.eta x.B x.phiInitial x.a x.c x.omegaInitial t
        ht x.heta x.ha x.hB x.hphiInitial x.hc x.homegaInitial hui hu0
    _ ≤ ((A + D) * (1 + t)) / x.eta := by
      apply div_le_div_of_nonneg_right _ x.heta.le
      nlinarith [mul_nonneg hA ht]
    _ = ((A + D) / x.eta) * (1 + t) := by ring

theorem uniform_cost_integrable_envelope
    (x : StateData) (r : ℝ) (hq : 0 ≤ x.q) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧
      IntegrableOn
        (fun t : ℝ => C * (1 + t ^ 2) * Real.exp (-x.rho * t))
        (Ioi (0 : ℝ)) ∧
      ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      ∀ t : ℝ, 0 ≤ t →
        0 ≤ discountedCost x r u t ∧
        discountedCost x r u t ≤
          C * (1 + t ^ 2) * Real.exp (-x.rho * t) := by
  obtain ⟨M, hM, hm⟩ := uniform_state_growth x
  let K := M + |x.target|
  have hK : 0 ≤ K := add_nonneg hM (abs_nonneg _)
  let C := 2 * x.q * K ^ 2 + r * x.U ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, GSTStage04.envelope_integrable x.rho C x.hrho 2, ?_⟩
  intro u hmeas hbound t ht
  have ht1 : 0 ≤ 1 + t := by linarith
  have hgrowth := hm u hmeas hbound t ht
  have hshift :
      |competitorState x u t - x.target| ≤ K * (1 + t) := by
    calc
      |competitorState x u t - x.target| ≤
          |competitorState x u t| + |x.target| := abs_sub _ _
      _ ≤ M * (1 + t) + |x.target| := by
        linarith
      _ ≤ K * (1 + t) := by
        dsimp [K]
        nlinarith [mul_nonneg (abs_nonneg x.target) ht]
  have hsquare :
      (competitorState x u t - x.target) ^ 2 ≤ K ^ 2 * (1 + t) ^ 2 := by
    calc
      (competitorState x u t - x.target) ^ 2 =
          |competitorState x u t - x.target| *
            |competitorState x u t - x.target| := by
        rw [← pow_two, sq_abs]
      _ ≤ (K * (1 + t)) * (K * (1 + t)) :=
        mul_le_mul hshift hshift (abs_nonneg _) (mul_nonneg hK ht1)
      _ = K ^ 2 * (1 + t) ^ 2 := by ring
  have htSquare : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (t - 1)]
  have hsBound :
      (competitorState x u t - x.target) ^ 2 ≤
        (2 * K ^ 2) * (1 + t ^ 2) := by
    have h := mul_le_mul_of_nonneg_left htSquare (sq_nonneg K)
    nlinarith [hsquare, h]
  have hub := hbound t ht
  have huSquare : (u t) ^ 2 ≤ x.U ^ 2 := by
    nlinarith [hub.1, hub.2]
  have hstateCost := mul_le_mul_of_nonneg_left hsBound hq
  have hcontrolCost := mul_le_mul_of_nonneg_left huSquare hr
  have htail : 0 ≤ (r * x.U ^ 2) * t ^ 2 :=
    mul_nonneg (mul_nonneg hr (sq_nonneg _)) (sq_nonneg _)
  have hsum :
      x.q * (competitorState x u t - x.target) ^ 2 + r * (u t) ^ 2 ≤
        C * (1 + t ^ 2) := by
    dsimp [C]
    nlinarith [hstateCost, hcontrolCost, htail]
  constructor
  · dsimp [discountedCost, GSTStage06.runningCost]
    exact mul_nonneg (Real.exp_pos _).le
      (add_nonneg (mul_nonneg hq (sq_nonneg _))
        (mul_nonneg hr (sq_nonneg _)))
  · calc
      discountedCost x r u t ≤
          Real.exp (-x.rho * t) * (C * (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
      _ = C * (1 + t ^ 2) * Real.exp (-x.rho * t) := by ring

#print axioms uniform_state_growth
#print axioms uniform_cost_integrable_envelope
end GSTStage67
