import GSTStage34
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage34

namespace GSTStage35

theorem p_linear_growth (x : StateData) :
    ∃ P : ℝ, 0 ≤ P ∧
      ∀ t : ℝ, 0 ≤ t → |p x t| ≤ P * (1 + t) := by
  exact GSTStage22.p_linear_growth
    (state x) x.rho x.a x.q x.target (growthConstant x)
    (toCostateData x).hdecay
    (toCostateData x).hM
    (toCostateData x).hcont
    (toCostateData x).hOmega

theorem z_linear_growth (x : StateData) :
    ∃ Z : ℝ, 0 ≤ Z ∧
      ∀ t : ℝ, 0 ≤ t → |z x t| ≤ Z * (1 + t) := by
  obtain ⟨P, hP, hp⟩ := p_linear_growth x
  have hpMeas : Measurable (p x) := by
    exact GSTStage24.p_measurable
      (state x) x.rho x.a x.q x.target
      (toCostateData x).hOmegaMeas
  have hm : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable
        (fun s => GSTStage23.zKernel x.u x.eta x.rho t (t + s) *
          (x.u (t + s) * p x (t + s)))
        (volume.restrict (Ioi (0 : ℝ))) := by
    intro t _ht
    exact GSTStage24.z_integrand_aestronglyMeasurable
      x.u (p x) x.eta x.rho t x.huMeas hpMeas
  exact GSTStage23.z_linear_growth
    x.u (p x) x.eta x.rho x.c x.U P
    x.heta.le x.hrho (toCostateData x).hU hP x.hu hp hm

theorem competitor_difference_growth
    (x : StateData) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t →
      |competitorState x u t - state x t| ≤ M * (1 + t) := by
  obtain ⟨A, hA, ha⟩ :=
    GSTStage30.admissible_omega_linear_growth
      u x.eta x.B x.phiInitial x.a x.c x.omegaInitial x.U
      x.heta x.ha x.hB x.hphiInitial x.hc x.homegaInitial
      huMeas huBound
  obtain ⟨B, hB, hb⟩ := state_linear_growth x
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro t ht
  have ha' : |competitorState x u t| ≤ A * (1 + t) := ha t ht
  calc
    |competitorState x u t - state x t|
        ≤ |competitorState x u t| + |state x t| :=
      abs_sub (competitorState x u t) (state x t)
    _ ≤ A * (1 + t) + B * (1 + t) :=
      add_le_add ha' (hb t ht)
    _ = (A + B) * (1 + t) := by ring

-- All growth bounds below are conclusions of earlier results.
-- Neither clipping nor S <= 0 is needed for boundary decay.
theorem boundary_polynomial_envelope
    (x : StateData) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |boundary x u t| ≤
        C * (1 + t ^ 2) * Real.exp (-x.rho * t) := by
  obtain ⟨P, hP, hp⟩ := p_linear_growth x
  obtain ⟨Z, hZ, hz⟩ := z_linear_growth x
  obtain ⟨M, hM, hm⟩ :=
    competitor_difference_growth x u huMeas huBound
  let R : ℝ := x.phiInitial + x.B
  have hR : 0 ≤ R := add_nonneg x.hphiInitial x.hB
  let K : ℝ := P * M + Z * R
  have hK : 0 ≤ K :=
    add_nonneg (mul_nonneg hP hM) (mul_nonneg hZ hR)
  refine ⟨2 * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro t ht
  have ht1 : 0 ≤ 1 + t := by linarith
  have hr :
      |resource u x.eta x.B x.phiInitial t -
        resource x.u x.eta x.B x.phiInitial t| ≤ R * (1 + t) :=
    GSTStage33.resource_difference_bound x u t ht huMeas huBound
  have hpterm :
      |p x t * (competitorState x u t - state x t)| ≤
        (P * (1 + t)) * (M * (1 + t)) := by
    rw [abs_mul]
    exact mul_le_mul (hp t ht) (hm t ht)
      (abs_nonneg _) (mul_nonneg hP ht1)
  have hzterm :
      |z x t * (resource u x.eta x.B x.phiInitial t -
        resource x.u x.eta x.B x.phiInitial t)| ≤
        (Z * (1 + t)) * (R * (1 + t)) := by
    rw [abs_mul]
    exact mul_le_mul (hz t ht) hr
      (abs_nonneg _) (mul_nonneg hZ ht1)
  have hsum :
      |p x t * (competitorState x u t - state x t) +
        z x t * (resource u x.eta x.B x.phiInitial t -
          resource x.u x.eta x.B x.phiInitial t)| ≤
        K * (1 + t) ^ 2 := by
    calc
      _ ≤ |p x t * (competitorState x u t - state x t)| +
          |z x t * (resource u x.eta x.B x.phiInitial t -
            resource x.u x.eta x.B x.phiInitial t)| :=
        abs_add_le _ _
      _ ≤ (P * (1 + t)) * (M * (1 + t)) +
          (Z * (1 + t)) * (R * (1 + t)) :=
        add_le_add hpterm hzterm
      _ = K * (1 + t) ^ 2 := by
        dsimp [K]
        ring
  have hsquare : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by
    nlinarith [sq_nonneg (t - 1)]
  have hpoly : K * (1 + t) ^ 2 ≤ (2 * K) * (1 + t ^ 2) := by
    calc
      K * (1 + t) ^ 2 ≤ K * (2 * (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left hsquare hK
      _ = (2 * K) * (1 + t ^ 2) := by ring
  calc
    |boundary x u t| =
        Real.exp (-x.rho * t) *
          |p x t * (competitorState x u t - state x t) +
            z x t * (resource u x.eta x.B x.phiInitial t -
              resource x.u x.eta x.B x.phiInitial t)| := by
      rw [boundary, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-x.rho * t) * (K * (1 + t) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ ≤ Real.exp (-x.rho * t) * ((2 * K) * (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left hpoly (Real.exp_pos _).le
    _ = (2 * K) * (1 + t ^ 2) * Real.exp (-x.rho * t) := by
      ring

theorem boundary_tendsto_zero
    (x : StateData) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    Tendsto (boundary x u) atTop (𝓝 0) := by
  obtain ⟨C, _hC, hb⟩ :=
    boundary_polynomial_envelope x u huMeas huBound
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    ?_
    (GSTStage20.discounted_polynomial_tendsto_zero x.rho C 2 x.hrho)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.norm_eq_abs]
  calc
    |boundary x u t| ≤ C * (1 + t ^ 2) * Real.exp (-x.rho * t) :=
      hb t ht
    _ = C * (Real.exp (-x.rho * t) +
          t ^ 2 * Real.exp (-x.rho * t)) := by ring

#print axioms p_linear_growth
#print axioms z_linear_growth
#print axioms competitor_difference_growth
#print axioms boundary_polynomial_envelope
#print axioms boundary_tendsto_zero

end GSTStage35
