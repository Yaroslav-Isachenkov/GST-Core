import GSTStage04
import GSTStage32

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage32

namespace GSTStage33

theorem resource_upper
    (u : ℝ → ℝ) (eta B initial U T : ℝ)
    (hT : 0 ≤ T) (heta : 0 ≤ eta)
    (hB : 0 ≤ B) (hi : 0 ≤ initial)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U) :
    resource u eta B initial T ≤ initial + B * T := by
  have hu := GSTStage27.bounded_control_integrable
    u U T hT huMeas huBound
  have hAC := GSTStage12.resource_ac u eta B initial T hu
  have hODE := GSTStage12.resource_ode_ae u eta B initial T hu
  have hderiv : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      deriv (resource u eta B initial) t ≤ B := by
    filter_upwards [hODE] with t ht
    intro hmem
    have hmem' : t ∈ Icc (0 : ℝ) T := by
      rwa [uIcc_of_le hT] at hmem
    rw [(ht hmem).deriv]
    have hn := mul_nonneg
      (mul_nonneg heta (huBound t hmem'.1).1)
      (GSTStage30.resource_nonneg u eta B initial t hB hi hmem'.1)
    linarith
  have h := GSTStage30.ac_endpoint_upper
    (resource u eta B initial) B T hT hAC hderiv
  simpa only [resource_initial] using h

theorem abs_sub_le_common_upper
    (a b R : ℝ)
    (ha0 : 0 ≤ a) (haR : a ≤ R)
    (hb0 : 0 ≤ b) (hbR : b ≤ R) :
    |a - b| ≤ R := by
  apply abs_le.mpr
  constructor <;> linarith

theorem resource_difference_bound
    (x : StateData) (u : ℝ → ℝ) (t : ℝ)
    (ht : 0 ≤ t) (huMeas : Measurable u)
    (huBound : ∀ s : ℝ, 0 ≤ s → 0 ≤ u s ∧ u s ≤ x.U) :
    |resource u x.eta x.B x.phiInitial t -
      resource x.u x.eta x.B x.phiInitial t| ≤
      (x.phiInitial + x.B) * (1 + t) := by
  have hleft := resource_upper
    u x.eta x.B x.phiInitial x.U t ht
    (le_of_lt x.heta) x.hB x.hphiInitial huMeas huBound
  have hright := resource_upper
    x.u x.eta x.B x.phiInitial x.U t ht
    (le_of_lt x.heta) x.hB x.hphiInitial x.huMeas x.hu
  have habs := abs_sub_le_common_upper
    (resource u x.eta x.B x.phiInitial t)
    (resource x.u x.eta x.B x.phiInitial t)
    (x.phiInitial + x.B * t)
    (GSTStage30.resource_nonneg
      u x.eta x.B x.phiInitial t x.hB x.hphiInitial ht)
    hleft
    (GSTStage30.resource_nonneg
      x.u x.eta x.B x.phiInitial t x.hB x.hphiInitial ht)
    hright
  apply le_trans habs
  have hn := mul_nonneg x.hphiInitial ht
  nlinarith [x.hB]

theorem mixed_aestronglyMeasurable
    (x : StateData) (u : ℝ → ℝ) (huMeas : Measurable u) :
    AEStronglyMeasurable (comparisonIntegrand x u)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hdcont : ContinuousOn (d x) (Ici (0 : ℝ)) := by
    apply continuousOn_nonnegative_of_finite
    intro T hT
    exact ((state_costates_verified x).1 T hT).continuousOn
  have hdcont' : ContinuousOn (d x) (Ioi (0 : ℝ)) := by
    apply hdcont.mono
    intro t ht
    change (0 : ℝ) < t at ht
    change (0 : ℝ) ≤ t
    exact le_of_lt ht
  have hd : AEStronglyMeasurable (d x)
      (volume.restrict (Ioi (0 : ℝ))) :=
    hdcont'.aestronglyMeasurable measurableSet_Ioi
  have he : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-x.rho * t))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((continuous_const.mul continuous_id).rexp.measurable).stronglyMeasurable.aestronglyMeasurable
  have hr :
      AEStronglyMeasurable
        (fun t =>
          resource u x.eta x.B x.phiInitial t -
          resource x.u x.eta x.B x.phiInitial t)
        (volume.restrict (Ioi (0 : ℝ))) :=
    ((resource_measurable u x.eta x.B x.phiInitial huMeas).sub
      (resource_measurable x.u x.eta x.B x.phiInitial x.huMeas)).stronglyMeasurable.aestronglyMeasurable
  have hc : AEStronglyMeasurable (fun t => u t - x.u t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (huMeas.sub x.huMeas).stronglyMeasurable.aestronglyMeasurable
  exact ((he.mul hd).mul hr).mul hc

theorem mixed_polynomial_envelope
    (x : StateData) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, 0 ≤ t →
        |comparisonIntegrand x u t| ≤
          C * (1 + t ^ (2 : ℕ)) * Real.exp (-x.rho * t) := by
  obtain ⟨D, hD, hd⟩ := (state_costates_verified x).2.2.1
  have hU : 0 ≤ x.U := le_trans (x.hu 0 le_rfl).1 (x.hu 0 le_rfl).2
  have hR : 0 ≤ x.phiInitial + x.B :=
    add_nonneg x.hphiInitial x.hB
  have hK : 0 ≤ D * (x.phiInitial + x.B) * x.U :=
    mul_nonneg (mul_nonneg hD hR) hU
  refine ⟨2 * (D * (x.phiInitial + x.B) * x.U),
    mul_nonneg (by norm_num) hK, ?_⟩
  intro t ht
  have htime : 0 ≤ 1 + t := by linarith
  have hdu : |u t - x.u t| ≤ x.U :=
    abs_sub_le_common_upper (u t) (x.u t) x.U
      (huBound t ht).1 (huBound t ht).2
      (x.hu t ht).1 (x.hu t ht).2
  have hphi := resource_difference_bound x u t ht huMeas huBound
  have hpoly : (1 + t) ^ (2 : ℕ) ≤ 2 * (1 + t ^ (2 : ℕ)) := by
    nlinarith [sq_nonneg (t - 1)]
  have he : 0 ≤ Real.exp (-x.rho * t) := le_of_lt (Real.exp_pos _)
  change
    |Real.exp (-x.rho * t) * d x t *
      (resource u x.eta x.B x.phiInitial t -
        resource x.u x.eta x.B x.phiInitial t) *
      (u t - x.u t)| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he]
  calc
    Real.exp (-x.rho * t) * |d x t| *
        |resource u x.eta x.B x.phiInitial t -
          resource x.u x.eta x.B x.phiInitial t| *
        |u t - x.u t|
      ≤ (Real.exp (-x.rho * t) * (D * (1 + t)) *
          ((x.phiInitial + x.B) * (1 + t))) * x.U := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hd t ht) he
          · exact hphi
          · exact abs_nonneg _
          · exact mul_nonneg he (mul_nonneg hD htime)
        · exact hdu
        · exact abs_nonneg _
        · exact mul_nonneg
            (mul_nonneg he (mul_nonneg hD htime))
            (mul_nonneg hR htime)
    _ = (Real.exp (-x.rho * t) *
          (D * (x.phiInitial + x.B) * x.U)) *
          (1 + t) ^ (2 : ℕ) := by ring
    _ ≤ (Real.exp (-x.rho * t) *
          (D * (x.phiInitial + x.B) * x.U)) *
          (2 * (1 + t ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hpoly (mul_nonneg he hK)
    _ = (2 * (D * (x.phiInitial + x.B) * x.U)) *
          (1 + t ^ (2 : ℕ)) * Real.exp (-x.rho * t) := by ring

theorem mixed_integrable_and_limit
    (x : StateData) (u : ℝ → ℝ)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    IntegrableOn (comparisonIntegrand x u) (Ioi (0 : ℝ)) ∧
      Tendsto
        (fun T : ℝ => ∫ t in (0 : ℝ)..T, comparisonIntegrand x u t)
        atTop
        (𝓝 (∫ t in Ioi (0 : ℝ), comparisonIntegrand x u t)) := by
  obtain ⟨C, _hC, hb⟩ := mixed_polynomial_envelope x u huMeas huBound
  have hm := mixed_aestronglyMeasurable x u huMeas
  have hb' : ∀ t : ℝ, 0 < t →
      |comparisonIntegrand x u t| ≤
        C * (1 + t ^ (2 : ℕ)) * Real.exp (-x.rho * t) :=
    fun t ht => hb t (le_of_lt ht)
  exact ⟨
    GSTStage04.dominated_integrable
      (comparisonIntegrand x u) x.rho C 2 x.hrho hm hb',
    GSTStage04.partial_integrals_converge
      (comparisonIntegrand x u) x.rho C 2 x.hrho hm hb'
  ⟩

theorem mixed_infinite_nonpos
    (x : StateData) (u : ℝ → ℝ)
    (hphiInitial : 0 < x.phiInitial)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0)
    (huMeas : Measurable u)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) :
    (∫ t in Ioi (0 : ℝ), comparisonIntegrand x u t) ≤ 0 := by
  obtain ⟨C, _hC, hb⟩ := mixed_polynomial_envelope x u huMeas huBound
  apply GSTStage04.improper_integral_nonpos
    (comparisonIntegrand x u) x.rho C 2 x.hrho
    (mixed_aestronglyMeasurable x u huMeas)
    (fun t ht => hb t (le_of_lt ht))
  intro T hT
  exact GSTStage32.state_finite_mixed_nonpos
    x u T hT hphiInitial hS
    (GSTStage27.bounded_control_integrable u x.U T hT huMeas huBound)

#print axioms resource_upper
#print axioms abs_sub_le_common_upper
#print axioms resource_difference_bound
#print axioms mixed_aestronglyMeasurable
#print axioms mixed_polynomial_envelope
#print axioms mixed_integrable_and_limit
#print axioms mixed_infinite_nonpos

end GSTStage33
