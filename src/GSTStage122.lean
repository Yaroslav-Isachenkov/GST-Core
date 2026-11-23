import GSTStage121

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage32 GSTStage34 GSTStage118

namespace GSTStage122

def resourceVariationBound (x : StateData) (t : ℝ) : ℝ :=
  x.eta * x.U * t * (x.phiInitial + x.B * t)

def stateVariationBound (x : StateData) (t : ℝ) : ℝ :=
  x.c * x.U * t * (x.phiInitial + x.B * t) *
    (1 + x.eta * x.U * t)

theorem convex_control_difference_bound
    (x : StateData) (v : ℝ → ℝ) (ε t : ℝ)
    (hvBound : ∀ s : ℝ, 0 ≤ s → 0 ≤ v s ∧ v s ≤ x.U)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    |convexControl x.u v ε t - x.u t| ≤ ε * x.U := by
  have hb := GSTStage33.abs_sub_le_common_upper
    (v t) (x.u t) x.U
    (hvBound t ht).1 (hvBound t ht).2
    (x.hu t ht).1 (x.hu t ht).2
  have he : convexControl x.u v ε t - x.u t =
      ε * (v t - x.u t) := by
    unfold convexControl
    ring
  rw [he, abs_mul, abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left hb hε

theorem mixed_convex_quadratic_bound
    (x : StateData) (v : ℝ → ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ s : ℝ, 0 ≤ s → 0 ≤ v s ∧ v s ≤ x.U) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ t : ℝ, 0 ≤ t →
        |comparisonIntegrand x (convexControl x.u v ε) t| ≤
          ε ^ 2 * (Real.exp (-x.rho * t) *
            (D * (1 + t)) * resourceVariationBound x t * x.U) := by
  obtain ⟨D, hD, hd⟩ := (state_costates_verified x).2.2.1
  refine ⟨D, hD, ?_⟩
  intro ε hε0 hε1 t ht
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  have htime : 0 ≤ 1 + t := by linarith
  have hR : 0 ≤ resourceVariationBound x t := by
    unfold resourceVariationBound
    exact mul_nonneg
      (mul_nonneg (mul_nonneg x.heta.le hU) ht)
      (add_nonneg x.hphiInitial (mul_nonneg x.hB ht))
  have he : 0 ≤ Real.exp (-x.rho * t) := (Real.exp_pos _).le
  have hphi :
      |resource (convexControl x.u v ε) x.eta x.B x.phiInitial t -
        resource x.u x.eta x.B x.phiInitial t| ≤
          ε * resourceVariationBound x t := by
    have h := GSTStage120.resource_convex_difference_bound
      x v ε t hvMeas hvBound hε0 hε1 ht
    calc
      |resource (convexControl x.u v ε) x.eta x.B x.phiInitial t -
          resource x.u x.eta x.B x.phiInitial t|
          ≤ ε * x.eta * x.U * t * (x.phiInitial + x.B * t) := h
      _ = ε * resourceVariationBound x t := by
        unfold resourceVariationBound
        ring
  have hu := convex_control_difference_bound x v ε t hvBound hε0 ht
  change
    |Real.exp (-x.rho * t) * d x t *
      (resource (convexControl x.u v ε) x.eta x.B x.phiInitial t -
        resource x.u x.eta x.B x.phiInitial t) *
      (convexControl x.u v ε t - x.u t)| ≤ _
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he]
  calc
    Real.exp (-x.rho * t) * |d x t| *
        |resource (convexControl x.u v ε) x.eta x.B x.phiInitial t -
          resource x.u x.eta x.B x.phiInitial t| *
        |convexControl x.u v ε t - x.u t|
      ≤ (Real.exp (-x.rho * t) * (D * (1 + t)) *
          (ε * resourceVariationBound x t)) * (ε * x.U) := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hd t ht) he
          · exact hphi
          · exact abs_nonneg _
          · exact mul_nonneg he (mul_nonneg hD htime)
        · exact hu
        · exact abs_nonneg _
        · exact mul_nonneg
            (mul_nonneg he (mul_nonneg hD htime))
            (mul_nonneg hε0 hR)
    _ = ε ^ 2 * (Real.exp (-x.rho * t) *
        (D * (1 + t)) * resourceVariationBound x t * x.U) := by ring

theorem gap_convex_quadratic_bound
    (x : StateData) (r : ℝ) (v : ℝ → ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ s : ℝ, 0 ≤ s → 0 ≤ v s ∧ v s ≤ x.U)
    (ε t : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    |gap x r (convexControl x.u v ε) t| ≤
      ε ^ 2 * (Real.exp (-x.rho * t) *
        (|x.q| * (stateVariationBound x t) ^ 2 + |r| * x.U ^ 2)) := by
  have hU : 0 ≤ x.U := (x.hu 0 le_rfl).1.trans (x.hu 0 le_rfl).2
  have hW : 0 ≤ stateVariationBound x t := by
    unfold stateVariationBound
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg x.hc hU) ht)
        (add_nonneg x.hphiInitial (mul_nonneg x.hB ht)))
      (add_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg x.heta.le hU) ht))
  have hstate :
      |competitorState x (convexControl x.u v ε) t - state x t| ≤
        ε * stateVariationBound x t := by
    have h := GSTStage121.competitor_convex_difference_bound
      x v ε t hvMeas hvBound hε0 hε1 ht
    have heq : competitorState x x.u t = state x t := rfl
    rw [heq] at h
    calc
      |competitorState x (convexControl x.u v ε) t - state x t|
          ≤ ε * x.c * x.U * t * (x.phiInitial + x.B * t) *
            (1 + x.eta * x.U * t) := h
      _ = ε * stateVariationBound x t := by
        unfold stateVariationBound
        ring
  have hu := convex_control_difference_bound x v ε t hvBound hε0 ht

  have hsquare :
      (competitorState x (convexControl x.u v ε) t - state x t) ^ 2 ≤
        ε ^ 2 * (stateVariationBound x t) ^ 2 := by
    calc
      (competitorState x (convexControl x.u v ε) t - state x t) ^ 2 =
          |competitorState x (convexControl x.u v ε) t - state x t| *
          |competitorState x (convexControl x.u v ε) t - state x t| := by
        rw [← pow_two, sq_abs]
      _ ≤ (ε * stateVariationBound x t) *
          (ε * stateVariationBound x t) :=
        mul_le_mul hstate hstate (abs_nonneg _) (mul_nonneg hε0 hW)
      _ = ε ^ 2 * (stateVariationBound x t) ^ 2 := by ring
  have husquare :
      (convexControl x.u v ε t - x.u t) ^ 2 ≤ ε ^ 2 * x.U ^ 2 := by
    calc
      (convexControl x.u v ε t - x.u t) ^ 2 =
          |convexControl x.u v ε t - x.u t| *
          |convexControl x.u v ε t - x.u t| := by
        rw [← pow_two, sq_abs]
      _ ≤ (ε * x.U) * (ε * x.U) :=
        mul_le_mul hu hu (abs_nonneg _) (mul_nonneg hε0 hU)
      _ = ε ^ 2 * x.U ^ 2 := by ring

  have he : 0 ≤ Real.exp (-x.rho * t) := (Real.exp_pos _).le
  unfold gap
  rw [abs_mul, abs_of_nonneg he]
  calc
    Real.exp (-x.rho * t) *
        |x.q * (competitorState x (convexControl x.u v ε) t - state x t)^2 +
          r * (convexControl x.u v ε t - x.u t)^2|
      ≤ Real.exp (-x.rho * t) *
        (|x.q * (competitorState x (convexControl x.u v ε) t - state x t)^2| +
          |r * (convexControl x.u v ε t - x.u t)^2|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) he
    _ = Real.exp (-x.rho * t) *
        (|x.q| * (competitorState x (convexControl x.u v ε) t - state x t)^2 +
          |r| * (convexControl x.u v ε t - x.u t)^2) := by
        simp only [abs_mul,
          abs_of_nonneg (sq_nonneg
            (competitorState x (convexControl x.u v ε) t - state x t)),
          abs_of_nonneg (sq_nonneg (convexControl x.u v ε t - x.u t))]
    _ ≤ Real.exp (-x.rho * t) *
        (|x.q| * (ε ^ 2 * (stateVariationBound x t)^2) +
          |r| * (ε ^ 2 * x.U^2)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add
            (mul_le_mul_of_nonneg_left hsquare (abs_nonneg _))
            (mul_le_mul_of_nonneg_left husquare (abs_nonneg _))) he
    _ = ε ^ 2 * (Real.exp (-x.rho * t) *
        (|x.q| * (stateVariationBound x t)^2 + |r| * x.U^2)) := by ring

end GSTStage122

#print axioms GSTStage122.convex_control_difference_bound
#print axioms GSTStage122.mixed_convex_quadratic_bound
#print axioms GSTStage122.gap_convex_quadratic_bound
