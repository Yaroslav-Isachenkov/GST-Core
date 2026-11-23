import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped Topology

namespace GSTStage21

noncomputable def envelope (beta s : ℝ) : ℝ :=
  Real.exp (-beta * s) + s * Real.exp (-beta * s)

noncomputable def moment (beta : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), envelope beta s

-- Integrability of the fixed exponential-affine envelope.
theorem envelope_integrable
    (beta : ℝ) (hbeta : 0 < beta) :
    IntegrableOn (envelope beta) (Ioi (0 : ℝ)) := by
  have h0 : IntegrableOn
      (fun s : ℝ => Real.exp (-beta * s)) (Ioi (0 : ℝ)) :=
    exp_neg_integrableOn_Ioi 0 hbeta
  have h1 : IntegrableOn
      (fun s : ℝ => s * Real.exp (-beta * s)) (Ioi (0 : ℝ)) := by
    simpa only [Real.rpow_one] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := beta)
        (by norm_num) (by norm_num) hbeta)
  exact h0.add h1

-- Pointwise domination; no assumptions about costates are used.
theorem kernel_affine_pointwise
    (beta C t s k f : ℝ)
    (hC : 0 ≤ C) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hk0 : 0 ≤ k)
    (hk : k ≤ Real.exp (-beta * s))
    (hf : |f| ≤ C * (1 + t + s)) :
    |k * f| ≤ (C * (1 + t)) * envelope beta s := by
  have hproduct : 1 + t + s ≤ (1 + t) * (1 + s) := by
    nlinarith [mul_nonneg ht hs]
  rw [abs_mul, abs_of_nonneg hk0]
  calc
    k * |f| ≤ Real.exp (-beta * s) * |f| :=
      mul_le_mul_of_nonneg_right hk (abs_nonneg f)
    _ ≤ Real.exp (-beta * s) * (C * (1 + t + s)) :=
      mul_le_mul_of_nonneg_left hf
        (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (-beta * s) * (C * ((1 + t) * (1 + s))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hproduct hC)
        (le_of_lt (Real.exp_pos _))
    _ = (C * (1 + t)) * envelope beta s := by
      unfold envelope
      ring

-- Both convergence and the integral estimate are proved.
theorem kernel_affine_integrable_and_bound
    (k f : ℝ → ℝ) (beta C t : ℝ)
    (hbeta : 0 < beta) (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hmeas : AEStronglyMeasurable (fun s => k s * f s)
      (volume.restrict (Ioi (0 : ℝ))))
    (hk0 : ∀ s : ℝ, 0 < s → 0 ≤ k s)
    (hk : ∀ s : ℝ, 0 < s → k s ≤ Real.exp (-beta * s))
    (hf : ∀ s : ℝ, 0 < s → |f s| ≤ C * (1 + t + s)) :
    IntegrableOn (fun s => k s * f s) (Ioi (0 : ℝ)) ∧
      |∫ s in Ioi (0 : ℝ), k s * f s|
        ≤ (C * (1 + t)) * moment beta := by
  have henv : Integrable
      (fun s => (C * (1 + t)) * envelope beta s)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (envelope_integrable beta hbeta).const_mul (C * (1 + t))
  have hbound : ∀ᵐ s ∂volume.restrict (Ioi (0 : ℝ)),
      ‖k s * f s‖ ≤ (C * (1 + t)) * envelope beta s := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall (fun s hs => by
      rw [Real.norm_eq_abs]
      exact kernel_affine_pointwise beta C t s (k s) (f s)
        hC ht (le_of_lt hs) (hk0 s hs) (hk s hs) (hf s hs))
  refine ⟨henv.mono' hmeas hbound, ?_⟩
  simpa only [Real.norm_eq_abs, integral_const_mul, moment] using
    (norm_integral_le_of_norm_le henv hbound)

-- A single finite real coefficient works for every t >= 0.
-- Its value is constructed, not introduced as a growth hypothesis.
theorem kernel_family_linear_growth
    (k f : ℝ → ℝ → ℝ) (beta C : ℝ)
    (hbeta : 0 < beta) (hC : 0 ≤ C)
    (hmeas : ∀ t : ℝ, 0 ≤ t →
      AEStronglyMeasurable (fun s => k t s * f t s)
        (volume.restrict (Ioi (0 : ℝ))))
    (hk0 : ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 0 < s → 0 ≤ k t s)
    (hk : ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 0 < s →
      k t s ≤ Real.exp (-beta * s))
    (hf : ∀ t : ℝ, 0 ≤ t → ∀ s : ℝ, 0 < s →
      |f t s| ≤ C * (1 + t + s)) :
    ∃ D : ℝ, ∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun s => k t s * f t s) (Ioi (0 : ℝ)) ∧
      |∫ s in Ioi (0 : ℝ), k t s * f t s| ≤ D * (1 + t) := by
  refine ⟨C * moment beta, ?_⟩
  intro t ht
  obtain ⟨hi, hb⟩ := kernel_affine_integrable_and_bound
    (k t) (f t) beta C t hbeta hC ht
    (hmeas t ht) (hk0 t ht) (hk t ht) (hf t ht)
  refine ⟨hi, ?_⟩
  calc
    |∫ s in Ioi (0 : ℝ), k t s * f t s|
        ≤ (C * (1 + t)) * moment beta := hb
    _ = (C * moment beta) * (1 + t) := by ring

#print axioms envelope_integrable
#print axioms kernel_affine_pointwise
#print axioms kernel_affine_integrable_and_bound
#print axioms kernel_family_linear_growth

end GSTStage21
