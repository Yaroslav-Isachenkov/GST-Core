import GSTStage21
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set
open scoped Topology
open GSTStage21

namespace GSTStage22

-- Original future-integral definition from the core.
noncomputable def pCostate
    (omega : ℝ → ℝ) (rho a q target t : ℝ) : ℝ :=
  2 * q * ∫ s in Ioi t,
    Real.exp (-(rho + a) * (s - t)) * (target - omega s)

-- Explicit coefficient derived from the envelope integral.
noncomputable def pBound
    (rho a q target M : ℝ) : ℝ :=
  |2 * q| * ((|target| + M) * moment (rho + a))

-- Translation of the actual improper integral, without assuming convergence.
-- Convergence is established separately below.
theorem tail_integral_shift
    (g : ℝ → ℝ) (t : ℝ) :
    (∫ s in Ioi (0 : ℝ), g (t + s)) =
      ∫ s in Ioi t, g s := by
  have hind :
      (fun s => (Ioi t).indicator g (t + s)) =
        (Ioi (0 : ℝ)).indicator (fun s => g (t + s)) := by
    funext s
    have hcmp : (t < t + s) ↔ 0 < s := by
      constructor
      · intro hlt
        linarith
      · intro hpos
        linarith
    simp only [Set.indicator, mem_Ioi, hcmp]
  calc
    (∫ s in Ioi (0 : ℝ), g (t + s)) =
        ∫ s : ℝ, (Ioi (0 : ℝ)).indicator
          (fun x => g (t + x)) s :=
      (integral_indicator measurableSet_Ioi).symm
    _ = ∫ s : ℝ, (Ioi t).indicator g (t + s) := by rw [hind]
    _ = ∫ s : ℝ, (Ioi t).indicator g s :=
      integral_add_left_eq_self ((Ioi t).indicator g) t
    _ = ∫ s in Ioi t, g s :=
      integral_indicator measurableSet_Ioi

theorem tail_integrable_of_shift
    (g : ℝ → ℝ) (t : ℝ)
    (h : IntegrableOn (fun s => g (t + s)) (Ioi (0 : ℝ))) :
    IntegrableOn g (Ioi t) := by
  have hi : Integrable
      ((Ioi (0 : ℝ)).indicator (fun s => g (t + s))) :=
    h.integrable_indicator measurableSet_Ioi
  have hj := hi.comp_add_left (-t)
  have hind :
      (fun s => (Ioi (0 : ℝ)).indicator
        (fun x => g (t + x)) (-t + s)) =
      (Ioi t).indicator g := by
    funext s
    have hcmp : (0 < -t + s) ↔ t < s := by
      constructor
      · intro hpos
        linarith
      · intro hlt
        linarith
    have harg : t + (-t + s) = s := by ring
    simp only [Set.indicator, mem_Ioi, hcmp, harg]
  rw [hind] at hj
  exact (integrable_indicator_iff measurableSet_Ioi).mp hj

theorem p_shifted
    (omega : ℝ → ℝ) (rho a q target t : ℝ) :
    pCostate omega rho a q target t =
      2 * q * ∫ s in Ioi (0 : ℝ),
        Real.exp (-(rho + a) * s) * (target - omega (t + s)) := by
  unfold pCostate
  rw [← tail_integral_shift
    (fun s => Real.exp (-(rho + a) * (s - t)) *
      (target - omega s)) t]
  simp only [add_sub_cancel_left]

-- No growth hypothesis on p is assumed.
-- Continuity and linear growth of omega are explicit premises.
theorem p_integrable_and_bound
    (omega : ℝ → ℝ) (rho a q target M t : ℝ)
    (hdecay : 0 < rho + a) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hcont : ContinuousOn omega (Ici (0 : ℝ)))
    (hOmega : ∀ x : ℝ, 0 ≤ x → |omega x| ≤ M * (1 + x)) :
    IntegrableOn
      (fun s => Real.exp (-(rho + a) * (s - t)) *
        (target - omega s)) (Ioi t) ∧
      |pCostate omega rho a q target t| ≤
        pBound rho a q target M * (1 + t) := by
  have hcomp : ContinuousOn
      (fun s => omega (t + s)) (Ioi (0 : ℝ)) := by
    apply hcont.comp (continuous_const.add continuous_id).continuousOn
    intro s hs
    change 0 ≤ t + s
    have hs' : 0 < s := hs
    linarith
  have hfun : ContinuousOn
      (fun s => Real.exp (-(rho + a) * s) *
        (target - omega (t + s))) (Ioi (0 : ℝ)) :=
    ((continuous_const.mul continuous_id).rexp.continuousOn).mul
      (continuousOn_const.sub hcomp)
  have hinput : ∀ s : ℝ, 0 < s →
      |target - omega (t + s)| ≤ (|target| + M) * (1 + t + s) := by
    intro s hs
    have hx : 0 ≤ t + s := by linarith
    have ho := hOmega (t + s) hx
    have hsum :
        |target| + |omega (t + s)| ≤
          (|target| + M) * (1 + t + s) := by
      nlinarith [mul_nonneg (abs_nonneg target) hx]
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le target, le_abs_self (omega (t + s))]
    · linarith [le_abs_self target, neg_abs_le (omega (t + s))]
  obtain ⟨hi, hb⟩ := kernel_affine_integrable_and_bound
    (fun s => Real.exp (-(rho + a) * s))
    (fun s => target - omega (t + s))
    (rho + a) (|target| + M) t
    hdecay (add_nonneg (abs_nonneg target) hM) ht
    (hfun.aestronglyMeasurable measurableSet_Ioi)
    (fun s _hs => le_of_lt (Real.exp_pos _))
    (fun s _hs => le_refl _)
    hinput
  have hiOriginal : IntegrableOn
      (fun s => Real.exp (-(rho + a) * (s - t)) *
        (target - omega s)) (Ioi t) := by
    apply tail_integrable_of_shift
      (fun s => Real.exp (-(rho + a) * (s - t)) *
        (target - omega s)) t
    simpa only [add_sub_cancel_left] using hi
  refine ⟨hiOriginal, ?_⟩
  rw [p_shifted, abs_mul]
  calc
    |2 * q| *
        |∫ s in Ioi (0 : ℝ),
          Real.exp (-(rho + a) * s) * (target - omega (t + s))|
        ≤ |2 * q| *
          (((|target| + M) * (1 + t)) * moment (rho + a)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = pBound rho a q target M * (1 + t) := by
      unfold pBound
      ring

theorem p_linear_growth
    (omega : ℝ → ℝ) (rho a q target M : ℝ)
    (hdecay : 0 < rho + a) (hM : 0 ≤ M)
    (hcont : ContinuousOn omega (Ici (0 : ℝ)))
    (hOmega : ∀ x : ℝ, 0 ≤ x → |omega x| ≤ M * (1 + x)) :
    ∃ P : ℝ, 0 ≤ P ∧
      ∀ t : ℝ, 0 ≤ t →
        |pCostate omega rho a q target t| ≤ P * (1 + t) := by
  have hzero := (p_integrable_and_bound omega rho a q target M 0
    hdecay hM (le_refl 0) hcont hOmega).2
  have hP : 0 ≤ pBound rho a q target M := by
    have h := le_trans (abs_nonneg (pCostate omega rho a q target 0)) hzero
    simpa only [add_zero, mul_one] using h
  refine ⟨pBound rho a q target M, hP, ?_⟩
  intro t ht
  exact (p_integrable_and_bound omega rho a q target M t
    hdecay hM ht hcont hOmega).2

#print axioms tail_integral_shift
#print axioms tail_integrable_of_shift
#print axioms p_shifted
#print axioms p_integrable_and_bound
#print axioms p_linear_growth

end GSTStage22
