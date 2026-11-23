import GSTStage118

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage118

namespace GSTStage119

theorem resource_kernel_representation
    (u : ℝ → ℝ) (eta B initial t : ℝ) :
    resource u eta B initial t =
      initial * Real.exp (-cumulative u eta t) +
        B * ∫ s in (0 : ℝ)..t,
          Real.exp (cumulative u eta s - cumulative u eta t) := by
  have he :
      (fun s => Real.exp (cumulative u eta s - cumulative u eta t)) =
        (fun s => Real.exp (-cumulative u eta t) *
          Real.exp (cumulative u eta s)) := by
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, intervalIntegral.integral_const_mul]
  unfold resource
  ring

theorem exp_neg_lipschitz
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    |Real.exp (-A) - Real.exp (-B)| ≤ |A - B| := by
  have h := GSTStage12.exp_distance_bound
    0 (-A) (-B) (neg_nonpos.mpr hA) (neg_nonpos.mpr hB)
  calc
    |Real.exp (-A) - Real.exp (-B)| ≤ |-A - -B| := by
      simpa only [Real.dist_eq, Real.exp_zero, one_mul] using h
    _ = |A - B| := by
      rw [show -A - -B = -(A - B) by ring, abs_neg]

theorem convex_cumulative_difference_bound
    (x : StateData) (v : ℝ → ℝ) (ε t : ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ s : ℝ, 0 ≤ s → 0 ≤ v s ∧ v s ≤ x.U)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    |cumulative (convexControl x.u v ε) x.eta t -
      cumulative x.u x.eta t| ≤ ε * x.eta * x.U * t := by
  have hadm := convex_control_admissible
    x.u v x.U ε x.huMeas hvMeas x.hu hvBound hε0 hε1
  have hpInt := GSTStage27.bounded_control_integrable
    (convexControl x.u v ε) x.U t ht hadm.1 hadm.2
  have huInt := GSTStage27.bounded_control_integrable
    x.u x.U t ht x.huMeas x.hu

  have hdiff (s : ℝ) (hs : 0 ≤ s) :
      |convexControl x.u v ε s - x.u s| ≤ ε * x.U := by
    have hb := GSTStage33.abs_sub_le_common_upper
      (v s) (x.u s) x.U
      (hvBound s hs).1 (hvBound s hs).2
      (x.hu s hs).1 (x.hu s hs).2
    have he :
        convexControl x.u v ε s - x.u s =
          ε * (v s - x.u s) := by
      unfold convexControl
      ring
    rw [he, abs_mul, abs_of_nonneg hε0]
    exact mul_le_mul_of_nonneg_left hb hε0

  have hi :
      |∫ s in (0 : ℝ)..t,
        convexControl x.u v ε s - x.u s| ≤ (ε * x.U) * t := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := t) (C := ε * x.U)
      (f := fun s => convexControl x.u v ε s - x.u s)
      (by
        intro s hs
        rw [uIoc_of_le ht] at hs
        simpa only [Real.norm_eq_abs] using hdiff s hs.1.le)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] using hn

  have he :
      cumulative (convexControl x.u v ε) x.eta t -
        cumulative x.u x.eta t =
      x.eta * ∫ s in (0 : ℝ)..t,
        convexControl x.u v ε s - x.u s := by
    rw [intervalIntegral.integral_sub hpInt huInt]
    unfold cumulative
    ring

  rw [he, abs_mul, abs_of_nonneg x.heta.le]
  calc
    x.eta * |∫ s in (0 : ℝ)..t,
        convexControl x.u v ε s - x.u s|
        ≤ x.eta * ((ε * x.U) * t) :=
      mul_le_mul_of_nonneg_left hi x.heta.le
    _ = ε * x.eta * x.U * t := by ring

end GSTStage119

#print axioms GSTStage119.resource_kernel_representation
#print axioms GSTStage119.exp_neg_lipschitz
#print axioms GSTStage119.convex_cumulative_difference_bound
