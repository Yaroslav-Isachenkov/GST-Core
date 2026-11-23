import GSTStage09
import GSTStage11
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11

namespace GSTStage12

theorem exp_distance_bound
    (M x y : ℝ) (hx : x ≤ M) (hy : y ≤ M) :
    dist (Real.exp x) (Real.exp y) ≤
      Real.exp M * dist x y := by
  have hderiv : ∀ z ∈ Iic M,
      HasDerivWithinAt Real.exp (Real.exp z) (Iic M) z := by
    intro z hz
    exact (Real.hasDerivAt_exp z).hasDerivWithinAt
  have hbound : ∀ z ∈ Iic M, ‖Real.exp z‖ ≤ Real.exp M := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos z)]
    exact Real.exp_le_exp.mpr hz
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_Iic M) hy hx
  simpa only [Real.norm_eq_abs, Real.dist_eq] using h

-- Exponentiation preserves AC on each compact interval.
theorem exp_ac
    (f : ℝ → ℝ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval
      (fun t => Real.exp (f t)) a b := by
  obtain ⟨M, hM⟩ := hf.exists_bound
  apply GSTStage09.composition_ac f Real.exp a b (Real.exp M) hf
  intro s hs t ht
  have hsM : f s ≤ M := by
    have h := hM s hs
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self (f s)).trans h
  have htM : f t ≤ M := by
    have h := hM t ht
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self (f t)).trans h
  exact exp_distance_bound M (f s) (f t) hsM htM

theorem resource_ac
    (u : ℝ → ℝ) (eta B initial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    AbsolutelyContinuousOnInterval
      (resource u eta B initial) 0 T := by
  have hA := cumulative_ac u eta T hu
  have he := exp_ac (cumulative u eta) 0 T hA
  have heint : IntervalIntegrable
      (fun t => Real.exp (cumulative u eta t)) volume 0 T :=
    he.continuousOn.intervalIntegrable
  have hI : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in (0 : ℝ)..t,
        Real.exp (cumulative u eta s)) 0 T :=
    heint.absolutelyContinuousOnInterval_intervalIntegral
      (left_mem_uIcc)
  have hnegative : AbsolutelyContinuousOnInterval
      (fun t => Real.exp (-cumulative u eta t)) 0 T :=
    exp_ac (fun t => -cumulative u eta t) 0 T hA.neg
  have hsum := (GSTStage09.constant_ac 0 T initial).fun_add
    (hI.const_mul B)
  simpa only [resource] using hnegative.fun_mul hsum

theorem resource_ode_ae
    (u : ℝ → ℝ) (eta B initial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (resource u eta B initial)
        (B - eta * u t * resource u eta B initial t) t := by
  have hAcont := (cumulative_ac u eta T hu).continuousOn
  have heint : IntervalIntegrable
      (fun t => Real.exp (cumulative u eta t)) volume 0 T :=
    hAcont.rexp.intervalIntegrable
  filter_upwards
    [hu.ae_hasDerivAt_integral, heint.ae_hasDerivAt_integral]
    with t hdu hdi
  intro ht
  have hA : HasDerivAt (cumulative u eta) (eta * u t) t := by
    simpa only [cumulative] using
      (hdu ht 0 (left_mem_uIcc)).const_mul eta
  have hI : HasDerivAt
      (fun x => ∫ s in (0 : ℝ)..x,
        Real.exp (cumulative u eta s))
      (Real.exp (cumulative u eta t)) t :=
    hdi ht 0 (left_mem_uIcc)
  have hproduct :=
    hA.neg.exp.mul ((hI.const_mul B).const_add initial)
  have hcancel :
      Real.exp (-cumulative u eta t) *
        Real.exp (cumulative u eta t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hBcancel :
      B * (Real.exp (-cumulative u eta t) *
        Real.exp (cumulative u eta t)) = B := by
    rw [hcancel, mul_one]
  convert hproduct using 1
  dsimp [resource]
  nlinarith [hBcancel]

-- Initial condition, AC and the ODE are now combined.
-- This statement does not assert uniqueness.
theorem resource_is_solution
    (u : ℝ → ℝ) (eta B initial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    resource u eta B initial 0 = initial ∧
    AbsolutelyContinuousOnInterval
      (resource u eta B initial) 0 T ∧
    (∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (resource u eta B initial)
        (B - eta * u t * resource u eta B initial t) t) := by
  exact ⟨resource_initial u eta B initial,
    resource_ac u eta B initial T hu,
    resource_ode_ae u eta B initial T hu⟩

#print axioms exp_distance_bound
#print axioms exp_ac
#print axioms resource_ac
#print axioms resource_ode_ae
#print axioms resource_is_solution

end GSTStage12
