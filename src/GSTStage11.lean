import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage11

noncomputable def cumulative
    (u : ℝ → ℝ) (eta t : ℝ) : ℝ :=
  eta * ∫ s in (0 : ℝ)..t, u s

noncomputable def resource
    (u : ℝ → ℝ) (eta B initial t : ℝ) : ℝ :=
  Real.exp (-cumulative u eta t) *
    (initial + B * ∫ s in (0 : ℝ)..t,
      Real.exp (cumulative u eta s))

theorem cumulative_ac
    (u : ℝ → ℝ) (eta T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    AbsolutelyContinuousOnInterval
      (cumulative u eta) 0 T := by
  have hi : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in (0 : ℝ)..t, u s) 0 T :=
    hu.absolutelyContinuousOnInterval_intervalIntegral
      (left_mem_uIcc)
  simpa only [cumulative] using hi.const_mul eta

-- Continuity of the explicit resource formula on a finite interval.
theorem resource_continuousOn
    (u : ℝ → ℝ) (eta B initial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    ContinuousOn (resource u eta B initial) (uIcc 0 T) := by
  have hA := (cumulative_ac u eta T hu).continuousOn
  have he : ContinuousOn
      (fun t => Real.exp (cumulative u eta t)) (uIcc 0 T) :=
    hA.rexp
  have heint : IntervalIntegrable
      (fun t => Real.exp (cumulative u eta t)) volume 0 T :=
    he.intervalIntegrable
  have hI : AbsolutelyContinuousOnInterval
      (fun t => ∫ s in (0 : ℝ)..t,
        Real.exp (cumulative u eta s)) 0 T :=
    heint.absolutelyContinuousOnInterval_intervalIntegral
      (left_mem_uIcc)
  have hsum : ContinuousOn
      (fun t => initial + B * ∫ s in (0 : ℝ)..t,
        Real.exp (cumulative u eta s)) (uIcc 0 T) :=
    continuousOn_const.add (hI.const_mul B).continuousOn
  simpa only [resource] using hA.neg.rexp.mul hsum

theorem resource_initial
    (u : ℝ → ℝ) (eta B initial : ℝ) :
    resource u eta B initial 0 = initial := by
  simp [resource, cumulative]

theorem resource_lower_bound
    (u : ℝ → ℝ) (eta B initial t : ℝ)
    (hB : 0 ≤ B) (ht : 0 ≤ t) :
    initial * Real.exp (-cumulative u eta t) ≤
      resource u eta B initial t := by
  have hI : 0 ≤ ∫ s in (0 : ℝ)..t,
      Real.exp (cumulative u eta s) :=
    intervalIntegral.integral_nonneg_of_forall ht
      (fun s => le_of_lt (Real.exp_pos _))
  have hsum : initial ≤ initial +
      B * ∫ s in (0 : ℝ)..t,
        Real.exp (cumulative u eta s) :=
    le_add_of_nonneg_right (mul_nonneg hB hI)
  have hmul := mul_le_mul_of_nonneg_left hsum
    (le_of_lt (Real.exp_pos (-cumulative u eta t)))
  simpa only [resource, mul_comm] using hmul

theorem resource_positive
    (u : ℝ → ℝ) (eta B initial t : ℝ)
    (hB : 0 ≤ B) (hinitial : 0 < initial) (ht : 0 ≤ t) :
    0 < resource u eta B initial t := by
  exact lt_of_lt_of_le
    (mul_pos hinitial (Real.exp_pos _))
    (resource_lower_bound u eta B initial t hB ht)

-- The control bound is only required almost everywhere
-- on the interval being considered.
theorem resource_quantitative_lower_bound
    (u : ℝ → ℝ) (eta B initial U t : ℝ)
    (heta : 0 ≤ eta) (hB : 0 ≤ B)
    (hinitial : 0 ≤ initial) (ht : 0 ≤ t)
    (hu : IntervalIntegrable u volume 0 t)
    (hupper : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) t),
      u s ≤ U) :
    initial * Real.exp (-(eta * U * t)) ≤
      resource u eta B initial t := by
  have hconst : IntervalIntegrable
      (fun _ : ℝ => U) volume 0 t :=
    intervalIntegrable_const
  have hint : (∫ s in (0 : ℝ)..t, u s) ≤ t * U := by
    have h := intervalIntegral.integral_mono_ae_restrict
      ht hu hconst hupper
    simpa using h
  have hA : cumulative u eta t ≤ eta * U * t := by
    have h := mul_le_mul_of_nonneg_left hint heta
    dsimp [cumulative]
    nlinarith
  have he :
      Real.exp (-(eta * U * t)) ≤
        Real.exp (-cumulative u eta t) :=
    Real.exp_le_exp.mpr (neg_le_neg hA)
  exact le_trans
    (mul_le_mul_of_nonneg_left he hinitial)
    (resource_lower_bound u eta B initial t hB ht)

#print axioms cumulative_ac
#print axioms resource_continuousOn
#print axioms resource_initial
#print axioms resource_lower_bound
#print axioms resource_positive
#print axioms resource_quantitative_lower_bound

end GSTStage11
