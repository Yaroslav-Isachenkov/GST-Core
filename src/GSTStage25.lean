import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic.Linarith

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage25

noncomputable def tail (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Ioi t, g s

theorem finite_interval_integrable
    (g : ℝ → ℝ) (T : ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ))) (hT : 0 ≤ T) :
    IntervalIntegrable g volume 0 T := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr
  exact hg.mono_set (fun _ hx => hx.1)

theorem tail_representation
    (g : ℝ → ℝ) (t : ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ))) (ht : 0 ≤ t) :
    tail g t = tail g 0 - ∫ s in (0 : ℝ)..t, g s := by
  have hgt : IntegrableOn g (Ioi t) :=
    hg.mono_set (fun _ hx => lt_of_le_of_lt ht hx)
  have hsum := intervalIntegral.integral_interval_add_Ioi hg hgt
  unfold tail
  linarith

-- Transfer absolute continuity between functions equal on the interval.
theorem ac_congr_on
    (f g : ℝ → ℝ) (a b : ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b)
    (heq : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro epsilon hepsilon
  obtain ⟨delta, hdelta, hsmall⟩ := hf epsilon hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro E hE hlength
  have hsum :
      (∑ i ∈ Finset.range E.1,
        dist (g (E.2 i).1) (g (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1,
        dist (f (E.2 i).1) (f (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← heq (hE.1 i hi).1, ← heq (hE.1 i hi).2]
  rw [hsum]
  exact hsmall E hE hlength

theorem tail_ac
    (g : ℝ → ℝ) (T : ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ))) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (tail g) 0 T := by
  have hi := finite_interval_integrable g T hg hT
  have hzero : (0 : ℝ) ∈ uIcc (0 : ℝ) T := by
    simp
  have hprimitive :
      AbsolutelyContinuousOnInterval
        (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s) 0 T :=
    hi.absolutelyContinuousOnInterval_intervalIntegral hzero
  have hconstant :
      AbsolutelyContinuousOnInterval
        (fun _ : ℝ => tail g 0) 0 T := by
    simp [AbsolutelyContinuousOnInterval]
    exact tendsto_const_nhds
  have hmodel :
      AbsolutelyContinuousOnInterval
        (fun t : ℝ => tail g 0 - ∫ s in (0 : ℝ)..t, g s) 0 T :=
    hconstant.fun_sub hprimitive
  apply ac_congr_on
    (fun t : ℝ => tail g 0 - ∫ s in (0 : ℝ)..t, g s)
    (tail g) 0 T hmodel
  intro t ht
  have hmem : t ∈ Icc (0 : ℝ) T := by
    simpa only [uIcc_of_le hT] using ht
  exact (tail_representation g t hg hmem.1).symm

-- The endpoint t=0 is excluded by a null set.
-- For positive t, the representation holds on a neighbourhood of t.
theorem tail_derivative_ae
    (g : ℝ → ℝ) (T : ℝ)
    (hg : IntegrableOn g (Ioi (0 : ℝ))) (hT : 0 ≤ T) :
    ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (tail g) (-g t) t := by
  have hi := finite_interval_integrable g T hg hT
  have hzero : (0 : ℝ) ∈ uIcc (0 : ℝ) T := by
    simp
  have hne : ∀ᵐ t : ℝ, t ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hi.ae_hasDerivAt_integral, hne] with t hd htne
  intro ht
  have hmem : t ∈ Icc (0 : ℝ) T := by
    simpa only [uIcc_of_le hT] using ht
  have htpos : 0 < t := by
    have ht0 := hmem.1
    exact lt_of_le_of_ne ht0 (Ne.symm htne)
  have hmodel :
      HasDerivAt
        (fun x : ℝ => tail g 0 - ∫ s in (0 : ℝ)..x, g s)
        (-g t) t := by
    simpa only [zero_sub] using
      (hasDerivAt_const t (tail g 0)).sub (hd ht 0 hzero)
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds htpos] with x hx
  exact tail_representation g x hg (le_of_lt hx)

#print axioms finite_interval_integrable
#print axioms tail_representation
#print axioms ac_congr_on
#print axioms tail_ac
#print axioms tail_derivative_ae

end GSTStage25
