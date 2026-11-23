import GSTStage51
import Mathlib.Topology.Order.Compact

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage52

-- A first zero exists if a continuous function starts positive
-- and becomes nonpositive on a finite interval.
theorem exists_first_zero
    (f : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hzero : 0 < f 0) (hterminal : f T ≤ 0) :
    ∃ s : ℝ, 0 < s ∧ s ≤ T ∧ f s = 0 ∧
      ∀ t ∈ Ico (0 : ℝ) s, 0 < f t := by
  let Z : Set ℝ := {t | t ∈ Icc (0 : ℝ) T ∧ f t = 0}
  have hZclosed : IsClosed Z :=
    isClosed_Icc.isClosed_eq hf continuousOn_const
  have hZcompact : IsCompact Z :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).of_isClosed_subset
      hZclosed (fun t ht => ht.1)
  have hZnonempty : Z.Nonempty := by
    obtain ⟨t, ht, hft⟩ :=
      intermediate_value_Icc' hT hf
        (show (0 : ℝ) ∈ Icc (f T) (f 0) from ⟨hterminal, hzero.le⟩)
    exact ⟨t, ht, hft⟩
  obtain ⟨s, hsLeast⟩ := hZcompact.exists_isLeast hZnonempty
  have hsI : s ∈ Icc (0 : ℝ) T := hsLeast.1.1
  have hfs : f s = 0 := hsLeast.1.2
  have hs : 0 < s := by
    by_contra hnot
    have heq : s = 0 := le_antisymm (le_of_not_gt hnot) hsI.1
    have hf0 : f 0 = 0 := by simpa only [heq] using hfs
    linarith
  refine ⟨s, hs, hsI.2, hfs, ?_⟩
  intro t ht
  by_contra hnot
  have hft : f t ≤ 0 := le_of_not_gt hnot
  have htT : t ≤ T := le_trans ht.2.le hsI.2
  have hflocal : ContinuousOn f (Icc (0 : ℝ) t) :=
    hf.mono (fun y hy => ⟨hy.1, le_trans hy.2 htT⟩)
  obtain ⟨z, hz, hfz⟩ :=
    intermediate_value_Icc' ht.1 hflocal
      (show (0 : ℝ) ∈ Icc (f t) (f 0) from ⟨hft, hzero.le⟩)
  have hzZ : z ∈ Z := ⟨⟨hz.1, le_trans hz.2 htT⟩, hfz⟩
  have hsz : s ≤ z := hsLeast.2 hzZ
  linarith [hz.2, ht.2]

-- Left difference quotients at a first zero are nonpositive.
theorem derivative_nonpos_at_first_zero
    (f : ℝ → ℝ) (v s : ℝ)
    (hs : 0 < s) (hf : HasDerivAt f v s)
    (hzero : f s = 0)
    (hbefore : ∀ t ∈ Ico (0 : ℝ) s, 0 < f t) :
    v ≤ 0 := by
  have hslope : Tendsto (slope f s) (𝓝[<] s) (𝓝 v) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hf).1
  apply le_of_tendsto hslope
  have hpositive_time_full : ∀ᶠ t in 𝓝 s, (0 : ℝ) < t :=
    Ioi_mem_nhds hs
  have hpositive_time : ∀ᶠ t in 𝓝[<] s, (0 : ℝ) < t :=
    hpositive_time_full.filter_mono nhdsWithin_le_nhds
  filter_upwards [hpositive_time, self_mem_nhdsWithin] with t ht hts
  have hts' : t < s := hts
  have hft : 0 < f t := hbefore t ⟨ht.le, hts'⟩
  change (t - s)⁻¹ * (f t - f s) ≤ 0
  rw [hzero, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg
    (inv_nonpos.mpr (sub_nonpos.mpr hts'.le)) hft.le

theorem candidate_p_positive
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : x.omegaInitial < x.target)
    (hclip : GSTStage44.Clipping x r) :
    ∀ t : ℝ, 0 ≤ t → 0 < p x t := by
  have hp0 : 0 < p x 0 :=
    GSTStage50.candidate_p_initial_positive x r hr hi ha hq ho hclip
  have htarget : 0 < x.target :=
    lt_of_le_of_lt x.homegaInitial ho
  intro T hT
  by_contra hnot
  have hpT : p x T ≤ 0 := le_of_not_gt hnot
  have hcont : ContinuousOn (p x) (Icc (0 : ℝ) T) := by
    have h := (GSTStage28.p_solution (toCostateData x) T hT).1.continuousOn
    rw [uIcc_of_le hT] at h
    exact h
  obtain ⟨s, hs, _hsT, hps, hbefore⟩ :=
    exists_first_zero (p x) T hT hcont hp0 hpT
  have hder := GSTStage47.p_ode_at x s hs
  have hnonpos := derivative_nonpos_at_first_zero
    (p x) ((x.rho + x.a) * p x s +
      2 * x.q * (state x s - x.target))
    s hs hder hps hbefore
  rw [hps, mul_zero, zero_add] at hnonpos
  have hstate : state x s ≤ x.target := by
    by_contra hnotstate
    have hpositive :
        0 < 2 * x.q * (state x s - x.target) :=
      mul_pos (mul_pos (by norm_num) hq)
        (sub_pos.mpr (lt_of_not_ge hnotstate))
    exact (not_lt_of_ge hnonpos) hpositive
  have hpositive := GSTStage51.candidate_p_positive_of_state_le_target
    x r s hr hi ha hq htarget hs hclip hstate
  exact (ne_of_gt hpositive) hps

-- The two strict bounds on p are now available together.
theorem candidate_p_strict_bounds
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hoPositive : 0 < x.omegaInitial)
    (hoTarget : x.omegaInitial < x.target)
    (hclip : GSTStage44.Clipping x r) :
    ∀ t : ℝ, 0 ≤ t →
      0 < p x t ∧ p x t < 2 * x.q * x.target / (x.rho + x.a) := by
  intro t ht
  exact ⟨
    candidate_p_positive x r hr hi ha hq hoTarget hclip t ht,
    GSTStage45.p_strict_upper x hq hoPositive t ht
  ⟩

#print axioms exists_first_zero
#print axioms derivative_nonpos_at_first_zero
#print axioms candidate_p_positive
#print axioms candidate_p_strict_bounds

end GSTStage52
