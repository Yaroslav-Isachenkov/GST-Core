import GSTStage54

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31

namespace GSTStage55

theorem s_continuous_on_interval
    (x : StateData) (T : ℝ) (hT : 0 ≤ T) :
    ContinuousOn (S x) (Icc (0 : ℝ) T) := by
  have h : ContinuousOn (S x) (uIcc (0 : ℝ) T) :=
    GSTStage28.s_continuous (toCostateData x) T hT
  rwa [uIcc_of_le hT] at h

-- The maximum is positive and interior, but need not be strict or unique.
theorem positive_interior_maximum
    (f : ℝ → ℝ) (T s : ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hzero : f 0 ≤ 0) (hterminal : f T ≤ 0)
    (hs : s ∈ Icc (0 : ℝ) T) (hpositive : 0 < f s) :
    ∃ m : ℝ, 0 < m ∧ m < T ∧ 0 < f m ∧
      (∀ t ∈ Icc (0 : ℝ) T, f t ≤ f m) ∧
      (∀ᶠ t in 𝓝 m, f t ≤ f m) := by
  obtain ⟨m, hm, hmax⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_isMaxOn
      ⟨s, hs⟩ hf
  have hbound : ∀ t ∈ Icc (0 : ℝ) T, f t ≤ f m :=
    isMaxOn_iff.mp hmax
  have hmpositive : 0 < f m :=
    lt_of_lt_of_le hpositive (hbound s hs)
  have hmzero : 0 < m := by
    by_contra hnot
    have heq : m = 0 := le_antisymm (le_of_not_gt hnot) hm.1
    have hnonpos : f m ≤ 0 := by
      simpa only [heq] using hzero
    exact (not_lt_of_ge hnonpos) hmpositive
  have hmT : m < T := by
    by_contra hnot
    have heq : m = T := le_antisymm hm.2 (le_of_not_gt hnot)
    have hnonpos : f m ≤ 0 := by
      simpa only [heq] using hterminal
    exact (not_lt_of_ge hnonpos) hmpositive
  refine ⟨m, hmzero, hmT, hmpositive, hbound, ?_⟩
  filter_upwards [Icc_mem_nhds hmzero hmT] with t ht
  exact hbound t ht

theorem candidate_s_positive_interior_maximum
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hthreshold :
      x.omegaInitial < x.rho * x.target / (x.rho + x.a))
    (hclip : GSTStage44.Clipping x r)
    (s : ℝ) (hs : 0 ≤ s) (hpositive : 0 < S x s) :
    ∃ T m : ℝ, s < T ∧
      0 < m ∧ m < T ∧ 0 < S x m ∧
      (∀ t ∈ Icc (0 : ℝ) T, S x t ≤ S x m) ∧
      (∀ᶠ t in 𝓝 m, S x t ≤ S x m) := by
  have hk : 0 < x.rho + x.a := (toCostateData x).hdecay
  have hscaled :
      x.omegaInitial * (x.rho + x.a) < x.rho * x.target :=
    (lt_div_iff₀ hk).mp hthreshold
  have hoTarget : x.omegaInitial < x.target := by
    by_contra hn
    have hbound := mul_le_mul_of_nonneg_left
      (le_of_not_gt hn) x.hrho.le
    nlinarith [mul_pos ho ha]
  have hSzero : S x 0 < 0 :=
    GSTStage53.s_initial_negative x ha hq ho hthreshold
  obtain ⟨T, hsT, hST⟩ :=
    GSTStage54.candidate_s_nonpos_later
      x r hr hi ha hq hoTarget hclip s hs
  have hT : 0 ≤ T := le_trans hs hsT.le
  obtain ⟨m, hmzero, hmT, hmpositive, hmax, hlocal⟩ :=
    positive_interior_maximum (S x) T s
      (s_continuous_on_interval x T hT)
      hSzero.le hST ⟨hs, hsT.le⟩ hpositive
  exact ⟨T, m, hsT, hmzero, hmT, hmpositive, hmax, hlocal⟩

#print axioms s_continuous_on_interval
#print axioms positive_interior_maximum
#print axioms candidate_s_positive_interior_maximum

end GSTStage55
