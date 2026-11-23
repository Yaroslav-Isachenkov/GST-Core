import GSTStage158

open Set Filter
open scoped Topology
open GSTStage151

namespace GSTStage159

noncomputable def saturationEnd (a : ℝ) : ℝ :=
  a + 20 * Real.log 2

theorem saturationEnd_gt (a : ℝ) :
    a < saturationEnd a := by
  have hlog : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  dsimp [saturationEnd]
  linarith

theorem satClock_at_saturationEnd (a : ℝ) :
    satClock a (saturationEnd a) = 2 := by
  have he :
      (saturationEnd a - a) / 20 = Real.log 2 := by
    dsimp [saturationEnd]
    ring
  unfold satClock
  rw [he]
  exact Real.exp_log (by norm_num)

theorem satClock_bounds_until_end (a t : ℝ)
    (ht : t ∈ Ioc a (saturationEnd a)) :
    1 < satClock a t ∧ satClock a t ≤ 2 := by
  have harg : 0 < (t - a) / 20 := by
    linarith only [ht.1]
  have hupper : (t - a) / 20 ≤ Real.log 2 := by
    have h := ht.2
    dsimp [saturationEnd] at h
    linarith only [h]
  constructor
  · have h := Real.exp_lt_exp.mpr harg
    simpa only [Real.exp_zero, satClock] using h
  · have h := Real.exp_le_exp.mpr hupper
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
    exact h

theorem strict_prefix_of_eventually_right
    (w : ℝ → ℝ) (a T c : ℝ)
    (haT : a < T)
    (hp : ∀ᶠ t in 𝓝[>] a, c < w t) :
    ∃ b : ℝ, a < b ∧ b ≤ T ∧
      ∀ t ∈ Ioc a b, c < w t := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hp
  let δ : ℝ := min ε (T - a) / 2
  have hmin : 0 < min ε (T - a) :=
    lt_min hε (sub_pos.mpr haT)
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith only [hmin]
  have hδε : δ < ε := by
    have hle := min_le_left ε (T - a)
    dsimp [δ]
    linarith only [hle, hε]
  have hδT : δ ≤ T - a := by
    have hle := min_le_right ε (T - a)
    dsimp [δ]
    linarith only [hle, haT]
  refine ⟨a + δ, by linarith, by linarith, ?_⟩
  intro t ht
  apply hball
  refine ⟨?_, ht.1⟩
  change dist t a < ε
  rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
  linarith only [ht.2, hδε]

end GSTStage159

#print axioms GSTStage159.saturationEnd_gt
#print axioms GSTStage159.satClock_at_saturationEnd
#print axioms GSTStage159.satClock_bounds_until_end
#print axioms GSTStage159.strict_prefix_of_eventually_right
