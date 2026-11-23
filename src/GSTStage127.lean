import GSTStage126

open MeasureTheory Set Filter
open scoped Topology

namespace GSTStage127

theorem clipping_bounds
    (r U w : ℝ) (hU : 0 ≤ U) :
    0 ≤ max 0 (min U (w / (2 * r))) ∧
      max 0 (min U (w / (2 * r))) ≤ U := by
  exact ⟨le_max_left _ _, max_le hU (min_le_left _ _)⟩

theorem clipping_stationarity_lower
    (r U w u : ℝ)
    (hr : 0 < r) (hU : 0 ≤ U)
    (hu0 : 0 ≤ u) (huU : u ≤ U) :
    let v := max 0 (min U (w / (2 * r)))
    2 * r * (v - u) ^ 2 ≤ (-2 * r * u + w) * (v - u) := by
  dsimp only
  by_cases hUzero : U = 0
  · have huzero : u = 0 := le_antisymm (hUzero ▸ huU) hu0
    simp [hUzero, huzero]
  · have hUpos : 0 < U := lt_of_le_of_ne hU (Ne.symm hUzero)
    have hsign := GSTStage07.clipping_variational_sign
      r U w u hr hUpos hu0 huU
    dsimp only at hsign
    nlinarith only [hsign]

theorem eq_clipping_of_stationarity_nonpos
    (r U w u : ℝ)
    (hr : 0 < r) (hU : 0 ≤ U)
    (hu0 : 0 ≤ u) (huU : u ≤ U)
    (hsign :
      (-2 * r * u + w) *
        (max 0 (min U (w / (2 * r))) - u) ≤ 0) :
    u = max 0 (min U (w / (2 * r))) := by
  have hlower := clipping_stationarity_lower r U w u hr hU hu0 huU
  dsimp only at hlower
  have hcoef : 0 < 2 * r := mul_pos (by norm_num) hr
  have hzero :
      2 * r * (max 0 (min U (w / (2 * r))) - u) ^ 2 = 0 :=
    le_antisymm (hlower.trans hsign)
      (mul_nonneg hcoef.le (sq_nonneg _))
  have hsquare :
      (max 0 (min U (w / (2 * r))) - u) ^ 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hcoef)
  have hsub : max 0 (min U (w / (2 * r))) - u = 0 :=
    sq_eq_zero_iff.mp hsquare
  exact (sub_eq_zero.mp hsub).symm

end GSTStage127

#print axioms GSTStage127.clipping_bounds
#print axioms GSTStage127.clipping_stationarity_lower
#print axioms GSTStage127.eq_clipping_of_stationarity_nonpos
