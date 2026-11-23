import GSTStage171
import Mathlib.Tactic.FieldSimp

namespace GSTStage172

theorem corner_control_iff_thresholds
    (a c eta h s U B : ℝ)
    (ha : 0 < a) (hc : 0 < c) (heta : 0 < eta)
    (hh : 0 < h) (hs : 0 < s) :
    (∃ v : ℝ, 0 ≤ v ∧ v ≤ U ∧
      0 ≤ -a * h + c * s * v ∧
      0 ≤ B - eta * s * v) ↔
    (a * h / (c * s) ≤ U ∧ eta * a * h / c ≤ B) := by
  have hcs : 0 < c * s := mul_pos hc hs
  constructor
  · rintro ⟨v, _hv0, hvU, hstate, hresource⟩
    constructor
    · apply (div_le_iff₀ hcs).2
      have hupper := mul_le_mul_of_nonneg_left hvU hcs.le
      nlinarith only [hstate, hupper]
    · apply (div_le_iff₀ hc).2
      have hstateScaled := mul_nonneg heta.le hstate
      have hresourceScaled := mul_nonneg hc.le hresource
      nlinarith only [hstateScaled, hresourceScaled]
  · rintro ⟨hU, hB⟩
    let v : ℝ := a * h / (c * s)
    have hv0 : 0 ≤ v := (div_pos (mul_pos ha hh) hcs).le
    have hbalance : c * s * v = a * h := by
      dsimp [v]
      field_simp
    have hBmul : eta * a * h ≤ B * c :=
      (div_le_iff₀ hc).mp hB
    have hscaled := congrArg (fun z : ℝ => eta * z) hbalance
    have hresource : 0 ≤ B - eta * s * v := by
      have hproduct : 0 ≤ c * (B - eta * s * v) := by
        nlinarith only [hBmul, hscaled]
      by_contra hn
      have hnegative : c * (B - eta * s * v) < 0 :=
        mul_neg_of_pos_of_neg hc (lt_of_not_ge hn)
      exact (not_lt_of_ge hproduct) hnegative
    refine ⟨v, hv0, hU, ?_, hresource⟩
    nlinarith only [hbalance]

end GSTStage172

#print axioms GSTStage172.corner_control_iff_thresholds
