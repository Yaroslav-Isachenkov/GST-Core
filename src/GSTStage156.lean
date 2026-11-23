import GSTStage155

open GSTStage147 GSTStage153 GSTStage154 GSTStage155

namespace GSTStage156

theorem zero_source_product_margin
    (P M F Z X : ℝ)
    (hP : 12 / 5 ≤ P) (hM : 0 ≤ M)
    (hFnonneg : 0 ≤ F) (hFupper : F ≤ 41 / 500)
    (hF : F = 1 / 10 - 3 * P / 400)
    (hsat : 1 / 5 ≤ F * (P - Z / 20))
    (hXlo : 1 ≤ X) (hXhi : X ≤ 2) :
    1 / 5 + 37 / 800 * (X - 1) ≤
      satResource F 0 X * satDifference P M F Z 0 X := by
  have hlower := zero_source_product_lower
    P M F Z X hXlo hM hFnonneg hF hsat
  have hbracket := saturation_remainder_bracket_lower
    P F X hP hFnonneg hFupper hXlo hXhi
  have hscaled := mul_le_mul_of_nonneg_left
    hbracket (sub_nonneg.mpr hXlo)
  nlinarith only [hlower, hscaled]

theorem saturated_product_margin
    (P M F Z B X : ℝ)
    (hP : 12 / 5 ≤ P) (hM : 0 ≤ M)
    (hFnonneg : 0 ≤ F) (hFupper : F ≤ 41 / 500)
    (hB : 0 ≤ B)
    (hF : F = 1 / 10 - 3 * P / 400)
    (hsat : 1 / 5 ≤ F * (P - Z / 20))
    (hXlo : 1 ≤ X) (hXhi : X ≤ 2) :
    1 / 5 + 37 / 800 * (X - 1) ≤
      satResource F B X * satDifference P M F Z B X := by
  have hzero := zero_source_product_margin
    P M F Z X hP hM hFnonneg hFupper hF hsat hXlo hXhi
  have hXpos : 0 < X := by linarith
  have hRzero : 0 ≤ satResource F 0 X := by
    simpa only [satResource, mul_zero, sub_zero, zero_add] using
      (div_nonneg hFnonneg hXpos.le)
  have hinc : 0 ≤ (37 / 800 : ℝ) * (X - 1) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hXlo)
  have hDzero : 0 ≤ satDifference P M F Z 0 X := by
    by_contra hn
    have hneg : satDifference P M F Z 0 X ≤ 0 :=
      (lt_of_not_ge hn).le
    have hprod := mul_nonpos_of_nonneg_of_nonpos hRzero hneg
    linarith only [hzero, hinc, hprod]
  have hR := saturated_resource_ge_zero_source F B X hB hXlo
  have hD := saturated_difference_ge_zero_source P M F Z B X hB hXlo
  have hRB : 0 ≤ satResource F B X := hRzero.trans hR
  have hprod :
      satResource F 0 X * satDifference P M F Z 0 X ≤
      satResource F B X * satDifference P M F Z B X :=
    mul_le_mul hR hD hDzero hRB
  exact hzero.trans hprod

theorem saturated_product_strictly_above_threshold
    (P M F Z B X : ℝ)
    (hP : 12 / 5 ≤ P) (hM : 0 ≤ M)
    (hFnonneg : 0 ≤ F) (hFupper : F ≤ 41 / 500)
    (hB : 0 ≤ B)
    (hF : F = 1 / 10 - 3 * P / 400)
    (hsat : 1 / 5 ≤ F * (P - Z / 20))
    (hXlo : 1 < X) (hXhi : X ≤ 2) :
    1 / 5 < satResource F B X * satDifference P M F Z B X := by
  have hlower := saturated_product_margin
    P M F Z B X hP hM hFnonneg hFupper hB hF hsat hXlo.le hXhi
  have hinc : 0 < (37 / 800 : ℝ) * (X - 1) :=
    mul_pos (by norm_num) (sub_pos.mpr hXlo)
  linarith only [hlower, hinc]

end GSTStage156

#print axioms GSTStage156.zero_source_product_margin
#print axioms GSTStage156.saturated_product_margin
#print axioms GSTStage156.saturated_product_strictly_above_threshold
