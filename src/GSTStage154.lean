import GSTStage153

open GSTStage147

namespace GSTStage154

noncomputable def saturationRemainder (P X : ℝ) : ℝ :=
  (3 * P / 5 - 8 / 3) * X ^ 2 +
  (4 * P / 5 - 14 / 3) * X + 3 * P / 5 - 6

theorem zero_source_product_decomposition
    (P M F Z X : ℝ) (hX : X ≠ 0)
    (hF : F = 1 / 10 - 3 * P / 400) :
    satResource F 0 X * satDifference P M F Z 0 X =
      1 / 5 +
      (X - 1) * (1 / 5 +
        F * (X - 1) ^ 2 / X ^ 3 * saturationRemainder P X) +
      M * F * (8 * X ^ 2 - 5 * X - 3 / X ^ 3) +
      X / 20 * (20 * F * P - 4 - F * Z) := by
  dsimp [satResource, satDifference, satP, satZ,
    satA, satC, satD, saturationRemainder]
  rw [hF]
  field_simp [hX]
  ring

theorem saturation_M_coefficient_nonneg
    (X : ℝ) (hX : 1 ≤ X) :
    0 ≤ 8 * X ^ 2 - 5 * X - 3 / X ^ 3 := by
  have hpos : 0 < X := by linarith
  have hsub : 0 ≤ X - 1 := sub_nonneg.mpr hX
  have he :
      8 * X ^ 2 - 5 * X - 3 / X ^ 3 =
      (X - 1) * (8 * X ^ 4 + 3 * X ^ 3 +
        3 * X ^ 2 + 3 * X + 3) / X ^ 3 := by
    field_simp [ne_of_gt hpos]
    ring
  rw [he]
  positivity

theorem zero_source_product_lower
    (P M F Z X : ℝ)
    (hX : 1 ≤ X) (hM : 0 ≤ M) (hFnonneg : 0 ≤ F)
    (hF : F = 1 / 10 - 3 * P / 400)
    (hsat : 1 / 5 ≤ F * (P - Z / 20)) :
    1 / 5 +
      (X - 1) * (1 / 5 +
        F * (X - 1) ^ 2 / X ^ 3 * saturationRemainder P X) ≤
      satResource F 0 X * satDifference P M F Z 0 X := by
  have hpos : 0 < X := by linarith
  have hslack : 0 ≤ 20 * F * P - 4 - F * Z := by
    nlinarith only [hsat]
  have hcoef := saturation_M_coefficient_nonneg X hX
  have hMterm :
      0 ≤ M * F * (8 * X ^ 2 - 5 * X - 3 / X ^ 3) :=
    mul_nonneg (mul_nonneg hM hFnonneg) hcoef
  have hZterm : 0 ≤ X / 20 * (20 * F * P - 4 - F * Z) :=
    mul_nonneg (by positivity) hslack
  have he := zero_source_product_decomposition P M F Z X
    (ne_of_gt hpos) hF
  linarith only [he, hMterm, hZterm]

end GSTStage154

#print axioms GSTStage154.zero_source_product_decomposition
#print axioms GSTStage154.saturation_M_coefficient_nonneg
#print axioms GSTStage154.zero_source_product_lower
