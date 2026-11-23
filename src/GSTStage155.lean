import GSTStage154

open GSTStage154

namespace GSTStage155

theorem saturation_remainder_lower
    (P X : ℝ) (hP : 12 / 5 ≤ P)
    (hXlo : 1 ≤ X) (hXhi : X ≤ 2) :
    -15 ≤ saturationRemainder P X := by
  have hXnonneg : 0 ≤ X := by linarith
  have hXsq : X ^ 2 ≤ 4 := by nlinarith
  have hD : 0 ≤ P - 12 / 5 := sub_nonneg.mpr hP
  have hDsq := mul_nonneg hD (sq_nonneg X)
  have hDX := mul_nonneg hD hXnonneg
  dsimp [saturationRemainder]
  nlinarith only [hDsq, hDX, hP, hXsq, hXhi]

theorem saturation_ratio_bounds
    (X : ℝ) (hXlo : 1 ≤ X) (hXhi : X ≤ 2) :
    0 ≤ (X - 1) ^ 2 / X ^ 3 ∧
    (X - 1) ^ 2 / X ^ 3 ≤ 1 / 8 := by
  have hpos : 0 < X := by linarith
  have hsub : 0 ≤ X - 1 := sub_nonneg.mpr hXlo
  have hfive : 0 ≤ 5 - X := by linarith
  have haux := mul_nonneg hsub hfive
  have hquad : 0 ≤ -X ^ 2 + 6 * X - 4 := by
    nlinarith only [haux]
  have hprod := mul_nonneg (sub_nonneg.mpr hXhi) hquad
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (pow_pos hpos 3)).2
  nlinarith only [hprod]

theorem saturation_remainder_bracket_lower
    (P F X : ℝ)
    (hP : 12 / 5 ≤ P)
    (hFnonneg : 0 ≤ F) (hFupper : F ≤ 41 / 500)
    (hXlo : 1 ≤ X) (hXhi : X ≤ 2) :
    37 / 800 ≤
      1 / 5 + F * (X - 1) ^ 2 / X ^ 3 * saturationRemainder P X := by
  have hR := saturation_remainder_lower P X hP hXlo hXhi
  obtain ⟨hYnonneg, hYupper⟩ := saturation_ratio_bounds X hXlo hXhi
  have hFYnonneg : 0 ≤ F * ((X - 1) ^ 2 / X ^ 3) :=
    mul_nonneg hFnonneg hYnonneg
  have hFYupper : F * ((X - 1) ^ 2 / X ^ 3) ≤ 41 / 4000 := by
    calc
      F * ((X - 1) ^ 2 / X ^ 3) ≤
          (41 / 500 : ℝ) * (1 / 8) :=
        mul_le_mul hFupper hYupper hYnonneg (by norm_num)
      _ = 41 / 4000 := by norm_num
  have hweighted := mul_le_mul_of_nonneg_left hR hFYnonneg
  have he :
      F * (X - 1) ^ 2 / X ^ 3 =
        F * ((X - 1) ^ 2 / X ^ 3) := by ring
  rw [he]
  nlinarith only [hweighted, hFYupper]

end GSTStage155

#print axioms GSTStage155.saturation_remainder_lower
#print axioms GSTStage155.saturation_ratio_bounds
#print axioms GSTStage155.saturation_remainder_bracket_lower
