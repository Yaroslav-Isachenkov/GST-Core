import GSTStage152

open GSTStage147

namespace GSTStage153

theorem saturated_resource_ge_zero_source
    (F B X : ℝ) (hB : 0 ≤ B) (hX : 1 ≤ X) :
    satResource F 0 X ≤ satResource F B X := by
  have hpos : 0 < X := by linarith
  have hinv : 1 / X ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hpos).2
    linarith
  have hn : 0 ≤ 20 * B * (1 - 1 / X) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hinv)
  have he := saturated_resource_source_increment F B X
  linarith only [he, hn]

theorem saturated_difference_ge_zero_source
    (P M F Z B X : ℝ) (hB : 0 ≤ B) (hX : 1 ≤ X) :
    satDifference P M F Z 0 X ≤ satDifference P M F Z B X := by
  have hpos : 0 < X := by linarith
  have hsub : 0 ≤ X - 1 := sub_nonneg.mpr hX
  have hn : 0 ≤ (400 * B / (3 * X ^ 2)) *
      (X - 1) ^ 3 * (4 * X ^ 2 + 7 * X + 9) := by
    positivity
  have he := saturated_difference_source_increment
    P M F Z B X (ne_of_gt hpos)
  linarith only [he, hn]

theorem saturated_z_at_two
    (P M F Z B : ℝ)
    (hF : F = 1 / 10 - 3 * P / 400) :
    satZ P M F Z B 2 =
      70 / 3 - 44 * P - 245 * M + 4 * Z - 14000 * B / 3 := by
  dsimp [satZ, satA, satC, satD]
  rw [hF]
  ring

theorem saturated_z_at_two_negative
    (P M F Z B : ℝ)
    (hP : 12 / 5 < P) (hM : 0 < M)
    (hB : 0 ≤ B) (hZ : Z ≤ 8 * P)
    (hF : F = 1 / 10 - 3 * P / 400) :
    satZ P M F Z B 2 < -82 / 15 := by
  rw [saturated_z_at_two P M F Z B hF]
  linarith only [hP, hM, hB, hZ]

end GSTStage153

#print axioms GSTStage153.saturated_resource_ge_zero_source
#print axioms GSTStage153.saturated_difference_ge_zero_source
#print axioms GSTStage153.saturated_z_at_two
#print axioms GSTStage153.saturated_z_at_two_negative
