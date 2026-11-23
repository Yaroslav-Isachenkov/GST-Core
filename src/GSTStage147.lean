import GSTStage146
import Mathlib.Tactic.FieldSimp

namespace GSTStage147

noncomputable def satA (P M B : ℝ) : ℝ :=
  -1 + P / 10 + M / 2 + 200 * B

noncomputable def satC (P M B : ℝ) : ℝ :=
  3 * P / 10 - 4 / 3 + 4 * M + 800 * B / 3

noncomputable def satD (M Z B : ℝ) : ℝ :=
  Z - 200 / 3 + 100 * M + 40000 * B / 3

noncomputable def satResource (F B X : ℝ) : ℝ :=
  20 * B + (F - 20 * B) / X

noncomputable def satState (P M F B X : ℝ) : ℝ :=
  200 * B + 20 * (F - 20 * B) / X + satA P M B / X ^ 2

noncomputable def satP (P M F B X : ℝ) : ℝ :=
  40 / 3 * (1 - 200 * B) - 200 * (F - 20 * B) / X -
    8 * satA P M B / X ^ 2 + satC P M B * X ^ 3

noncomputable def satZ (P M F Z B X : ℝ) : ℝ :=
  400 / 3 * (1 - 200 * B) - 4000 / 3 * (F - 20 * B) / X -
    40 * satA P M B / X ^ 2 - 20 * satC P M B * X ^ 3 +
    satD M Z B * X ^ 2

noncomputable def satDifference (P M F Z B X : ℝ) : ℝ :=
  satP P M F B X - satZ P M F Z B X / 20

theorem saturated_profiles_initial_values
    (P M F Z B : ℝ)
    (hF : F = 1 / 10 - 3 * P / 400) :
    satResource F B 1 = F ∧
    satState P M F B 1 = 1 + M / 2 - P / 20 ∧
    satP P M F B 1 = P ∧
    satZ P M F Z B 1 = Z := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    dsimp [satResource, satState, satP, satZ, satA, satC, satD] <;>
    rw [hF] <;>
    ring

theorem saturated_resource_source_increment
    (F B X : ℝ) :
    satResource F B X - satResource F 0 X =
      20 * B * (1 - 1 / X) := by
  dsimp [satResource]
  ring

theorem saturated_difference_source_increment
    (P M F Z B X : ℝ) (hX : X ≠ 0) :
    satDifference P M F Z B X - satDifference P M F Z 0 X =
      (400 * B / (3 * X ^ 2)) *
        (X - 1) ^ 3 * (4 * X ^ 2 + 7 * X + 9) := by
  dsimp [satDifference, satP, satZ, satA, satC, satD]
  field_simp [hX]
  ring

end GSTStage147

#print axioms GSTStage147.saturated_profiles_initial_values
#print axioms GSTStage147.saturated_resource_source_increment
#print axioms GSTStage147.saturated_difference_source_increment
