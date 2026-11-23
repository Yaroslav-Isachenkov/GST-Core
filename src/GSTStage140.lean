import GSTStage139

namespace GSTStage140

theorem fixed_saturation_stationary_bounds
    (P M F Z B : ℝ)
    (_hP : 0 < P) (hM : 0 < M)
    (hFnonneg : 0 ≤ F) (hZ : 0 ≤ Z) (hB : 0 ≤ B)
    (hF : F = 1 / 10 - 3 * P / 400)
    (hsecond : 3 / 200 * M + 3 / 2000 * P - 1 / 100 + 2 * B ≤ 0)
    (hsaturation : 1 / 5 ≤ F * (P - Z / 20)) :
    (12 / 5 < P ∧ P < 20 / 3) ∧
    (1 / 20 < F ∧ F < 41 / 500) ∧
    (1 / 5 ≤ F * P ∧ F * P ≤ 1 / 3) ∧
    (0 ≤ Z ∧ Z ≤ 8 * P) := by
  have hPupper : P < 20 / 3 := by
    nlinarith only [hsecond, hM, hB]
  have hFZ : 0 ≤ F * Z := mul_nonneg hFnonneg hZ
  have hFPlower : 1 / 5 ≤ F * P := by
    nlinarith only [hsaturation, hFZ]
  have hFP : F * P = P / 10 - 3 * P ^ 2 / 400 := by
    rw [hF]
    ring
  have hPlower : 12 / 5 < P := by
    by_contra hn
    have hp : P ≤ 12 / 5 := le_of_not_gt hn
    nlinarith only [hFPlower, hFP, hp, sq_nonneg (P - 12 / 5)]
  have hFlower : 1 / 20 < F := by
    nlinarith only [hF, hPupper]
  have hFupper : F < 41 / 500 := by
    nlinarith only [hF, hPlower]
  have hFPupper : F * P ≤ 1 / 3 := by
    nlinarith only [hFP, sq_nonneg (P - 20 / 3)]
  have hZupper : Z ≤ 8 * P := by
    by_contra hn
    have hz : 8 * P < Z := lt_of_not_ge hn
    have hf : 0 < F := by
      linarith only [hFlower]
    have hprod : 0 < F * (Z - 8 * P) :=
      mul_pos hf (sub_pos.mpr hz)
    nlinarith only [hsaturation, hFPupper, hprod]
  exact ⟨⟨hPlower, hPupper⟩, ⟨hFlower, hFupper⟩,
    ⟨hFPlower, hFPupper⟩, ⟨hZ, hZupper⟩⟩

end GSTStage140

#print axioms GSTStage140.fixed_saturation_stationary_bounds
