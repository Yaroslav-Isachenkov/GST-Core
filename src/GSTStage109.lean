import GSTStage108

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage36

namespace GSTStage109

theorem weighted_sum_eventually_lower
    (S C : ℕ → ℝ) (s c q r : ℝ)
    (hr : 0 ≤ r)
    (hS : Tendsto S atTop (𝓝 s))
    (hC : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, c ≤ C n + ε) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, q * s + r * c ≤ q * S n + r * C n + ε := by
  intro ε hε
  have hq : Tendsto (fun n => q * S n) atTop (𝓝 (q * s)) :=
    (show Tendsto (fun _ : ℕ => q) atTop (𝓝 q) from
      tendsto_const_nhds).mul hS
  have hs : ∀ᶠ n in atTop, q * s - ε / 2 < q * S n :=
    (tendsto_order.1 hq).1 (q * s - ε / 2) (by linarith)
  let δ : ℝ := (ε / 2) / (r + 1)
  have hr1 : 0 < r + 1 := by linarith
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact div_pos (half_pos hε) hr1
  have hδeq : δ * (r + 1) = ε / 2 := by
    dsimp only [δ]
    exact div_mul_cancel₀ _ (ne_of_gt hr1)
  have hc := hC δ hδ
  filter_upwards [hs, hc] with n hsn hcn
  have hm := mul_le_mul_of_nonneg_left hcn hr
  nlinarith [hm, hδeq]

theorem discounted_cost_integral_split
    (x : StateData) (r : ℝ) (u : ℝ → ℝ) (T : ℝ)
    (hstate : IntegrableOn
      (fun t => Real.exp (-x.rho * t) *
        (competitorState x u t - x.target) ^ 2)
      (Icc (0 : ℝ) T))
    (hcontrol : IntegrableOn
      (fun t => Real.exp (-x.rho * t) * (u t) ^ 2)
      (Icc (0 : ℝ) T)) :
    (∫ t in Icc (0 : ℝ) T, discountedCost x r u t) =
      x.q * (∫ t in Icc (0 : ℝ) T,
        Real.exp (-x.rho * t) * (competitorState x u t - x.target) ^ 2) +
      r * (∫ t in Icc (0 : ℝ) T,
        Real.exp (-x.rho * t) * (u t) ^ 2) := by
  have he : discountedCost x r u =
      (fun t => x.q * (Real.exp (-x.rho * t) *
        (competitorState x u t - x.target) ^ 2) +
        r * (Real.exp (-x.rho * t) * (u t) ^ 2)) := by
    funext t
    dsimp only [discountedCost, GSTStage06.runningCost]
    ring
  rw [he, integral_add (hstate.const_mul x.q) (hcontrol.const_mul r),
    integral_const_mul, integral_const_mul]

end GSTStage109

#print axioms GSTStage109.weighted_sum_eventually_lower
#print axioms GSTStage109.discounted_cost_integral_split
