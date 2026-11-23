import GSTStage189

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31

namespace GSTStage190

theorem candidate_state_bounds_of_S_nonpos
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hoTarget : x.omegaInitial < x.target)
    (hclip : GSTStage44.Clipping x r)
    (hS : ∀ t : ℝ, 0 ≤ t → S x t ≤ 0) :
    ∀ t : ℝ, 0 ≤ t →
      0 < state x t ∧
      state x t ≤ x.target - x.a * p x t / (2 * x.q) ∧
      x.target - x.a * p x t / (2 * x.q) < x.target := by
  intro t ht
  have hp : 0 < p x t :=
    GSTStage52.candidate_p_positive x r hr hi ha hq hoTarget hclip t ht
  have hs := hS t ht
  change x.a * p x t + 2 * x.q * (state x t - x.target) ≤ 0 at hs
  have hden : 0 < 2 * x.q := mul_pos (by norm_num) hq
  have hquot :
      x.a * p x t / (2 * x.q) ≤ x.target - state x t := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hs]
  have hquotPos : 0 < x.a * p x t / (2 * x.q) :=
    div_pos (mul_pos ha hp) hden
  refine ⟨GSTStage45.state_positive x ho t ht, ?_, ?_⟩
  · linarith only [hquot]
  · linarith only [hquotPos]

theorem candidate_state_bounds_under_thresholds
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hthreshold :
      x.omegaInitial < x.rho * x.target / (x.rho + x.a))
    (hdiscount : x.eta * x.U ≤ x.rho)
    (hrThreshold :
      x.a * x.q * x.target ^ 2 /
        (4 * x.U ^ 2 * (x.rho + x.a)) < r)
    (hclip : GSTStage44.Clipping x r) :
    ∀ t : ℝ, 0 ≤ t →
      0 < state x t ∧
      state x t ≤ x.target - x.a * p x t / (2 * x.q) ∧
      x.target - x.a * p x t / (2 * x.q) < x.target := by
  have hS := (GSTStage66.candidate_sufficiency_and_uniqueness
    x r hr hU hi ha hq ho hthreshold hdiscount hrThreshold hclip).1
  have hoTarget :=
    GSTStage65.initial_lt_target_of_threshold x ha ho hthreshold
  exact candidate_state_bounds_of_S_nonpos
    x r hr hi ha hq ho hoTarget hclip hS

end GSTStage190

#print axioms GSTStage190.candidate_state_bounds_of_S_nonpos
#print axioms GSTStage190.candidate_state_bounds_under_thresholds
