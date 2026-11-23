import GSTStage117

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage32 GSTStage34 GSTStage37

namespace GSTStage118

def convexControl (u v : ℝ → ℝ) (ε : ℝ) (t : ℝ) : ℝ :=
  (1 - ε) * u t + ε * v t

theorem convex_control_admissible
    (u v : ℝ → ℝ) (U ε : ℝ)
    (huMeas : Measurable u) (hvMeas : Measurable v)
    (huBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ U)
    (hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ U)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Measurable (convexControl u v ε) ∧
      (∀ t : ℝ, 0 ≤ t →
        0 ≤ convexControl u v ε t ∧ convexControl u v ε t ≤ U) := by
  constructor
  · exact (measurable_const.mul huMeas).add
      (measurable_const.mul hvMeas)
  · intro t ht
    have hleft : 0 ≤ 1 - ε := sub_nonneg.mpr hε1
    constructor
    · exact add_nonneg
        (mul_nonneg hleft (huBound t ht).1)
        (mul_nonneg hε0 (hvBound t ht).1)
    · change (1 - ε) * u t + ε * v t ≤ U
      calc
        (1 - ε) * u t + ε * v t
            ≤ (1 - ε) * U + ε * U :=
          add_le_add
            (mul_le_mul_of_nonneg_left (huBound t ht).2 hleft)
            (mul_le_mul_of_nonneg_left (hvBound t ht).2 hε0)
        _ = U := by ring

theorem stationarity_convex_control
    (x : StateData) (r : ℝ) (v : ℝ → ℝ) (ε : ℝ) :
    stationarity x r (convexControl x.u v ε) =
      (fun t => ε * stationarity x r v t) := by
  funext t
  dsimp only [stationarity, convexControl]
  ring

theorem objective_convex_control_identity
    (x : StateData) (r : ℝ) (v : ℝ → ℝ) (ε : ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    objective x r (convexControl x.u v ε) - objective x r x.u =
      ε * (∫ t in Ioi (0 : ℝ), stationarity x r v t) +
      (∫ t in Ioi (0 : ℝ),
        comparisonIntegrand x (convexControl x.u v ε) t) -
      (∫ t in Ioi (0 : ℝ),
        gap x r (convexControl x.u v ε) t) := by
  have hadm := convex_control_admissible
    x.u v x.U ε x.huMeas hvMeas x.hu hvBound hε0 hε1
  have h := GSTStage117.objective_difference_identity
    x r (convexControl x.u v ε) hadm.1 hadm.2
  rw [stationarity_convex_control x r v ε,
      integral_const_mul] at h
  exact h

end GSTStage118

#print axioms GSTStage118.convex_control_admissible
#print axioms GSTStage118.stationarity_convex_control
#print axioms GSTStage118.objective_convex_control_identity
