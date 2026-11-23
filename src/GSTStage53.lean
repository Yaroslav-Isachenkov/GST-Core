import GSTStage52

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31

namespace GSTStage53

-- No clipping or sign assumption on S is used.
theorem s_strict_upper
    (x : StateData)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (t : ℝ) (ht : 0 ≤ t) :
    S x t < 2 * x.q *
      (state x t - x.rho * x.target / (x.rho + x.a)) := by
  have hk : 0 < x.rho + x.a := (toCostateData x).hdecay
  have hp := GSTStage45.p_strict_upper x hq ho t ht
  change
    x.a * p x t + 2 * x.q * (state x t - x.target) <
      2 * x.q *
        (state x t - x.rho * x.target / (x.rho + x.a))
  calc
    x.a * p x t + 2 * x.q * (state x t - x.target) <
        x.a * (2 * x.q * x.target / (x.rho + x.a)) +
          2 * x.q * (state x t - x.target) :=
      by
        have hmul := mul_lt_mul_of_pos_left hp ha
        linarith
    _ = 2 * x.q *
        (state x t - x.rho * x.target / (x.rho + x.a)) := by
      field_simp [ne_of_gt hk]; ring

theorem s_initial_negative
    (x : StateData)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hthreshold :
      x.omegaInitial < x.rho * x.target / (x.rho + x.a)) :
    S x 0 < 0 := by
  have hupper := s_strict_upper x ha hq ho 0 le_rfl
  rw [GSTStage50.state_initial] at hupper
  have hnegative :
      2 * x.q *
        (x.omegaInitial - x.rho * x.target / (x.rho + x.a)) < 0 :=
    mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) hq)
      (sub_neg.mpr hthreshold)
  exact lt_trans hupper hnegative

#print axioms s_strict_upper
#print axioms s_initial_negative

end GSTStage53
