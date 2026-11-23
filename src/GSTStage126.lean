import GSTStage125

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage37 GSTStage118

namespace GSTStage126

theorem optimal_control_variational_inequality
    (x : StateData) (r : ℝ)
    (hoptimal : ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r x.u)
    (v : ℝ → ℝ)
    (hvMeas : Measurable v)
    (hvBound : ∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U) :
    (∫ t in Ioi (0 : ℝ), stationarity x r v t) ≤ 0 := by
  have hlim := GSTStage125.objective_convex_right_derivative
    x r v hvMeas hvBound
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < 1 :=
    (show ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 from
      Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  apply le_of_tendsto hlim
  filter_upwards [hpositive, hsmall] with ε hε hε1
  have hadm := convex_control_admissible
    x.u v x.U ε x.huMeas hvMeas x.hu hvBound hε.le hε1.le
  have hvalue := hoptimal (convexControl x.u v ε) hadm.1 hadm.2
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hvalue) hε.le

end GSTStage126

#print axioms GSTStage126.optimal_control_variational_inequality
