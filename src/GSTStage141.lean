import GSTStage140

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage57

namespace GSTStage141

theorem positive_local_maximum_is_saturated
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hoTarget : x.omegaInitial < x.target)
    (hdiscount : x.eta * x.U ≤ x.rho)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t) (hS : 0 < S x t)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    x.u t = x.U := by
  have hu0 := GSTStage58.control_positive_at_local_maximum
    x r t ha hq ho hclip ht hlocal
  rcases lt_or_eq_of_le (x.hu t ht.le).2 with huU | huU
  · exact (GSTStage64.candidate_no_positive_local_maximum_interior
      x r t hr hi ha hq hoTarget hdiscount hclip
      ht hu0 huU hS hlocal).elim
  · exact huU

theorem candidate_positive_saturated_stationary_maximum
    (x : StateData) (r : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hthreshold :
      x.omegaInitial < x.rho * x.target / (x.rho + x.a))
    (hdiscount : x.eta * x.U ≤ x.rho)
    (hclip : GSTStage44.Clipping x r)
    (s : ℝ) (hs : 0 ≤ s) (hpositive : 0 < S x s) :
    ∃ t : ℝ, 0 < t ∧ 0 < S x t ∧
      sRate x t = 0 ∧ x.u t = x.U ∧
      (∀ᶠ v in 𝓝 t, S x v ≤ S x t) ∧
      (2 * x.q * x.c *
          resource x.u x.eta x.B x.phiInitial t * x.U =
        2 * x.a * x.q * x.target -
          x.a * (x.rho + x.a) * p x t) ∧
      (2 * r * x.U ≤
        resource x.u x.eta x.B x.phiInitial t * d x t) := by
  have hoTarget := GSTStage65.initial_lt_target_of_threshold
    x ha ho hthreshold
  obtain ⟨t, ht, hS, hstationary, _hu0, hlocal⟩ :=
    GSTStage58.candidate_positive_stationary_maximum
      x r hr hi ha hq ho hthreshold hclip s hs hpositive
  have hu := positive_local_maximum_is_saturated
    x r t hr hi ha hq ho hoTarget hdiscount hclip ht hS hlocal
  have hbalance := GSTStage57.stationary_balance x t hstationary
  rw [hu] at hbalance
  have hclipped := hclip t ht.le
  rw [hu] at hclipped
  have hsaturation := GSTStage59.clipping_saturation_lower_bound
    r x.U
    (resource x.u x.eta x.B x.phiInitial t * d x t)
    hr hU hclipped
  exact ⟨t, ht, hS, hstationary, hu, hlocal, hbalance, hsaturation⟩

end GSTStage141

#print axioms GSTStage141.positive_local_maximum_is_saturated
#print axioms GSTStage141.candidate_positive_saturated_stationary_maximum
