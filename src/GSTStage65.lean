import GSTStage64
open MeasureTheory Set Filter
open scoped Topology
open GSTStage31

namespace GSTStage65

theorem initial_lt_target_of_threshold
    (x : StateData)
    (ha : 0 < x.a)
    (ho : 0 < x.omegaInitial)
    (hthreshold :
      x.omegaInitial < x.rho * x.target / (x.rho + x.a)) :
    x.omegaInitial < x.target := by
  have hk : 0 < x.rho + x.a := add_pos x.hrho ha
  have hscaled := (lt_div_iff₀ hk).mp hthreshold
  have htarget : 0 < x.target := by
    by_contra hn
    have hnonpos : x.rho * x.target ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos x.hrho.le (le_of_not_gt hn)
    have hpositive := mul_pos ho hk
    linarith
  have hupper :
      x.rho * x.target / (x.rho + x.a) < x.target := by
    apply (div_lt_iff₀ hk).mpr
    nlinarith [mul_pos ha htarget]
  exact lt_trans hthreshold hupper

theorem candidate_no_positive_local_maximum
    (x : StateData) (r t : ℝ)
    (hr : 0 < r) (hU : 0 < x.U)
    (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (ho : 0 < x.omegaInitial)
    (hoTarget : x.omegaInitial < x.target)
    (hdiscount : x.eta * x.U ≤ x.rho)
    (hrThreshold :
      x.a * x.q * x.target ^ 2 /
        (4 * x.U ^ 2 * (x.rho + x.a)) < r)
    (hclip : GSTStage44.Clipping x r)
    (ht : 0 < t) (hS : 0 < S x t)
    (hlocal : ∀ᶠ s in 𝓝 t, S x s ≤ S x t) :
    False := by
  by_cases hu0 : x.u t = 0
  · exact GSTStage58.no_local_maximum_at_zero_control
      x r t ha hq ho hclip ht hu0 hlocal
  · by_cases huU : x.u t = x.U
    · exact GSTStage59.candidate_no_local_maximum_at_saturation
        x r t hr hU hi ha hq hrThreshold hclip ht huU hlocal
    · have hbound := x.hu t ht.le
      have huPositive : 0 < x.u t :=
        lt_of_le_of_ne hbound.1 (Ne.symm hu0)
      have huInterior : x.u t < x.U :=
        lt_of_le_of_ne hbound.2 huU
      exact GSTStage64.candidate_no_positive_local_maximum_interior
        x r t hr hi ha hq hoTarget hdiscount hclip
        ht huPositive huInterior hS hlocal

theorem candidate_S_nonpos
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
    ∀ t : ℝ, 0 ≤ t → S x t ≤ 0 := by
  have hoTarget := initial_lt_target_of_threshold x ha ho hthreshold
  intro s hs
  by_contra hn
  have hpositive : 0 < S x s := lt_of_not_ge hn
  obtain ⟨T, t, _hsT, ht, _htT, hpos, _hmax, hlocal⟩ :=
    GSTStage55.candidate_s_positive_interior_maximum
      x r hr hi ha hq ho hthreshold hclip s hs hpositive
  exact candidate_no_positive_local_maximum
    x r t hr hU hi ha hq ho hoTarget hdiscount hrThreshold
    hclip ht hpos hlocal

#print axioms initial_lt_target_of_threshold
#print axioms candidate_no_positive_local_maximum
#print axioms candidate_S_nonpos
end GSTStage65
