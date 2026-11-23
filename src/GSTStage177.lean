import GSTStage176

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29

namespace GSTStage177

theorem combined_state_resource_integral_balance
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial T : ℝ)
    (hu : IntervalIntegrable u volume 0 T) :
    eta * omega u eta B phiInitial a c omegaInitial T +
      c * resource u eta B phiInitial T =
    eta * omegaInitial + c * phiInitial + c * B * T -
      eta * a * (∫ t in (0 : ℝ)..T,
        omega u eta B phiInitial a c omegaInitial t) := by
  let O := omega u eta B phiInitial a c omegaInitial
  let F := resource u eta B phiInitial
  let H : ℝ → ℝ := fun t => eta * O t + c * F t
  have hs := omega_solution u eta B phiInitial a c omegaInitial T hu
  have hF := GSTStage12.resource_ac u eta B phiInitial T hu
  have hH : AbsolutelyContinuousOnInterval H 0 T :=
    (hs.1.const_mul eta).fun_add (hF.const_mul c)
  have hD : ∀ᵐ t : ℝ, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt H (-eta * a * O t + c * B) t := by
    filter_upwards [hs.2, GSTStage12.resource_ode_ae
      u eta B phiInitial T hu] with t hot hft
    intro ht
    have hd := ((hot ht).const_mul eta).add ((hft ht).const_mul c)
    convert hd using 1
    dsimp [H, O, F]
    ring
  have hOm : IntervalIntegrable O volume 0 T :=
    hs.1.continuousOn.intervalIntegrable
  have hFTC := GSTStage08.ac_integral_identity
    H (fun t => -eta * a * O t + c * B) 0 T hH hD
  rw [intervalIntegral.integral_add
    (hOm.const_mul (-eta * a)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul] at hFTC
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    H, O, F, omega_initial, resource_initial] at hFTC
  nlinarith only [hFTC]

theorem source_threshold_necessary_of_state_lower_bound
    (u : ℝ → ℝ)
    (eta B phiInitial a c omegaInitial h : ℝ)
    (heta : 0 < eta) (ha : 0 < a) (hc : 0 < c)
    (hB : 0 ≤ B) (hi : 0 ≤ phiInitial) (hh : 0 < h)
    (hu : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable u volume 0 T)
    (hkeep : ∀ t : ℝ, 0 ≤ t →
      h ≤ omega u eta B phiInitial a c omegaInitial t) :
    eta * a * h / c ≤ B := by
  by_contra hn
  have hbad : B * c < eta * a * h :=
    (lt_div_iff₀ hc).mp (lt_of_not_ge hn)
  let D := eta * a * h - c * B
  let C := eta * omegaInitial + c * phiInitial
  have hD : 0 < D := by
    dsimp [D]
    nlinarith only [hbad]
  let T := (max C 0 + 1) / D
  have hT : 0 < T := by
    apply div_pos _ hD
    have hm : 0 ≤ max C 0 := le_max_right C 0
    linarith
  have hTD : T * D = max C 0 + 1 := by
    dsimp [T]
    exact div_mul_cancel₀ _ (ne_of_gt hD)
  have hs := omega_solution u eta B phiInitial a c omegaInitial T (hu T hT.le)
  have hOm : IntervalIntegrable
      (omega u eta B phiInitial a c omegaInitial) volume 0 T :=
    hs.1.continuousOn.intervalIntegrable
  have hpoint : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      h ≤ omega u eta B phiInitial a c omegaInitial t := by
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall (fun t ht => hkeep t ht.1)
  have hIntegral :
      T * h ≤ ∫ t in (0 : ℝ)..T,
        omega u eta B phiInitial a c omegaInitial t := by
    have hm := intervalIntegral.integral_mono_ae_restrict
      hT.le (intervalIntegrable_const (c := h)) hOm hpoint
    simpa using hm
  have hscaled := mul_le_mul_of_nonneg_left hIntegral (mul_pos heta ha).le
  have hFnonneg := GSTStage30.resource_nonneg
    u eta B phiInitial T hB hi hT.le
  have hOnonneg : 0 ≤ omega u eta B phiInitial a c omegaInitial T :=
    hh.le.trans (hkeep T hT.le)
  have hEnd : 0 ≤
      eta * omega u eta B phiInitial a c omegaInitial T +
        c * resource u eta B phiInitial T :=
    add_nonneg (mul_nonneg heta.le hOnonneg) (mul_nonneg hc.le hFnonneg)
  have hbalance := combined_state_resource_integral_balance
    u eta B phiInitial a c omegaInitial T (hu T hT.le)
  have hbudget : T * D ≤ C := by
    dsimp [D, C]
    nlinarith only [hbalance, hEnd, hscaled]
  have hmax : C ≤ max C 0 := le_max_left C 0
  linarith only [hTD, hbudget, hmax]

end GSTStage177

#print axioms GSTStage177.combined_state_resource_integral_balance
#print axioms GSTStage177.source_threshold_necessary_of_state_lower_bound
