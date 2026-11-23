import GSTStage48

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31

namespace GSTStage49

-- A future upper bound on the state gives a lower bound on p.
-- Integrability follows from the already established state growth.
theorem p_lower_bound_of_future_state_bound
    (x : StateData) (s M : ℝ)
    (hq : 0 ≤ x.q) (hs : 0 ≤ s)
    (hfuture : ∀ t : ℝ, s ≤ t → state x t ≤ M) :
    2 * x.q * ((x.target - M) / (x.rho + x.a)) ≤ p x s := by
  have hk : 0 < x.rho + x.a := (toCostateData x).hdecay
  have hinput : IntegrableOn
      (fun t : ℝ =>
        Real.exp (-(x.rho + x.a) * (t - s)) *
          (x.target - state x t)) (Ioi s) :=
    (GSTStage22.p_integrable_and_bound
      (state x) x.rho x.a x.q x.target (growthConstant x) s
      hk (toCostateData x).hM hs
      (toCostateData x).hcont (toCostateData x).hOmega).1
  have hlower : IntegrableOn
      (fun t : ℝ =>
        Real.exp (-(x.rho + x.a) * (t - s)) *
          (x.target - M)) (Ioi s) :=
    (GSTStage45.exponential_tail_integrable
      (x.rho + x.a) s hk).mul_const (x.target - M)
  have hmono :
      (∫ t in Ioi s,
        Real.exp (-(x.rho + x.a) * (t - s)) * (x.target - M)) ≤
      ∫ t in Ioi s,
        Real.exp (-(x.rho + x.a) * (t - s)) *
          (x.target - state x t) := by
    apply integral_mono_ae hlower hinput
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hst : s < t := ht
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left (hfuture t hst.le) x.target)
      (Real.exp_pos _).le
  have heval :
      (∫ t in Ioi s,
        Real.exp (-(x.rho + x.a) * (t - s)) * (x.target - M)) =
      (x.target - M) / (x.rho + x.a) := by
    rw [integral_mul_const,
      GSTStage45.exponential_tail_integral (x.rho + x.a) s hk]
    ring
  rw [heval] at hmono
  change
    2 * x.q * ((x.target - M) / (x.rho + x.a)) ≤
      2 * x.q * ∫ t in Ioi s,
        Real.exp (-(x.rho + x.a) * (t - s)) *
          (x.target - state x t)
  exact mul_le_mul_of_nonneg_left hmono
    (mul_nonneg (by norm_num) hq)

-- The invariant rectangle contradicts the integral definition of p.
theorem candidate_rectangle_impossible
    (x : StateData) (r s M : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (hs : 0 < s) (hM : 0 < M) (hMtarget : M < x.target)
    (hclip : GSTStage44.Clipping x r)
    (hp : p x s ≤ 0) (ho : state x s ≤ M) :
    False := by
  have hinvariant :=
    GSTStage48.candidate_rectangle_invariant_forever
      x r s M hr hi ha hq hs hM hMtarget hclip hp ho
  have hlower := p_lower_bound_of_future_state_bound
    x s M hq.le hs.le (fun t ht => (hinvariant t ht).2)
  have hpositive :
      0 < 2 * x.q * ((x.target - M) / (x.rho + x.a)) :=
    mul_pos (mul_pos (by norm_num) hq)
      (div_pos (sub_pos.mpr hMtarget) (toCostateData x).hdecay)
  exact (not_lt_of_ge hp) (lt_of_lt_of_le hpositive hlower)

-- This does not yet cover state = target or the initial time s = 0.
theorem candidate_p_positive_of_state_lt_target
    (x : StateData) (r s : ℝ)
    (hr : 0 < r) (hi : 0 < x.phiInitial)
    (ha : 0 < x.a) (hq : 0 < x.q)
    (htarget : 0 < x.target) (hs : 0 < s)
    (hclip : GSTStage44.Clipping x r)
    (ho : state x s < x.target) :
    0 < p x s := by
  by_contra hnot
  have hp : p x s ≤ 0 := le_of_not_gt hnot
  let M : ℝ := (max 0 (state x s) + x.target) / 2
  have hmax : max 0 (state x s) < x.target :=
    max_lt_iff.mpr ⟨htarget, ho⟩
  have hzero : 0 ≤ max 0 (state x s) := le_max_left _ _
  have hstate : state x s ≤ max 0 (state x s) := le_max_right _ _
  have hM : 0 < M := by
    dsimp [M]
    linarith
  have hMtarget : M < x.target := by
    dsimp [M]
    linarith
  have hoM : state x s ≤ M := by
    dsimp [M]
    linarith
  exact candidate_rectangle_impossible
    x r s M hr hi ha hq hs hM hMtarget hclip hp hoM

#print axioms p_lower_bound_of_future_state_bound
#print axioms candidate_rectangle_impossible
#print axioms candidate_p_positive_of_state_lt_target

end GSTStage49
