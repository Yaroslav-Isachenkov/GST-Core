import GSTStage183

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage31 GSTStage37

namespace GSTStage184

theorem zero_source_continuous_clipped_control_not_ae_zero
    (x : StateData) (r : ℝ)
    (hB0 : x.B = 0) (hr : 0 < r)
    (hi : 0 < x.phiInitial) (ha : 0 < x.a)
    (hc : 0 < x.c) (hq : 0 < x.q)
    (htarget : 0 < x.target) (hU : 0 < x.U)
    (huCont : ContinuousOn x.u (Ici (0 : ℝ)))
    (hclip : GSTStage44.Clipping x r) :
    ¬ x.u =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  intro hzero
  have huZero : ∀ t : ℝ, 0 ≤ t → x.u t = 0 :=
    GSTStage130.halfline_continuous_eq_of_ae
      x.u (fun _ => 0) huCont continuousOn_const hzero
  have huInt : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable x.u volume 0 T := by
    intro T hT
    exact GSTStage27.bounded_control_integrable
      x.u x.U T hT x.huMeas x.hu
  have hlim : Tendsto (state x) atTop (𝓝 (0 : ℝ)) := by
    have h := GSTStage170.zero_source_omega_tendsto_zero
      x.u x.eta x.phiInitial x.a x.c x.omegaInitial
      x.heta ha x.hphiInitial x.hc x.homegaInitial
      huInt (fun t ht => (x.hu t ht).1)
    simpa only [state, hB0] using h
  have hbelow : ∀ᶠ t in atTop, state x t < x.target :=
    hlim.eventually (gt_mem_nhds htarget)
  obtain ⟨s, hstate, hs⟩ :=
    (hbelow.and (eventually_gt_atTop (0 : ℝ))).exists
  have hp : 0 < p x s :=
    GSTStage49.candidate_p_positive_of_state_lt_target
      x r s hr hi ha hq htarget hs hclip hstate
  have hz : z x s = 0 := by
    unfold z GSTStage23.zCostate
    have hint :
        (∫ t in Ioi s,
          GSTStage23.zKernel x.u x.eta x.rho s t * (x.u t * p x t)) = 0 := by
      calc
        _ = ∫ t in Ioi s, (0 : ℝ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          change GSTStage23.zKernel x.u x.eta x.rho s t *
            (x.u t * p x t) = 0
          rw [huZero t (hs.le.trans (le_of_lt ht)), zero_mul, mul_zero]
        _ = 0 := by simp
    rw [hint, mul_zero]
  have hd : 0 < d x s := by
    change 0 < x.c * p x s - x.eta * z x s
    rw [hz, mul_zero, sub_zero]
    exact mul_pos hc hp
  have hF : 0 < resource x.u x.eta x.B x.phiInitial s :=
    resource_positive x.u x.eta x.B x.phiInitial s x.hB hi hs.le
  have hinput :
      0 < resource x.u x.eta x.B x.phiInitial s * d x s / (2 * r) :=
    div_pos (mul_pos hF hd) (mul_pos (by norm_num) hr)
  have hmin :
      0 < min x.U
        (resource x.u x.eta x.B x.phiInitial s * d x s / (2 * r)) :=
    lt_min hU hinput
  have hmax :
      0 < max 0 (min x.U
        (resource x.u x.eta x.B x.phiInitial s * d x s / (2 * r))) :=
    lt_of_lt_of_le hmin (le_max_right _ _)
  have hcl := hclip s hs.le
  rw [huZero s hs.le] at hcl
  linarith only [hcl, hmax]

theorem zero_source_continuous_optimal_control_not_ae_zero
    (x : StateData) (r : ℝ)
    (hB0 : x.B = 0) (hr : 0 < r)
    (hi : 0 < x.phiInitial) (ha : 0 < x.a)
    (hc : 0 < x.c) (hq : 0 < x.q)
    (htarget : 0 < x.target) (hU : 0 < x.U)
    (huCont : ContinuousOn x.u (Ici (0 : ℝ)))
    (hoptimal : ∀ u : ℝ → ℝ, Measurable u →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ x.U) →
      objective x r u ≤ objective x r x.u) :
    ¬ x.u =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hclip : GSTStage44.Clipping x r :=
    GSTStage130.continuous_optimal_control_clipping x r hr huCont hoptimal
  exact zero_source_continuous_clipped_control_not_ae_zero
    x r hB0 hr hi ha hc hq htarget hU huCont hclip

end GSTStage184

#print axioms GSTStage184.zero_source_continuous_clipped_control_not_ae_zero
#print axioms GSTStage184.zero_source_continuous_optimal_control_not_ae_zero
