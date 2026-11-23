import GSTStage186

open MeasureTheory Set Filter
open scoped Topology
open GSTStage11 GSTStage29 GSTStage31 GSTStage37

namespace GSTStage187

theorem p_positive_of_future_state_below_target
    (x : StateData) (s : ℝ) (hs : 0 ≤ s) (hq : 0 < x.q)
    (hbelow : ∀ t : ℝ, s < t → state x t < x.target) :
    0 < p x s := by
  obtain ⟨M, hM, hgrowth⟩ := state_linear_growth x
  have hdecay : 0 < x.rho + x.a :=
    lt_of_lt_of_le x.hrho (le_add_of_nonneg_right x.ha)
  have hint := (GSTStage22.p_integrable_and_bound
    (state x) x.rho x.a x.q x.target M s
    hdecay hM hs (state_continuousOn x) hgrowth).1
  let f : ℝ → ℝ := fun t =>
    Real.exp (-(x.rho + x.a) * (t - s)) * (x.target - state x t)
  have hpos : ∀ t ∈ Ioi s, 0 < f t := by
    intro t ht
    exact mul_pos (Real.exp_pos _) (sub_pos.mpr (hbelow t ht))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi s)] f :=
    ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => (hpos t ht).le)
  have hsupp : Ioi s ⊆ Function.support f := by
    intro t ht
    change f t ≠ 0
    exact (hpos t ht).ne'
  have hmass : 0 < volume.restrict (Ioi s) (Ioi s) := by
    simp [Real.volume_Ioi]
  have hintegral : 0 < ∫ t in Ioi s, f t :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg_ae
      hnonneg hint).mpr
      (lt_of_lt_of_le hmass (measure_mono hsupp))
  change 0 < 2 * x.q * ∫ t in Ioi s, f t
  exact mul_pos (mul_pos (by norm_num) hq) hintegral

theorem zero_control_not_optimal_of_positive_source
    (x : StateData) (r : ℝ)
    (hzero : x.u = fun _ => 0)
    (hB : 0 < x.B) (hr : 0 < r) (ha : 0 < x.a)
    (hc : 0 < x.c) (hq : 0 < x.q)
    (htarget : 0 < x.target) (hU : 0 < x.U) :
    ¬ (∀ v : ℝ → ℝ, Measurable v →
      (∀ t : ℝ, 0 ≤ t → 0 ≤ v t ∧ v t ≤ x.U) →
      objective x r v ≤ objective x r x.u) := by
  intro hoptimal
  have huCont : ContinuousOn x.u (Ici (0 : ℝ)) := by
    rw [hzero]
    exact continuousOn_const
  have hclip : GSTStage44.Clipping x r :=
    GSTStage130.continuous_optimal_control_clipping
      x r hr huCont hoptimal
  have hlim0 := GSTStage170.zero_source_omega_tendsto_zero
    (fun _ : ℝ => 0) x.eta x.phiInitial x.a x.c x.omegaInitial
    x.heta ha x.hphiInitial x.hc x.homegaInitial
    (fun _ _ => intervalIntegrable_const) (fun _ _ => le_rfl)
  have hstateEq :
      state x =
        omega (fun _ => 0) x.eta 0 x.phiInitial x.a x.c x.omegaInitial := by
    funext t
    simp only [state, hzero, GSTStage186.zero_control_omega]
  have hlim : Tendsto (state x) atTop (𝓝 (0 : ℝ)) := by
    rw [hstateEq]
    exact hlim0
  have hbelow : ∀ᶠ t in atTop, state x t < x.target :=
    hlim.eventually (gt_mem_nhds htarget)
  obtain ⟨T, hT⟩ := eventually_atTop.1 hbelow
  let s : ℝ := max T 0 + 1
  have hs : 0 < s := by
    dsimp [s]
    linarith only [le_max_right T (0 : ℝ)]
  have hTs : T ≤ s := by
    dsimp [s]
    linarith only [le_max_left T (0 : ℝ)]
  have hp : 0 < p x s :=
    p_positive_of_future_state_below_target x s hs.le hq
      (fun t ht => hT t (hTs.trans ht.le))
  have hz : z x s = 0 := by
    simp [z, GSTStage23.zCostate, hzero]
  have hd : 0 < d x s := by
    change 0 < x.c * p x s - x.eta * z x s
    rw [hz, mul_zero, sub_zero]
    exact mul_pos hc hp
  have hFformula :
      resource x.u x.eta x.B x.phiInitial s =
        x.phiInitial + x.B * s := by
    simp [resource, cumulative, hzero]
  have hF : 0 < resource x.u x.eta x.B x.phiInitial s := by
    rw [hFformula]
    exact add_pos_of_nonneg_of_pos x.hphiInitial (mul_pos hB hs)
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
  have hus : x.u s = 0 := by rw [hzero]
  rw [hus] at hcl
  linarith only [hcl, hmax]

end GSTStage187

#print axioms GSTStage187.p_positive_of_future_state_below_target
#print axioms GSTStage187.zero_control_not_optimal_of_positive_source
