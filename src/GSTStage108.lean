import GSTStage107
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11 GSTStage88

namespace GSTStage108

theorem joint_global_limit_state_cost_convergence
    (x : StateData) (u : ℕ → ℝ → ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ x.U) :
    ∃ κ : ℕ → ℕ, StrictMono κ ∧
    ∃ a Phi Omega : ℝ → ℝ, Measurable a ∧
      (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        0 ≤ a t ∧ a t ≤ x.U) ∧
    ∃ v : ∀ m : ℕ, ℕ → IntervalL2 m,
    ∃ w : ∀ m : ℕ, IntervalL2 m,
      (∀ (m n : ℕ), (v m n : ℝ → ℝ) =ᵐ[
        volume.restrict (Icc (0 : ℝ) (m : ℝ))] u (κ n)) ∧
      (∀ (m : ℕ), ‖w m‖ ≤ GSTStage78.intervalL2Bound x.U (m : ℝ)) ∧
      (∀ (m : ℕ), a =ᵐ[volume.restrict (Icc (0 : ℝ) (m : ℝ))]
        (w m : ℝ → ℝ)) ∧
      (∀ m (h : IntervalL2 m),
        Tendsto (fun n => inner ℝ (v m n) h)
          atTop (𝓝 (inner ℝ (w m) h))) ∧
    ∃ F G : ∀ m : ℕ, ℕ → IntervalBC m,
    ∃ f g : ∀ m : ℕ, IntervalBC m,
      (∀ m n t,
        F m n t = resource (u (κ n)) x.eta x.B x.phiInitial t ∧
        G m n t = competitorState x (u (κ n)) t) ∧
      (∀ m, Tendsto (fun n => (F m n, G m n))
        atTop (𝓝 (f m, g m))) ∧
      (∀ (m : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (m : ℝ)),
        Phi t = f m ⟨t, ht⟩ ∧ Omega t = g m ⟨t, ht⟩) ∧
      (∀ m : ℕ,
        ContinuousOn Phi (Icc (0 : ℝ) (m : ℝ)) ∧
        ContinuousOn Omega (Icc (0 : ℝ) (m : ℝ))) ∧
      (∀ t : ℝ, 0 ≤ t →
        Tendsto
          (fun n => ∫ s in Icc (0 : ℝ) t,
            resource (u (κ n)) x.eta x.B x.phiInitial s * u (κ n) s)
          atTop (𝓝 (∫ s in Icc (0 : ℝ) t, Phi s * a s))) ∧
      (∀ t : ℝ, 0 ≤ t →
        Phi t = x.phiInitial + x.B * t -
          x.eta * ∫ s in Icc (0 : ℝ) t, Phi s * a s) ∧
      (∀ t : ℝ, 0 ≤ t →
        Tendsto
          (fun n =>
            (resource (u (κ n)) x.eta x.B x.phiInitial t,
             competitorState x (u (κ n)) t))
          atTop (𝓝 (Phi t, Omega t))) ∧
      (∀ t : ℝ, 0 ≤ t →
        Tendsto
          (fun n => ∫ s in Icc (0 : ℝ) t, competitorState x (u (κ n)) s)
          atTop (𝓝 (∫ s in Icc (0 : ℝ) t, Omega s))) ∧
      (∀ t : ℝ, 0 ≤ t →
        Omega t = x.omegaInitial -
          x.a * (∫ s in Icc (0 : ℝ) t, Omega s) +
          x.c * (∫ s in Icc (0 : ℝ) t, Phi s * a s)) ∧
      (∀ T : ℝ, 0 ≤ T → IntervalIntegrable a volume 0 T) ∧
      (∀ t : ℝ, 0 ≤ t →
        Phi t = resource a x.eta x.B x.phiInitial t) ∧
      (∀ t : ℝ, 0 ≤ t →
        Omega t = competitorState x a t) ∧
      (∀ T : ℝ, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        0 ≤ a t ∧ a t ≤ x.U) ∧
      (∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          (∫ t in Icc (0 : ℝ) (m : ℝ),
            Real.exp (-x.rho * t) * (a t) ^ 2) ≤
          (∫ t in Icc (0 : ℝ) (m : ℝ),
            Real.exp (-x.rho * t) * (u (κ n) t) ^ 2) + ε) ∧
      (∀ m : ℕ,
        Tendsto
          (fun n => ∫ t in Icc (0 : ℝ) (m : ℝ),
            Real.exp (-x.rho * t) *
              (competitorState x (u (κ n)) t - x.target) ^ 2)
          atTop (𝓝 (∫ t in Icc (0 : ℝ) (m : ℝ),
            Real.exp (-x.rho * t) * (Omega t - x.target) ^ 2))) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont,
      hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
      haInt, hPhiEq, hOmegaEq, haIntervals, hcontrol⟩ :=
    GSTStage107.joint_global_limit_discounted_control_lower
      x u huMeas huBound

  obtain ⟨M, hM, hgrowth⟩ := GSTStage67.uniform_state_growth x

  have hstateCost (m : ℕ) :
      Tendsto
        (fun n => ∫ t in Icc (0 : ℝ) (m : ℝ),
          Real.exp (-x.rho * t) *
            (competitorState x (u (κ n)) t - x.target) ^ 2)
        atTop (𝓝 (∫ t in Icc (0 : ℝ) (m : ℝ),
          Real.exp (-x.rho * t) * (Omega t - x.target) ^ 2)) := by
    let K : ℝ := M * (1 + (m : ℝ)) + |x.target|
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity

    have htraj (n : ℕ) :
        ContinuousOn (competitorState x (u (κ n)))
          (Icc (0 : ℝ) (m : ℝ)) := by
      have hu := GSTStage27.bounded_control_integrable
        (u (κ n)) x.U (m : ℝ) (Nat.cast_nonneg m)
        (huMeas (κ n)) (huBound (κ n))
      have hs := GSTStage29.omega_solution
        (u (κ n)) x.eta x.B x.phiInitial x.a x.c x.omegaInitial
        (m : ℝ) hu
      have hc : ContinuousOn (competitorState x (u (κ n)))
          (uIcc (0 : ℝ) (m : ℝ)) := hs.1.continuousOn
      simpa only [uIcc_of_le (Nat.cast_nonneg m)] using hc

    have heCont : Continuous (fun t : ℝ => Real.exp (-x.rho * t)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)

    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : ℝ => K ^ 2)
    · intro n
      have hc : ContinuousOn
          (fun t => Real.exp (-x.rho * t) *
            (competitorState x (u (κ n)) t - x.target) ^ 2)
          (Icc (0 : ℝ) (m : ℝ)) :=
        heCont.continuousOn.mul (((htraj n).sub continuousOn_const).pow 2)
      exact hc.aestronglyMeasurable measurableSet_Icc
    · exact integrable_const (K ^ 2)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have hb := hgrowth (u (κ n)) (huMeas (κ n)) (huBound (κ n)) t ht.1
      have hshift :
          |competitorState x (u (κ n)) t - x.target| ≤ K := by
        calc
          |competitorState x (u (κ n)) t - x.target| ≤
              |competitorState x (u (κ n)) t| + |x.target| :=
            abs_sub _ _
          _ ≤ M * (1 + t) + |x.target| := by
            linarith [hb]
          _ ≤ K := by
            dsimp only [K]
            nlinarith [mul_nonneg hM (sub_nonneg.mpr ht.2)]
      have hsquare :
          (competitorState x (u (κ n)) t - x.target) ^ 2 ≤ K ^ 2 := by
        have hh := mul_le_mul hshift hshift (abs_nonneg _) hK
        simpa only [← pow_two, sq_abs] using hh
      have hexp : Real.exp (-x.rho * t) ≤ 1 := by
        have hn : -x.rho * t ≤ 0 := by
          nlinarith [mul_nonneg x.hrho.le ht.1]
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hn
      have hnonneg : 0 ≤ Real.exp (-x.rho * t) *
          (competitorState x (u (κ n)) t - x.target) ^ 2 :=
        mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        Real.exp (-x.rho * t) *
            (competitorState x (u (κ n)) t - x.target) ^ 2 ≤
            1 * (competitorState x (u (κ n)) t - x.target) ^ 2 :=
          mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
        _ ≤ K ^ 2 := by simpa only [one_mul] using hsquare
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      have htend : Tendsto (fun n => competitorState x (u (κ n)) t)
          atTop (𝓝 (Omega t)) := by
        simpa only [Function.comp_def] using
          (continuous_snd.tendsto (Phi t, Omega t)).comp (hpoint t ht.1)
      have htarget : Tendsto (fun _ : ℕ => x.target)
          atTop (𝓝 x.target) := tendsto_const_nhds
      have hweight : Tendsto (fun _ : ℕ => Real.exp (-x.rho * t))
          atTop (𝓝 (Real.exp (-x.rho * t))) := tendsto_const_nhds
      exact hweight.mul ((htend.sub htarget).pow 2)

  exact ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
    v, w, hrep, hwNorm, haEq, hweak,
    F, G, f, g, hFG, hconv, hglue, hcont,
    hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
    haInt, hPhiEq, hOmegaEq, haIntervals, hcontrol, hstateCost⟩

end GSTStage108

#print axioms GSTStage108.joint_global_limit_state_cost_convergence
