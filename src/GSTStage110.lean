import GSTStage109
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11 GSTStage88

namespace GSTStage110

theorem joint_global_limit_finite_cost_lower
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
            Real.exp (-x.rho * t) * (Omega t - x.target) ^ 2))) ∧
      (∀ r : ℝ, 0 ≤ r → ∀ m : ℕ, ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          (∫ t in Icc (0 : ℝ) (m : ℝ),
            GSTStage36.discountedCost x r a t) ≤
          (∫ t in Icc (0 : ℝ) (m : ℝ),
            GSTStage36.discountedCost x r (u (κ n)) t) + ε) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont,
      hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
      haInt, hPhiEq, hOmegaEq, haIntervals, hcontrol, hstateCost⟩ :=
    GSTStage108.joint_global_limit_state_cost_convergence
      x u huMeas huBound

  have hparts (m : ℕ) (b : ℝ → ℝ) (hbMeas : Measurable b)
      (hbBound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
        0 ≤ b t ∧ b t ≤ x.U) :
      IntegrableOn
        (fun t => Real.exp (-x.rho * t) *
          (competitorState x b t - x.target) ^ 2)
        (Icc (0 : ℝ) (m : ℝ)) ∧
      IntegrableOn
        (fun t => Real.exp (-x.rho * t) * (b t) ^ 2)
        (Icc (0 : ℝ) (m : ℝ)) := by
    have hbInt := GSTStage14.admissible_control_integrable
      b x.U (m : ℝ) (Nat.cast_nonneg m) hbMeas hbBound
    have hs := GSTStage29.omega_solution
      b x.eta x.B x.phiInitial x.a x.c x.omegaInitial (m : ℝ) hbInt
    have htraj : ContinuousOn (competitorState x b)
        (Icc (0 : ℝ) (m : ℝ)) := by
      have hc : ContinuousOn (competitorState x b)
          (uIcc (0 : ℝ) (m : ℝ)) := hs.1.continuousOn
      simpa only [uIcc_of_le (Nat.cast_nonneg m)] using hc
    have heCont : Continuous (fun t : ℝ => Real.exp (-x.rho * t)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hstateCont : ContinuousOn
        (fun t => Real.exp (-x.rho * t) *
          (competitorState x b t - x.target) ^ 2)
        (Icc (0 : ℝ) (m : ℝ)) :=
      heCont.continuousOn.mul ((htraj.sub continuousOn_const).pow 2)

    have hbNorm : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
        ‖b t‖ ≤ |x.U| := by
      filter_upwards [hbBound] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact ht.2.trans (le_abs_self x.U)
    have hp : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
        0 ≤ Real.exp (-x.rho * t) ∧ Real.exp (-x.rho * t) ≤ 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      refine ⟨(Real.exp_pos _).le, ?_⟩
      have hn : -x.rho * t ≤ 0 := by
        nlinarith [mul_nonneg x.hrho.le ht.1]
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hn
    have hcontrolInt := GSTStage106.bounded_weighted_product_integrable
      b b (fun t => Real.exp (-x.rho * t)) |x.U| (abs_nonneg x.U)
      hbMeas hbMeas heCont.measurable hbNorm hbNorm hp
    have he :
        (fun t => Real.exp (-x.rho * t) * b t * b t) =
        (fun t => Real.exp (-x.rho * t) * (b t) ^ 2) := by
      funext t
      ring
    rw [he] at hcontrolInt
    exact ⟨hstateCont.integrableOn_Icc, hcontrolInt⟩

  have hcost (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          (∫ t in Icc (0 : ℝ) (m : ℝ),
            GSTStage36.discountedCost x r a t) ≤
          (∫ t in Icc (0 : ℝ) (m : ℝ),
            GSTStage36.discountedCost x r (u (κ n)) t) + ε := by
    have huIntervals (n : ℕ) :
        ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
          0 ≤ u (κ n) t ∧ u (κ n) t ≤ x.U := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact huBound (κ n) t ht.1

    have hlimParts := hparts m a haMeas (haIntervals (m : ℝ))
    have hseqParts (n : ℕ) :=
      hparts m (u (κ n)) (huMeas (κ n)) (huIntervals n)

    have hstateEq :
        (∫ t in Icc (0 : ℝ) (m : ℝ),
          Real.exp (-x.rho * t) * (Omega t - x.target) ^ 2) =
        (∫ t in Icc (0 : ℝ) (m : ℝ),
          Real.exp (-x.rho * t) *
            (competitorState x a t - x.target) ^ 2) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      rw [hOmegaEq t ht.1]
    have hstate := hstateCost m
    rw [hstateEq] at hstate

    have hsum := GSTStage109.weighted_sum_eventually_lower
      (fun n => ∫ t in Icc (0 : ℝ) (m : ℝ),
        Real.exp (-x.rho * t) *
          (competitorState x (u (κ n)) t - x.target) ^ 2)
      (fun n => ∫ t in Icc (0 : ℝ) (m : ℝ),
        Real.exp (-x.rho * t) * (u (κ n) t) ^ 2)
      (∫ t in Icc (0 : ℝ) (m : ℝ),
        Real.exp (-x.rho * t) * (competitorState x a t - x.target) ^ 2)
      (∫ t in Icc (0 : ℝ) (m : ℝ),
        Real.exp (-x.rho * t) * (a t) ^ 2)
      x.q r hr hstate (hcontrol m)

    have hlimSplit := GSTStage109.discounted_cost_integral_split
      x r a (m : ℝ) hlimParts.1 hlimParts.2
    have hseqSplit (n : ℕ) := GSTStage109.discounted_cost_integral_split
      x r (u (κ n)) (m : ℝ) (hseqParts n).1 (hseqParts n).2
    intro ε hε
    filter_upwards [hsum ε hε] with n hn
    rw [hlimSplit, hseqSplit n]
    exact hn

  exact ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
    v, w, hrep, hwNorm, haEq, hweak,
    F, G, f, g, hFG, hconv, hglue, hcont,
    hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
    haInt, hPhiEq, hOmegaEq, haIntervals, hcontrol, hstateCost, hcost⟩

end GSTStage110

#print axioms GSTStage110.joint_global_limit_finite_cost_lower
