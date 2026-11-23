import GSTStage111
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11 GSTStage88

namespace GSTStage112

theorem joint_global_limit_infinite_cost_lower
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
            GSTStage36.discountedCost x r (u (κ n)) t) + ε)

      ∧ (∀ r : ℝ,
        IntegrableOn (GSTStage36.discountedCost x r a)
          (Ioi (0 : ℝ)))
      ∧ (∀ r : ℝ, ∀ n : ℕ,
        IntegrableOn (GSTStage36.discountedCost x r (u (κ n)))
          (Ioi (0 : ℝ)))
      ∧ (∀ r : ℝ, 0 ≤ x.q → 0 ≤ r →
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ n in atTop,
            (∫ t in Ioi (0 : ℝ),
              GSTStage36.discountedCost x r a t) ≤
            (∫ t in Ioi (0 : ℝ),
              GSTStage36.discountedCost x r (u (κ n)) t) + ε) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont,
      hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
      haInt, hPhiEq, hOmegaEq, haIntervals, hcontrol, hstateCost, hcost⟩ :=
    GSTStage110.joint_global_limit_finite_cost_lower x u huMeas huBound

  have hlimInt (r : ℝ) :
      IntegrableOn (GSTStage36.discountedCost x r a)
        (Ioi (0 : ℝ)) :=
    GSTStage111.halfline_ae_cost_integrable x r a haMeas haBound

  have hseqBound (n : ℕ) :
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        0 ≤ u (κ n) t ∧ u (κ n) t ≤ x.U := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change (0 : ℝ) < t at ht
    exact huBound (κ n) t (le_of_lt ht)

  have hseqInt (r : ℝ) (n : ℕ) :
      IntegrableOn (GSTStage36.discountedCost x r (u (κ n)))
        (Ioi (0 : ℝ)) :=
    GSTStage111.halfline_ae_cost_integrable
      x r (u (κ n)) (huMeas (κ n)) (hseqBound n)

  have hfull (r : ℝ) (hq : 0 ≤ x.q) (hr : 0 ≤ r) :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          (∫ t in Ioi (0 : ℝ),
            GSTStage36.discountedCost x r a t) ≤
          (∫ t in Ioi (0 : ℝ),
            GSTStage36.discountedCost x r (u (κ n)) t) + ε := by
    apply GSTStage111.integral_lower_of_nat_intervals
      (fun n => GSTStage36.discountedCost x r (u (κ n)))
      (GSTStage36.discountedCost x r a)
      (hseqInt r) (hlimInt r)
    · intro n
      exact Filter.Eventually.of_forall
        (fun t => GSTStage111.discounted_cost_nonneg
          x r (u (κ n)) hq hr t)
    · exact hcost r hr

  exact ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
    v, w, hrep, hwNorm, haEq, hweak,
    F, G, f, g, hFG, hconv, hglue, hcont,
    hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
    haInt, hPhiEq, hOmegaEq, haIntervals, hcontrol, hstateCost, hcost,
    hlimInt, hseqInt, hfull⟩

end GSTStage112

#print axioms GSTStage112.joint_global_limit_infinite_cost_lower
