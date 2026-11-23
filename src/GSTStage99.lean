import GSTStage98

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11 GSTStage88

namespace GSTStage99

theorem joint_global_limit_integral_equations
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
          x.c * (∫ s in Icc (0 : ℝ) t, Phi s * a s)) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont,
      hproduct, hbalance, hpoint⟩ :=
    GSTStage97.joint_global_limit_resource_equation x u huMeas huBound

  have hOmegaCont (m n : ℕ) :
      ContinuousOn (competitorState x (u (κ n)))
        (Icc (0 : ℝ) (m : ℝ)) := by
    have hu : IntervalIntegrable (u (κ n)) volume 0 (m : ℝ) :=
      GSTStage27.bounded_control_integrable
        (u (κ n)) x.U (m : ℝ) (Nat.cast_nonneg m)
        (huMeas (κ n)) (huBound (κ n))
    have hs := GSTStage29.omega_solution
      (u (κ n)) x.eta x.B x.phiInitial x.a x.c x.omegaInitial
      (m : ℝ) hu
    have hc : ContinuousOn (competitorState x (u (κ n)))
        (uIcc (0 : ℝ) (m : ℝ)) := hs.1.continuousOn
    simpa only [uIcc_of_le (Nat.cast_nonneg m)] using hc

  have hintegral (t : ℝ) (_ht : 0 ≤ t) :
      Tendsto
        (fun n => ∫ s in Icc (0 : ℝ) t, competitorState x (u (κ n)) s)
        atTop (𝓝 (∫ s in Icc (0 : ℝ) t, Omega s)) := by
    obtain ⟨m, hm⟩ := exists_nat_gt t
    have hG : Tendsto (G m) atTop (𝓝 (g m)) := by
      simpa only [Function.comp_def] using
        (continuous_snd.tendsto (f m, g m)).comp (hconv m)
    exact GSTStage98.continuous_subinterval_integral_limit
      (m : ℝ) t (le_of_lt hm)
      (fun n => competitorState x (u (κ n))) Omega (G m) (g m)
      (hOmegaCont m) (hcont m).2
      (fun n s hs => (hFG m n ⟨s, hs⟩).2)
      (fun s hs => (hglue m s hs).2.symm)
      hG

  have hOmegaBalance : ∀ t : ℝ, 0 ≤ t →
      Omega t = x.omegaInitial -
        x.a * (∫ s in Icc (0 : ℝ) t, Omega s) +
        x.c * (∫ s in Icc (0 : ℝ) t, Phi s * a s) := by
    apply GSTStage98.competitor_limit_integral_balance
      x (fun n => u (κ n)) a Phi Omega
    · intro n T hT
      exact GSTStage27.bounded_control_integrable
        (u (κ n)) x.U T hT (huMeas (κ n)) (huBound (κ n))
    · intro t ht
      simpa only [Function.comp_def] using
        (continuous_snd.tendsto (Phi t, Omega t)).comp (hpoint t ht)
    · exact hintegral
    · exact hproduct

  exact ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
    v, w, hrep, hwNorm, haEq, hweak,
    F, G, f, g, hFG, hconv, hglue, hcont,
    hproduct, hbalance, hpoint, hintegral, hOmegaBalance⟩

end GSTStage99

#print axioms GSTStage99.joint_global_limit_integral_equations
