import GSTStage106

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11 GSTStage88

namespace GSTStage107

theorem joint_global_limit_discounted_control_lower
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
            Real.exp (-x.rho * t) * (u (κ n) t) ^ 2) + ε) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont,
      hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
      haInt, hPhiEq, hOmegaEq⟩ :=
    GSTStage103.joint_global_limit_trajectory_identification
      x u huMeas huBound

  have haIntervals (T : ℝ) :
      ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
        0 ≤ a t ∧ a t ≤ x.U := by
    have hb := haBound
    rw [ae_restrict_iff' measurableSet_Ioi] at hb
    have hz : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
      simp [ae_iff, measure_singleton]
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hb, hz] with t ht hzero
    intro hmem
    have hpos : 0 < t := by
      by_contra hn
      have he : t = 0 := le_antisymm (le_of_not_gt hn) hmem.1
      exact hzero he
    exact ht hpos

  have hcontrol (m : ℕ) :
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop,
          (∫ t in Icc (0 : ℝ) (m : ℝ),
            Real.exp (-x.rho * t) * (a t) ^ 2) ≤
          (∫ t in Icc (0 : ℝ) (m : ℝ),
            Real.exp (-x.rho * t) * (u (κ n) t) ^ 2) + ε := by
    have huIntervals : ∀ n,
        ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (m : ℝ)),
          0 ≤ u (κ n) t ∧ u (κ n) t ≤ x.U := by
      intro n
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact huBound (κ n) t ht.1
    exact GSTStage106.discounted_interval_control_square_lower
      (m : ℝ) x.rho x.U x.hrho.le
      (fun n => u (κ n)) a (fun n => huMeas (κ n)) haMeas
      huIntervals (haIntervals (m : ℝ))
      (v m) (w m) (hrep m) (haEq m).symm (hweak m)

  exact ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
    v, w, hrep, hwNorm, haEq, hweak,
    F, G, f, g, hFG, hconv, hglue, hcont,
    hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
    haInt, hPhiEq, hOmegaEq, haIntervals, hcontrol⟩

end GSTStage107

#print axioms GSTStage107.joint_global_limit_discounted_control_lower
