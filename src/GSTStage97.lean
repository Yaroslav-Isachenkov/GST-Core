import GSTStage96

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11 GSTStage88

namespace GSTStage97

theorem joint_global_limit_resource_equation
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
          atTop (𝓝 (Phi t, Omega t))) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont, hproduct⟩ :=
    GSTStage95.joint_global_subsequence_with_all_time_resource_product
      x u huMeas huBound

  have hpoint (t : ℝ) (ht : 0 ≤ t) :
      Tendsto
        (fun n =>
          (resource (u (κ n)) x.eta x.B x.phiInitial t,
           competitorState x (u (κ n)) t))
        atTop (𝓝 (Phi t, Omega t)) := by
    obtain ⟨m, hm⟩ := exists_nat_gt t
    have htI : t ∈ Icc (0 : ℝ) (m : ℝ) := ⟨ht, le_of_lt hm⟩
    have hv := GSTStage75.paired_evaluation_tendsto
      (F m) (G m) (f m) (g m) (hconv m) ⟨t, htI⟩
    have he (n : ℕ) :
        (F m n ⟨t, htI⟩, G m n ⟨t, htI⟩) =
        (resource (u (κ n)) x.eta x.B x.phiInitial t,
         competitorState x (u (κ n)) t) :=
      Prod.ext (hFG m n ⟨t, htI⟩).1 (hFG m n ⟨t, htI⟩).2
    have hv' := hv.congr' (Filter.Eventually.of_forall he)
    rw [← (hglue m t htI).1, ← (hglue m t htI).2] at hv'
    exact hv'

  have hbalance : ∀ t : ℝ, 0 ≤ t →
      Phi t = x.phiInitial + x.B * t -
        x.eta * ∫ s in Icc (0 : ℝ) t, Phi s * a s := by
    apply GSTStage96.resource_limit_integral_balance
      (fun n => u (κ n)) x.eta x.B x.phiInitial a Phi
    · intro n T hT
      exact GSTStage27.bounded_control_integrable
        (u (κ n)) x.U T hT (huMeas (κ n)) (huBound (κ n))
    · intro t ht
      simpa only [Function.comp_def] using
        (continuous_fst.tendsto (Phi t, Omega t)).comp (hpoint t ht)
    · exact hproduct

  exact ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
    v, w, hrep, hwNorm, haEq, hweak,
    F, G, f, g, hFG, hconv, hglue, hcont, hproduct,
    hbalance, hpoint⟩

end GSTStage97

#print axioms GSTStage97.joint_global_limit_resource_equation
