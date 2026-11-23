import GSTStage92

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11 GSTStage88

namespace GSTStage93

theorem joint_global_subsequence_with_resource_product
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
      (∀ m : ℕ,
        Tendsto
          (fun n => ∫ t in Icc (0 : ℝ) (m : ℝ),
            resource (u (κ n)) x.eta x.B x.phiInitial t * u (κ n) t)
          atTop (𝓝 (∫ t in Icc (0 : ℝ) (m : ℝ), Phi t * a t))) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont⟩ :=
    GSTStage88.joint_global_subsequence x u huMeas huBound

  have hvNorm (m n : ℕ) :
      ‖v m n‖ ≤ GSTStage78.intervalL2Bound x.U (m : ℝ) := by
    have hb : ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
        0 ≤ u (κ n) t ∧ u (κ n) t ≤ x.U :=
      fun t ht => huBound (κ n) t ht.1
    let hp := GSTStage78.bounded_control_memLp
      (u (κ n)) x.U (m : ℝ) (huMeas (κ n)) hb
    have he : v m n = hp.toLp (u (κ n)) := by
      apply Lp.ext
      exact (hrep m n).trans hp.coeFn_toLp.symm
    rw [he]
    exact GSTStage78.bounded_control_L2_norm
      (u (κ n)) x.U (m : ℝ) (huMeas (κ n)) hb

  have hresource (m n : ℕ) :
      ContinuousOn
        (resource (u (κ n)) x.eta x.B x.phiInitial)
        (Icc (0 : ℝ) (m : ℝ)) := by
    have hi := GSTStage27.bounded_control_integrable
      (u (κ n)) x.U (m : ℝ) (Nat.cast_nonneg m)
      (huMeas (κ n)) (huBound (κ n))
    have hc := GSTStage11.resource_continuousOn
      (u (κ n)) x.eta x.B x.phiInitial (m : ℝ) hi
    rw [uIcc_of_le (Nat.cast_nonneg m)] at hc
    exact hc

  refine ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
    v, w, hrep, hwNorm, haEq, hweak,
    F, G, f, g, hFG, hconv, hglue, hcont, ?_⟩
  intro m
  exact GSTStage92.continuous_interval_product_limit
    (m : ℝ)
    (fun n => u (κ n))
    (fun n => resource (u (κ n)) x.eta x.B x.phiInitial)
    a Phi (v m) (w m) (F m) (f m)
    (GSTStage78.intervalL2Bound x.U (m : ℝ))
    (hrep m) (haEq m).symm (hvNorm m) (hweak m)
    (hresource m) (hcont m).1
    (fun n t ht => (hFG m n ⟨t, ht⟩).1)
    (fun t ht => (hglue m t ht).1.symm)
    (by
      simpa only [Function.comp_def] using
        (continuous_fst.tendsto (f m, g m)).comp (hconv m))

end GSTStage93

#print axioms GSTStage93.joint_global_subsequence_with_resource_product
