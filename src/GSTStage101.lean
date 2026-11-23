import GSTStage100

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11 GSTStage88

namespace GSTStage101

theorem halfline_admissible_control_integrable
    (a : ℝ → ℝ) (U T : ℝ)
    (hT : 0 ≤ T) (haMeas : Measurable a)
    (haBound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      0 ≤ a t ∧ a t ≤ U) :
    IntervalIntegrable a volume 0 T := by
  have hc : IntervalIntegrable (fun _ : ℝ => U) volume 0 T :=
    intervalIntegrable_const
  apply hc.mono_fun' haMeas.aestronglyMeasurable
  rw [uIoc_of_le hT]
  have hb : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) T),
      0 ≤ a t ∧ a t ≤ U :=
    haBound.filter_mono
      (ae_mono (Measure.restrict_mono
        (show Ioc (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ ht => ht.1)
        le_rfl))
  filter_upwards [hb] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2



theorem joint_global_limit_resource_identification
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
        Phi t = resource a x.eta x.B x.phiInitial t) := by
  obtain ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
      v, w, hrep, hwNorm, haEq, hweak,
      F, G, f, g, hFG, hconv, hglue, hcont,
      hproduct, hbalance, hpoint, hintegral, hOmegaBalance⟩ :=
    GSTStage99.joint_global_limit_integral_equations x u huMeas huBound

  have haInt (T : ℝ) (hT : 0 ≤ T) :
      IntervalIntegrable a volume 0 T :=
    halfline_admissible_control_integrable a x.U T hT haMeas haBound

  have hPhiEq (T : ℝ) (hT : 0 ≤ T) :
      Phi T = resource a x.eta x.B x.phiInitial T := by
    obtain ⟨m, hm⟩ := exists_nat_gt T
    have hPhi : ContinuousOn Phi (Icc (0 : ℝ) T) :=
      (hcont m).1.mono (Icc_subset_Icc le_rfl (le_of_lt hm))
    have he := GSTStage100.resource_eq_of_integral_balance
      a Phi x.eta x.B x.phiInitial T hT (haInt T hT) hPhi
      (fun t ht => hbalance t ht.1)
    exact he ⟨hT, le_rfl⟩

  exact ⟨κ, hκ, a, Phi, Omega, haMeas, haBound,
    v, w, hrep, hwNorm, haEq, hweak,
    F, G, f, g, hFG, hconv, hglue, hcont,
    hproduct, hbalance, hpoint, hintegral, hOmegaBalance,
    haInt, hPhiEq⟩

end GSTStage101

#print axioms GSTStage101.halfline_admissible_control_integrable
#print axioms GSTStage101.joint_global_limit_resource_identification
