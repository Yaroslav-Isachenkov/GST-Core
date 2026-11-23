import GSTStage87

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11

namespace GSTStage88

noncomputable abbrev IntervalL2 (m : ℕ) :=
  Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) (m : ℝ)))

abbrev IntervalBC (m : ℕ) :=
  BoundedContinuousFunction (Icc (0 : ℝ) (m : ℝ)) ℝ

theorem joint_global_subsequence
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
        ContinuousOn Omega (Icc (0 : ℝ) (m : ℝ))) := by
  obtain ⟨a, haMeas, haBound, v, hrep, w, hwNorm, haEq,
      ψ, hψ, hweak⟩ :=
    GSTStage87.global_admissible_control_limit u x.U huMeas huBound
  obtain ⟨Phi, Omega, F, G, hFG, f, g, χ, hχ,
      hconv, hglue, hcont⟩ :=
    GSTStage76.trajectory_global_interval_limits x
      (fun n => u (ψ n))
      (fun n => huMeas (ψ n))
      (fun n t ht => huBound (ψ n) t ht)
  refine ⟨(fun n => ψ (χ n)), hψ.comp hχ,
    a, Phi, Omega, haMeas, haBound,
    (fun m n => v m (ψ (χ n))), w,
    ?_, hwNorm, haEq, ?_,
    (fun m n => F m (χ n)), (fun m n => G m (χ n)),
    f, g, ?_, hconv, hglue, hcont⟩
  · intro m n
    exact hrep m (ψ (χ n))
  · intro m h
    exact (hweak m h).comp hχ.tendsto_atTop
  · intro m n t
    exact hFG m (χ n) t

#print axioms GSTStage88.joint_global_subsequence

end GSTStage88
