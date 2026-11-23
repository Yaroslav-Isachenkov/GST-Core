import GSTStage73

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11

namespace GSTStage74

theorem trajectory_subsequence_on_nat_intervals
    (x : StateData) (u : ℕ → ℝ → ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ x.U) :
    ∃ F G : ∀ m : ℕ,
        ℕ → BoundedContinuousFunction (Icc (0 : ℝ) (m : ℝ)) ℝ,
      (∀ m n t,
        F m n t = resource (u n) x.eta x.B x.phiInitial t ∧
        G m n t = competitorState x (u n) t) ∧
      ∃ f g : ∀ m : ℕ,
          BoundedContinuousFunction (Icc (0 : ℝ) (m : ℝ)) ℝ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ m, Tendsto (fun n => (F m (ψ n), G m (ψ n)))
            atTop (𝓝 (f m, g m)) := by
  classical
  choose Lphi Lomega hLphi hLomega hdiff using
    (fun m : ℕ =>
      GSTStage70.uniform_trajectory_lipschitz_estimates
        x (m : ℝ) (Nat.cast_nonneg m))
  choose R W _hR _hW hb using
    (fun m : ℕ =>
      GSTStage69.uniform_trajectory_bounds
        x (m : ℝ) (Nat.cast_nonneg m))
  let K : ℕ → NNReal := fun m => ⟨Lphi m, hLphi m⟩
  let H : ℕ → NNReal := fun m => ⟨Lomega m, hLomega m⟩
  have hphiLip : ∀ m n, LipschitzWith (K m)
      (fun t : Icc (0 : ℝ) (m : ℝ) =>
        resource (u n) x.eta x.B x.phiInitial t) := by
    intro m n
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have h := (hdiff m (u n) (huMeas n) (huBound n)
      t t.property s s.property).1
    simpa only [Real.dist_eq, Subtype.dist_eq] using h
  have homegaLip : ∀ m n, LipschitzWith (H m)
      (fun t : Icc (0 : ℝ) (m : ℝ) =>
        competitorState x (u n) t) := by
    intro m n
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have h := (hdiff m (u n) (huMeas n) (huBound n)
      t t.property s s.property).2
    simpa only [Real.dist_eq, Subtype.dist_eq] using h
  let F : ∀ m : ℕ,
      ℕ → BoundedContinuousFunction (Icc (0 : ℝ) (m : ℝ)) ℝ :=
    fun m n => BoundedContinuousFunction.mkOfCompact
      ⟨(fun t => resource (u n) x.eta x.B x.phiInitial t),
        (hphiLip m n).continuous⟩
  let G : ∀ m : ℕ,
      ℕ → BoundedContinuousFunction (Icc (0 : ℝ) (m : ℝ)) ℝ :=
    fun m n => BoundedContinuousFunction.mkOfCompact
      ⟨(fun t => competitorState x (u n) t),
        (homegaLip m n).continuous⟩
  have hFLip : ∀ m n, LipschitzWith (K m) (F m n) := hphiLip
  have hGLip : ∀ m n, LipschitzWith (H m) (G m n) := homegaLip
  have hFBound : ∀ m n t, F m n t ∈ Icc (0 : ℝ) (R m) := by
    intro m n t
    exact (hb m (u n) (huMeas n) (huBound n) t t.property).1
  have hGBound : ∀ m n t, G m n t ∈ Icc (0 : ℝ) (W m) := by
    intro m n t
    exact (hb m (u n) (huMeas n) (huBound n) t t.property).2
  obtain ⟨f, g, ψ, hψ, hlim⟩ :=
    GSTStage73.countable_paired_function_subsequence
      F G K H R W hFLip hGLip hFBound hGBound
  refine ⟨F, G, ?_, f, g, ψ, hψ, hlim⟩
  intro m n t
  exact ⟨rfl, rfl⟩

#print axioms GSTStage74.trajectory_subsequence_on_nat_intervals

end GSTStage74
