import GSTStage71

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11

namespace GSTStage72

theorem trajectory_subsequence_on_interval
    (x : StateData) (T : ℝ) (hT : 0 ≤ T)
    (u : ℕ → ℝ → ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ x.U) :
    ∃ F G : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ,
      (∀ n t, F n t = resource (u n) x.eta x.B x.phiInitial t ∧
        G n t = competitorState x (u n) t) ∧
      ∃ f g : BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          Tendsto (fun n => (F (ψ n), G (ψ n)))
            atTop (𝓝 (f, g)) := by
  obtain ⟨Lphi, Lomega, hLphi, hLomega, hdiff⟩ :=
    GSTStage70.uniform_trajectory_lipschitz_estimates x T hT
  obtain ⟨R, W, _hR, _hW, hb⟩ :=
    GSTStage69.uniform_trajectory_bounds x T hT
  let K : NNReal := ⟨Lphi, hLphi⟩
  let H : NNReal := ⟨Lomega, hLomega⟩
  have hphiLip : ∀ n, LipschitzWith K
      (fun t : Icc (0 : ℝ) T =>
        resource (u n) x.eta x.B x.phiInitial t) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have h := (hdiff (u n) (huMeas n) (huBound n)
      t t.property s s.property).1
    simpa only [Real.dist_eq, Subtype.dist_eq] using h
  have homegaLip : ∀ n, LipschitzWith H
      (fun t : Icc (0 : ℝ) T => competitorState x (u n) t) := by
    intro n
    apply LipschitzWith.of_dist_le_mul
    intro s t
    have h := (hdiff (u n) (huMeas n) (huBound n)
      t t.property s s.property).2
    simpa only [Real.dist_eq, Subtype.dist_eq] using h
  let F : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ :=
    fun n => BoundedContinuousFunction.mkOfCompact
      ⟨(fun t => resource (u n) x.eta x.B x.phiInitial t),
        (hphiLip n).continuous⟩
  let G : ℕ → BoundedContinuousFunction (Icc (0 : ℝ) T) ℝ :=
    fun n => BoundedContinuousFunction.mkOfCompact
      ⟨(fun t => competitorState x (u n) t),
        (homegaLip n).continuous⟩
  have hFLip : ∀ n, LipschitzWith K (F n) := hphiLip
  have hGLip : ∀ n, LipschitzWith H (G n) := homegaLip
  have hFBound : ∀ n t, F n t ∈ Icc (0 : ℝ) R := by
    intro n t
    exact (hb (u n) (huMeas n) (huBound n) t t.property).1
  have hGBound : ∀ n t, G n t ∈ Icc (0 : ℝ) W := by
    intro n t
    exact (hb (u n) (huMeas n) (huBound n) t t.property).2
  obtain ⟨f, g, _hf, _hg, ψ, hψ, hlim⟩ :=
    GSTStage71.paired_subsequence_of_uniform_bounds
      F G K H R W hFLip hGLip hFBound hGBound
  refine ⟨F, G, ?_, f, g, ψ, hψ, hlim⟩
  intro n t
  exact ⟨rfl, rfl⟩

#print axioms GSTStage72.trajectory_subsequence_on_interval

end GSTStage72
