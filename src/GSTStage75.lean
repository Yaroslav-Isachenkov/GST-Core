import GSTStage74

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11

namespace GSTStage75

theorem paired_evaluation_tendsto
    {α : Type*} [TopologicalSpace α]
    (F G : ℕ → BoundedContinuousFunction α ℝ)
    (f g : BoundedContinuousFunction α ℝ)
    (hlim : Tendsto (fun n => (F n, G n)) atTop (𝓝 (f, g)))
    (t : α) :
    Tendsto (fun n => (F n t, G n t)) atTop (𝓝 (f t, g t)) := by
  have heval : Continuous
      (fun p : BoundedContinuousFunction α ℝ ×
        BoundedContinuousFunction α ℝ => (p.1 t, p.2 t)) :=
    ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.comp
      continuous_fst).prodMk
      ((BoundedContinuousFunction.lipschitz_eval_const t).continuous.comp
        continuous_snd)
  have hevalAt : Tendsto
      (fun p : BoundedContinuousFunction α ℝ ×
        BoundedContinuousFunction α ℝ => (p.1 t, p.2 t))
      (𝓝 (f, g)) (𝓝 (f t, g t)) :=
    heval.continuousAt
  exact hevalAt.comp hlim

theorem trajectory_compatible_interval_limits
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
          (∀ m, Tendsto (fun n => (F m (ψ n), G m (ψ n)))
            atTop (𝓝 (f m, g m))) ∧
          (∀ (m k : ℕ) (t : ℝ)
            (hm : t ∈ Icc (0 : ℝ) (m : ℝ))
            (hk : t ∈ Icc (0 : ℝ) (k : ℝ)),
              f m ⟨t, hm⟩ = f k ⟨t, hk⟩ ∧
              g m ⟨t, hm⟩ = g k ⟨t, hk⟩) := by
  obtain ⟨F, G, hrep, f, g, ψ, hψ, hlim⟩ :=
    GSTStage74.trajectory_subsequence_on_nat_intervals
      x u huMeas huBound
  have hpoint : ∀ (m : ℕ) (t : Icc (0 : ℝ) (m : ℝ)),
      Tendsto
        (fun n =>
          (resource (u (ψ n)) x.eta x.B x.phiInitial t,
            competitorState x (u (ψ n)) t))
        atTop (𝓝 (f m t, g m t)) := by
    intro m t
    have hv := paired_evaluation_tendsto
      (fun n => F m (ψ n)) (fun n => G m (ψ n))
      (f m) (g m) (hlim m) t
    apply hv.congr'
    exact Filter.Eventually.of_forall
      (fun n => Prod.ext (hrep m (ψ n) t).1 (hrep m (ψ n) t).2)
  refine ⟨F, G, hrep, f, g, ψ, hψ, hlim, ?_⟩
  intro m k t hm hk
  have heq := tendsto_nhds_unique
    (hpoint m ⟨t, hm⟩) (hpoint k ⟨t, hk⟩)
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

#print axioms GSTStage75.paired_evaluation_tendsto
#print axioms GSTStage75.trajectory_compatible_interval_limits

end GSTStage75
