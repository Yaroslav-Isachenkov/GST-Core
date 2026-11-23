import GSTStage75

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage34 GSTStage11

namespace GSTStage76

theorem glue_compatible_interval_functions
    (f : ∀ m : ℕ,
      BoundedContinuousFunction (Icc (0 : ℝ) (m : ℝ)) ℝ)
    (hcompat : ∀ (m k : ℕ) (t : ℝ)
      (hm : t ∈ Icc (0 : ℝ) (m : ℝ))
      (hk : t ∈ Icc (0 : ℝ) (k : ℝ)),
        f m ⟨t, hm⟩ = f k ⟨t, hk⟩) :
    ∃ Phi : ℝ → ℝ,
      (∀ (m : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (m : ℝ)),
        Phi t = f m ⟨t, ht⟩) ∧
      (∀ m : ℕ, ContinuousOn Phi (Icc (0 : ℝ) (m : ℝ))) := by
  classical
  have hex : ∀ t : ℝ, ∃ a : ℝ,
      ∀ (m : ℕ) (ht : t ∈ Icc (0 : ℝ) (m : ℝ)),
        a = f m ⟨t, ht⟩ := by
    intro t
    by_cases ht0 : 0 ≤ t
    · obtain ⟨k, hk⟩ := exists_nat_gt t
      have htk : t ∈ Icc (0 : ℝ) (k : ℝ) := ⟨ht0, hk.le⟩
      refine ⟨f k ⟨t, htk⟩, ?_⟩
      intro m htm
      exact hcompat k m t htk htm
    · refine ⟨0, ?_⟩
      intro m htm
      exact (ht0 htm.1).elim
  choose Phi hPhi using hex
  refine ⟨Phi, (fun m t ht => hPhi t m ht), ?_⟩
  intro m
  apply continuousOn_iff_continuous_restrict.mpr
  change Continuous (fun t : Icc (0 : ℝ) (m : ℝ) => Phi t)
  have heq :
      (fun t : Icc (0 : ℝ) (m : ℝ) => Phi t) =
      (fun t : Icc (0 : ℝ) (m : ℝ) => f m t) := by
    funext t
    exact hPhi t m t.property
  rw [heq]
  exact (f m).continuous

theorem trajectory_global_interval_limits
    (x : StateData) (u : ℕ → ℝ → ℝ)
    (huMeas : ∀ n, Measurable (u n))
    (huBound : ∀ n t, 0 ≤ t → 0 ≤ u n t ∧ u n t ≤ x.U) :
    ∃ Phi Omega : ℝ → ℝ,
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
            (∀ (m : ℕ) (t : ℝ)
              (ht : t ∈ Icc (0 : ℝ) (m : ℝ)),
                Phi t = f m ⟨t, ht⟩ ∧
                Omega t = g m ⟨t, ht⟩) ∧
            (∀ m : ℕ,
              ContinuousOn Phi (Icc (0 : ℝ) (m : ℝ)) ∧
              ContinuousOn Omega (Icc (0 : ℝ) (m : ℝ))) := by
  obtain ⟨F, G, hrep, f, g, ψ, hψ, hlim, hcompat⟩ :=
    GSTStage75.trajectory_compatible_interval_limits
      x u huMeas huBound
  obtain ⟨Phi, hPhi, hPhiCont⟩ :=
    glue_compatible_interval_functions f
      (fun m k t hm hk => (hcompat m k t hm hk).1)
  obtain ⟨Omega, hOmega, hOmegaCont⟩ :=
    glue_compatible_interval_functions g
      (fun m k t hm hk => (hcompat m k t hm hk).2)
  refine ⟨Phi, Omega, F, G, hrep, f, g, ψ, hψ, hlim, ?_, ?_⟩
  · intro m t ht
    exact ⟨hPhi m t ht, hOmega m t ht⟩
  · intro m
    exact ⟨hPhiCont m, hOmegaCont m⟩

#print axioms GSTStage76.glue_compatible_interval_functions
#print axioms GSTStage76.trajectory_global_interval_limits

end GSTStage76
