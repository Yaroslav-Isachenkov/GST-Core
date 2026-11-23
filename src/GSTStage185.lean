import GSTStage184

open MeasureTheory Set Filter
open scoped Topology
open GSTStage31 GSTStage36 GSTStage37 GSTStage115 GSTStage180

namespace GSTStage185

def IsCoreOptimizer
    (k : CoreParameters) (n : ℝ) (hn : 0 ≤ n) (u : ℝ → ℝ) : Prop :=
  Measurable u ∧
  (∀ t : ℝ, 0 ≤ t → 0 ≤ u t ∧ u t ≤ k.U) ∧
  IntegrableOn (discountedCost (k.toStateData n hn) k.r u) (Ioi (0 : ℝ)) ∧
  (∀ v : ℝ → ℝ,
    AEMeasurable v (volume.restrict (Ioi (0 : ℝ))) →
    (∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ v t ∧ v t ≤ k.U) →
    objective (k.toStateData n hn) k.r v ≤
      objective (k.toStateData n hn) k.r u)

theorem exists_strictly_ordered_optimizers_positive_resource
    (k : CoreParameters) (n : ℝ) (hn : 0 < n)
    (hi : 0 < k.phiInitial) :
    ∃ u0 un : ℝ → ℝ,
      IsCoreOptimizer k 0 le_rfl u0 ∧
      IsCoreOptimizer k n hn.le un ∧
      Continuous u0 ∧ Continuous un ∧
      objective (k.toStateData 0 le_rfl) k.r u0 <
        objective (k.toStateData n hn.le) k.r un := by
  obtain ⟨y0, hparams0, hcont0, hint0, hopt0, hclip0⟩ :=
    GSTStage136.core_exists_continuous_optimal_self_clipping k 0 le_rfl
  obtain ⟨yn, hparamsN, hcontN, hintN, hoptN, _hclipN⟩ :=
    GSTStage136.core_exists_continuous_optimal_self_clipping k n hn.le
  rcases hparams0 with
    ⟨_heta, hB0, hphi, ha, hc, _homega, _hrho, hq, htarget, hU⟩
  simp only [CoreParameters.toStateData, mul_zero] at hB0 hphi ha hc hq htarget hU
  have hynU : yn.U = k.U :=
    hparamsN.2.2.2.2.2.2.2.2.2
  have hbound0 : ∀ t : ℝ, 0 ≤ t → 0 ≤ y0.u t ∧ y0.u t ≤ k.U := by
    simpa only [hU] using y0.hu
  have hboundN : ∀ t : ℝ, 0 ≤ t → 0 ≤ yn.u t ∧ yn.u t ≤ k.U := by
    simpa only [hynU] using yn.hu
  have hnonzero : ¬ y0.u =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    GSTStage184.zero_source_continuous_clipped_control_not_ae_zero
      y0 k.r hB0 k.hr
      (by simpa only [hphi] using hi)
      (by simpa only [ha] using k.ha)
      (by simpa only [hc] using k.hc)
      (by simpa only [hq] using k.hq)
      (by simpa only [htarget] using k.htarget)
      (by simpa only [hU] using k.hU)
      hcont0.continuousOn hclip0
  have hstrict := GSTStage183.source_lift_objective_strict
    k n hn y0.u hi y0.huMeas hbound0 hnonzero
  obtain ⟨hvMeas, hvBound, _htraj⟩ :=
    GSTStage181.source_lift_canonical_trajectories
      y0.u k.eta (k.b * n) k.phiInitial k.a k.c k.omegaInitial k.U
      hi (mul_nonneg k.hb.le hn.le) y0.huMeas hbound0
  have hvAE :
      ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
        0 ≤ liftedControl y0.u k.eta (k.b * n) k.phiInitial t ∧
        liftedControl y0.u k.eta (k.b * n) k.phiInitial t ≤ k.U := by
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun t ht => hvBound t (le_of_lt ht))
  have hupper :=
    (hoptN (liftedControl y0.u k.eta (k.b * n) k.phiInitial)
      hvMeas.aemeasurable hvAE).2
  refine ⟨y0.u, yn.u, ?_, ?_, hcont0, hcontN, lt_of_lt_of_le hstrict hupper⟩
  · exact ⟨y0.huMeas, hbound0, hint0,
      fun v hv hb => (hopt0 v hv hb).2⟩
  · exact ⟨yn.huMeas, hboundN, hintN,
      fun v hv hb => (hoptN v hv hb).2⟩

end GSTStage185

#print axioms GSTStage185.exists_strictly_ordered_optimizers_positive_resource
